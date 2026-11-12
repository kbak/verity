"""Bind gas observations to a live original-bytecode execution.

The pinned local EVM is the trusted meter for ordinary instruction spans. This
adapter does not claim to prove EVM execution or to derive costs from Solidity.
The Lean checker independently computes GAS and raw CALL boundary accounting.
"""
from .engine import HarnessError


def source_sites(ast):
    sites = set()
    def walk(node):
        if isinstance(node, list):
            for child in node:
                walk(child)
        elif isinstance(node, dict):
            expr = node.get('expression', {})
            high = (node.get('nodeType') == 'FunctionCall' and
                    expr.get('nodeType') == 'Identifier' and expr.get('name') == 'gasleft' and
                    expr.get('referencedDeclaration', 0) < 0)
            low = (node.get('nodeType') == 'YulFunctionCall' and
                   node.get('functionName', {}).get('name') == 'gas')
            if high or low:
                sites.add(node['src'])
            for child in node.values():
                walk(child)
    walk(ast)
    return sites


def source_map(runtime, mapping):
    """Expand solc's compressed map at instruction boundaries, skipping PUSH data."""
    code = bytes.fromhex(runtime.removeprefix('0x'))
    entries, previous, pc = {}, ['0', '0', '-1', '', ''], 0
    for row in mapping.split(';'):
        if pc >= len(code):
            raise HarnessError('source map extends beyond runtime')
        for i, field in enumerate(row.split(':')):
            if field:
                previous[i] = field
        entries[pc] = ':'.join(previous[:3])
        opcode = code[pc]
        pc += 1 + (opcode - 0x5f if 0x60 <= opcode <= 0x7f else 0)
    return code, entries


def evidence(trace, call, prestate, runtime, mapping, sites, *, coinbase):
    """Record one original root frame, including its full ordinary-cost spans.

    The caller validates the runtime and configured child programs against the
    deployed accounts, and supplies the block coinbase (EIP-3651 warmth).
    Transactions with access lists require an additional adapter. No result, gas budget, or missing trace receives a default.
    Child calls here must not access further accounts; those require a complete
    journaled access-list adapter rather than guessing account warmth.
    """
    logs = trace['structLogs']
    root = [step for step in logs if step['depth'] == 1]
    if not root or root[0]['pc'] != 0:
        raise HarnessError('source gas requires a complete root-frame trace')
    if root[-1]['op'] not in ('RETURN', 'REVERT', 'STOP', 'INVALID'):
        raise HarnessError('source frame OOG/unknown halt requires a separate exceptional adapter')
    for step in logs:
        if step['depth'] > 1 and step['op'] in (
                'CALL', 'DELEGATECALL', 'STATICCALL', 'CALLCODE', 'CREATE', 'CREATE2',
                'BALANCE', 'EXTCODESIZE', 'EXTCODECOPY', 'EXTCODEHASH', 'SELFDESTRUCT'):
            raise HarnessError('nested account accesses require a journaled warmth adapter')
    code, positions = source_map(runtime, mapping)
    remaining = root[0]['gas']
    if int(call['gas'], 16) != remaining:
        raise HarnessError('root opcode and call traces disagree on initial gas')
    previous, events, accounting = remaining, [], []
    children = iter(call.get('calls', []))
    warm = {int(call['from'], 16), int(call['to'], 16), coinbase, *range(1, 18), 256}
    balances = {int(a, 16): int(state.get('balance', '0x0'), 16)
                for a, state in prestate.items()}
    caller = int(call['to'], 16)
    for position, step in enumerate(root):
        pc, op = step['pc'], step['op']
        if not (0 <= pc < len(code)) or pc not in positions:
            raise HarnessError('source PC is not an instruction in pinned runtime')
        stack = [int(v, 16) for v in step['stack']]
        if op in ('BALANCE', 'EXTCODESIZE', 'EXTCODECOPY', 'EXTCODEHASH'):
            warm.add(stack[-1] % (1 << 160))
        if op == 'GAS' and positions[pc] in sites:
            if code[pc] != 0x5a or step['gasCost'] != 2:
                raise HarnessError('source GAS opcode or its own charge differs')
            cost = previous - step['gas']
            if cost < 0:
                raise HarnessError('source gas increased between observations')
            events.append({'type': 'read', 'site': positions[pc], 'cost': cost})
            previous = step['gas'] - 2
            accounting.append({'kind': 'read', 'remaining': previous})
        elif op in ('CALL', 'DELEGATECALL'):
            if code[pc] != (0xf1 if op == 'CALL' else 0xf4):
                raise HarnessError('source call opcode differs from pinned runtime')
            try:
                child = next(children)
            except StopIteration as exc:
                raise HarnessError('missing original child call trace') from exc
            delegated = op == 'DELEGATECALL'
            requested, target = stack[-1], stack[-2] % (1 << 160)
            amount = int(call.get('value', '0x0'), 16) if delegated else stack[-3]
            start = 3 if delegated else 4
            offset, size, out_offset, out_size = (stack[-i] for i in range(start, start + 4))
            memory = bytes.fromhex(''.join(step['memory']))
            payload = memory[offset:offset + size].ljust(size, b'\0') if size else b''
            if (child['type'] != op or int(child['to'], 16) != target or
                    bytes.fromhex(child.get('input', '0x')[2:]) != payload):
                raise HarnessError('opcode operands and child call trace disagree')
            account = prestate.get('0x' + target.to_bytes(20, 'big').hex(), {})
            dead = (not account.get('code', '0x')[2:] and
                    int(account.get('nonce', 0)) == 0 and balances.get(target, 0) == 0)
            if account.get('code', '').startswith('0xef0100'):
                raise HarnessError('delegated code needs explicit EIP-7702 access-list evidence')
            allowance = int(child['gas'], 16)
            left = allowance - int(child['gasUsed'], 16)
            if left < 0:
                raise HarnessError('child consumed more gas than its allowance')
            exceptional = ('error' in child and child['error'] not in
                           ('execution reverted', 'insufficient balance for transfer'))
            cost = previous - step['gas']
            if cost < 0:
                raise HarnessError('source gas increased before call')
            event = {'type': 'call', 'cost': cost,
                     'kind': 'delegatecall' if delegated else 'call', 'caller': caller,
                     'target': target, 'value': amount, 'gas': requested,
                     'calldata': list(payload), 'allowance': allowance,
                     'exceptional': exceptional, 'gasLeft': left,
                     'success': 'error' not in child,
                     'returndata': list(bytes.fromhex(child.get('output', '0x')[2:])),
                     'context': {'memoryWords': len(memory) // 32,
                                 'inputOffset': offset, 'inputSize': size,
                                 'outputOffset': out_offset, 'outputSize': out_size,
                                 'targetWarm': target in warm, 'targetDead': dead,
                                 'transfersValue': not delegated and amount != 0,
                                 'delegationWarm': None}}
            events.append(event)
            # Read the actual resumed parent gas independently of the Lean formula.
            if position + 1 == len(root):
                raise HarnessError('missing parent continuation after call')
            previous = root[position + 1]['gas']
            accounting.append({'kind': 'call', 'allowance': allowance, 'remaining': previous})
            warm.add(target)
            if not delegated and 'error' not in child and amount:
                balances[caller] = balances.get(caller, 0) - amount
                balances[target] = balances.get(target, 0) + amount
    if next(children, None) is not None:
        raise HarnessError('unmatched original child trace')
    final = root[-1]
    left = 0 if final['op'] == 'INVALID' else final['gas'] - final['gasCost']
    cost = previous - left
    if cost < 0:
        raise HarnessError('source gas increased before frame exit')
    events.append({'type': 'end', 'cost': cost})
    accounting.append({'kind': 'end', 'remaining': left})
    return {'remaining': remaining, 'events': events}, left, accounting
