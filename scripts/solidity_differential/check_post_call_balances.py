"""Post-callback ledger reads, payment checks and whole-frame rollback.

A separately compiled payer updates a separately compiled ledger. Lean executes
an independent finite child program, never EVM-derived response rows. Gas is
assumed adequate; this campaign makes no generated-code gas equivalence claim.
"""
import argparse
import json
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .anvil import Anvil, SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .check_interface_word_static_call import address, SENDER
from .check_deployed_immutables import capture, declarations
from .stateful import replay_three_routes
from .identity import ImplementationIdentity

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyPostCallBalance.sol')
ORACLE = FIXTURE.with_name('PostCallBalanceOracle.sol')
FUNCTIONS = ['ledger()', 'callback()', 'sequence()', 'observe()',
             'settle(uint256,uint256,uint256,bytes)', 'settleTwice(uint256,uint256,uint256,bytes)']
MASK = (1 << 256) - 1


def word(n):
    return '0x' + n.to_bytes(32, 'big').hex()


def error(reason):
    return '0x' + (keccak(text='Error(string)')[:4] + encode(['string'], [reason])).hex()


def transactions(root, ledger, payer, methods):
    """Independent expected state, exact failures and ordered logs after every call."""
    slot = word(int.from_bytes(keccak(encode(['address', 'uint256'], [root, 0])), 'big'))
    balance, mode, count, sequence = 100, 0, 0, 0
    txs, expected = [], {}
    def log(account, data, signature=None):
        return {'address': account, 'topics': [] if signature is None else
                ['0x' + keccak(text=signature).hex()], 'data': data}
    def add(signature, args, status, data, events):
        ident = str(len(txs))
        types = signature[signature.index('(')+1:-1].split(',') if args else []
        payload = encode(types, args)
        txs.append({'id': ident, 'function': signature.split('(')[0],
            'args': [int.from_bytes(payload[i:i+32], 'big') for i in range(0,len(payload),32)],
            'sender': SENDER, 'target': root, 'value': '0x0',
            'data': '0x' + methods[signature] + encode(types, args).hex(),
            'timestamp': 1000000100 + len(txs), 'blockNumber': 4 + len(txs)})
        expected[ident] = {'status': status, 'data': data, 'events': events,
            'storage': [[root, word(0), word(sequence)], [ledger, slot, word(balance)],
                        [ledger, word(1), word(mode)], [payer, word(0), word(count)]]}
    for signature, value in [('ledger()', int(ledger, 16)), ('callback()', int(payer, 16)),
                             ('sequence()', sequence), ('observe()', balance)]:
        add(signature, [], 'ok', word(value), [])
    cases = [(10, 10, 0, 0), (3, 9, 0, 1), (9, 8, 0, 31), (0, 0, 0, 32),
             (1, 1, 4, 33), (MASK, 0, 0, 65), (1, MASK, 0, 128)]
    cases += [(1, 2, m, 33) for m in [1, 2, 3, 5, 6, 7, 8]]
    cases += [(i, i+1, 0, size) for i, size in enumerate([0, 1, 31, 32, 33, 65, 128])]
    for due, paid, selected, size in cases:
        payload = bytes((i * 17 + 3) % 256 for i in range(size))
        after = (balance + paid) & MASK
        failure = '0x005200' if selected == 7 else '0x' if selected in [1,2,3,5,6,8] else (
            error('overflow') if balance + due > MASK else
            error('payment') if balance + due > after else None)
        events = []
        if failure is None:
            balance, mode, count, sequence = after, selected, count + 1, sequence + 1
            events = [log(root, word(sequence), 'Starting(uint256)'), log(ledger, word(paid)),
                      log(payer, word(selected)),
                      log(root, '0x'+encode(['uint256','uint256'],[sequence,balance]).hex(),
                          'Received(uint256,uint256)')]
        add(FUNCTIONS[4], [due,paid,selected,payload], 'revert' if failure else 'ok',
            failure if failure else word(balance), events)
        add('observe()', [], 'ok', word(balance), [])
        add('sequence()', [], 'ok', word(sequence), [])
    for due, first, second in [(9,4,5), (10,4,5), (0,0,0), (1,MASK,1)]:
        middle, after = (balance + first) & MASK, (balance + first + second) & MASK
        failure = error('overflow') if balance + first > MASK else (
            error('first') if balance + first > middle else
            error('overflow') if balance + due > MASK else
            error('payment') if balance + due > after else None)
        events = []
        if failure is None:
            balance, mode, count = after, 0, count+2
            events = [log(ledger,word(first)), log(payer,word(0)),
                      log(ledger,word(second)), log(payer,word(0))]
        add(FUNCTIONS[5], [due,first,second,b'\x00\x41\x00'], 'revert' if failure else 'ok',
            failure if failure else word(balance), events)
        add('observe()', [], 'ok', word(balance), [])
    initial = [(root,word(0),word(0)), (ledger,slot,word(100)),
               (ledger,word(1),word(0)), (payer,word(0),word(0))]
    return txs, expected, initial


def campaign(out, optimized=False, mutation=None):
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = FIXTURE.read_text()
    if mutation == 'stale':
        source = source.replace('uint256 afterAmount = query();',
                                'uint256 afterAmount = beforeAmount;', 1)
    elif mutation == 'unchecked':
        source = source.replace('require(beforeAmount.add(due) <= afterAmount, "payment");',
                                'require(true, "payment");', 1)
    (out / FIXTURE.name).write_text(source)
    settings = {'evmVersion':'istanbul', 'optimizer':{'enabled':optimized,'runs':200},
                'metadata':{'bytecodeHash':'none'}}
    source_result = solc_compile({'language':'Solidity','sources':{FIXTURE.name:{'content':source}},
        'settings':{**settings,'outputSelection':{'*':{'':['ast'],'*':['evm.bytecode.object',
            'evm.deployedBytecode','evm.methodIdentifiers']}}}},out,out/'solc',
        solc=Path.cwd()/'.lake/solidity-import/solc-0.7.6')
    compiled = source_result['contracts'][FIXTURE.name][FIXTURE.stem]['evm']
    ast = source_result['sources'][FIXTURE.name]['ast']
    bases = next(n['linearizedBaseContracts'] for n in ast['nodes'] if n.get('name') == FIXTURE.stem)
    decls = [d | {'source':FIXTURE.name} for d in declarations(ast,bases)]
    root, ledger, payer = address(0), address(1), address(2)
    creation = '0x'+compiled['bytecode']['object']+encode(['address','address'],[ledger,payer]).hex()
    with Anvil(out/'capture') as node:
        manifest = capture(node,creation,decls,compiled['deployedBytecode']['immutableReferences'])
    if manifest['codeAddress'] != root:
        raise HarnessError('unexpected root deployment address')
    write_json(out/'deployment.json',manifest)
    template = Path('Contracts/SolidityImportSmoke/LegacyStaticWordModel.lean').read_text()
    template = template.replace('import Contracts.SolidityImportSmoke.StaticGasMocks',
        'import Contracts.SolidityImportSmoke.PostCallBalanceMocks\n'
        'import Compiler.SolidityImport.PostCallStaticFrames')
    start, end = template.index('solidity_import imported'), template.index('end SolidityImportSmoke')
    template = template[:start] + (
        f'solidity_import imported from {json.dumps(str(out))} entry "{FIXTURE.name}"\n'
        '  using {\n    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,\n'
        f'    optimizerRuns := {"some 200" if optimized else "none"}, bytecodeHash := "none",\n'
        '    deployedImmutables := some "deployment.json" }\n'
        f'  contract {FIXTURE.stem}\n' + ''.join(f'  function {f}\n' for f in FUNCTIONS)) + template[end:]
    template = template[:template.index('        (configure :=')] + (
        '        (configure := Contracts.SolidityImportSmoke.PostCallBalanceMocks.configure)\n')
    driver = out/'Driver.lean'
    driver.write_text(template)
    write_json(out/'selectors.json',[int(compiled['methodIdentifiers'][f],16) for f in FUNCTIONS])
    command(['lake','env','lean','--run',driver,'compile',out/'selectors.json',out/'model.yul'],
            log=out/'compile.log',timeout=900)
    model = solc_compile({'language':'Yul','sources':{'Model.yul':{'content':(out/'model.yul').read_text()}},
        'settings':{'evmVersion':'osaka','optimizer':{'enabled':True,'runs':466},
            'outputSelection':{'*':{'*':['evm.bytecode.object']}}}},out,out/'model-solc',solc=SOLC)
    model_code = next(iter(model['contracts']['Model.yul'].values()))['evm']['bytecode']['object']
    children = solc_compile({'language':'Solidity','sources':{ORACLE.name:{'content':ORACLE.read_text()}},
        'settings':{'evmVersion':'osaka','optimizer':{'enabled':True,'runs':466},
            'outputSelection':{'*':{'*':['evm.bytecode.object','evm.deployedBytecode.object',
                                       'evm.methodIdentifiers']}}}},out,out/'children-solc',solc=SOLC)
    children = [children['contracts'][ORACLE.name][name]['evm']
                for name in ['PostCallBalanceLedger','PostCallBalancePayer']]
    codes = ['0x'+c['bytecode']['object'] for c in children]
    environment = {'program':'post-call-balances-v1','accounts':[str(int(ledger,16)),str(int(payer,16))],
        'emptyAccounts':[], 'gas':'1000000',
        'readSelector':int(children[0]['methodIdentifiers']['read(address)'],16),
        'paySelector':int(children[1]['methodIdentifiers']['settle(address,uint256,uint256,bytes)'],16)}
    txs, expected, initial = transactions(root,ledger,payer,compiled['methodIdentifiers'])
    write_json(out/'transactions.json',txs)
    write_json(out/'expected.json',expected)
    adapters = {'source':EVM(out/'A',[creation]+codes,initial),
        'model':Denote(out/'B',driver,root,initial,byte_call_environment=environment,
            identity=ImplementationIdentity(driver,[out/'deployment.json',out/FIXTURE.name]),
            account_code=[(a,'0x'+c['deployedBytecode']['object'])
                          for a,c in zip([ledger,payer],children,strict=True)]),
        'compiled':EVM(out/'C',['0x'+model_code]+codes,initial)}
    # Observe all asserted cells even before their first dynamic access.
    # Discovery alone would omit untouched initial state in getter transactions.
    cells = {(a, s) for a, s, _ in initial}
    def observe_all(adapter):
        return lambda txs, plans: adapter(txs,
            [[list(key) for key in sorted(cells | {tuple(k) for k in plan})] for plan in plans])
    result = replay_three_routes(txs,{name:observe_all(adapter) for name,adapter in adapters.items()})
    mismatches = []
    for route, rows in result['observations'].items():
        for row in rows:
            want = expected[row['id']]
            if (any(row[k] != want[k] for k in ['status','data','events']) or
                    not all(s in row['storage'] for s in want['storage'])):
                mismatches.append([route,row['id']])
    write_json(out/'results.json',result | {'expectationMismatches':mismatches})
    if result['divergences']:
        raise HarnessError('post-callback observations diverged')
    if mutation:
        # The unchanged behavioral oracle must find completed counterexamples on
        # every route; importer errors and missing observations never count.
        witnesses = {r:[i for route,i in mismatches if route == r and
                       result['observations'][r][int(i)]['status'] != expected[i]['status']]
                     for r in adapters}
        if not all(witnesses.values()):
            raise HarnessError('post-callback mutation escaped detection')
    elif mismatches:
        raise HarnessError(f'post-callback behavior mismatch: {mismatches[:4]}')
    write_json(out/'complete.json',{'optimized':optimized,'mutation':mutation,
        'head':command(['git','rev-parse','HEAD']).strip()})
    print('post-callback balance observations passed' if not mutation else
          'post-callback balance mutation detected on all routes')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--optimized',action='store_true')
    parser.add_argument('--mutation',choices=['stale','unchecked'])
    args = parser.parse_args()
    campaign(args.output,args.optimized,args.mutation)


if __name__ == '__main__':
    main()
