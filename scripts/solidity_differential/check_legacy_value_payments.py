"""Original-bytecode payment calls: return shapes, gas price, state and rollback."""
import argparse
import hashlib
import json
from pathlib import Path

from eth_abi import encode
from .anvil import Anvil
from .engine import HarnessError, command, solc_compile, source_compiler, write_json
from .source_gas_trace import evidence, source_sites

FIXTURE = Path("Contracts/SolidityImportSmoke/LegacyValuePayments.sol")
MODEL = "Contracts.SolidityImportSmoke.LegacyValuePaymentsModel"
CHILDREN = list(range(0x2234, 0x223d))
EMPTY = 0x3344
MAX = (1 << 256) - 1
BALANCE = 100000000


def address(value):
    return "0x" + value.to_bytes(20, "big").hex()


def child_code(index):
    # Record calldata word at byte 36, then return/revert a fixed memory slice.
    length = [0, 32, 32, 32, 1, 31, 33, 64, 32][index]
    value = 0 if index == 1 else MAX if index == 3 else 2
    return ("6024356000557f" + value.to_bytes(32, "big").hex() +
            "60005260" + bytes([length]).hex() + "6000" + ("fd" if index == 8 else "f3"))


def replay(out, payload, optimized, mutant=None):
    write_json(out / "input.json", payload)
    prefix = Path(MODEL.replace(".", "/") + ".lean").read_text()
    if optimized:
        prefix = prefix.replace("optimizerRuns := none", "optimizerRuns := some 200")
    if mutant:
        # Mutate executable model guards, preserving the independently recorded
        # bytecode observations. Compiler/instrumentation errors never count.
        mutation = """
open Compiler.CompilationModel
private partial def dropGuard : Stmt → Stmt
  | .require condition message =>
      .require (if message == MUTANT then .literal 1 else condition) message
  | .ite condition yes no => .ite condition (yes.map dropGuard) (no.map dropGuard)
  | .forEach name count body => .forEach name count (body.map dropGuard)
  | statement => statement
private def candidate : CompilationModel :=
  { SolidityImportSmoke.LegacyValuePaymentsModel.model with
    functions := SolidityImportSmoke.LegacyValuePaymentsModel.model.functions.map
      fun fn => { fn with body := fn.body.map dropGuard } }
""".replace("MUTANT", json.dumps(mutant))
        prefix = prefix.replace("def main (args", mutation + "\ndef main (args")
        prefix = prefix.replace("    SolidityImportSmoke.LegacyValuePaymentsModel.model\n", "    candidate\n")
    wrapper = out / "Run.lean"
    wrapper.write_text(prefix + "\n#eval main " + json.dumps(
        [str(out / "input.json"), str(out / "output.json")]) + "\n")
    command(["turbo-lean", "eval", wrapper, "--project-dir", Path.cwd(),
             "--timeout-ms", "180000"], log=out / "model.log", timeout=210)
    return json.loads((out / "output.json").read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--optimized", action="store_true")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if not args.skip_build:
        command(["turbo-lean", "--json", "build", MODEL], log=out / "build.log", timeout=1800)
    source = FIXTURE.read_text()
    request = {"language": "Solidity", "sources": {FIXTURE.name: {"content": source}},
        "settings": {"evmVersion": "istanbul", "optimizer": {"enabled": args.optimized, "runs": 200},
            "metadata": {"bytecodeHash": "none"}, "outputSelection": {"*": {"*": [
                "evm.bytecode.object", "evm.deployedBytecode.object", "evm.deployedBytecode.sourceMap",
                "evm.methodIdentifiers"], "": ["ast"]}}}}
    release, solc = source_compiler({"solc": "0.7.6+commit.7338295f"})
    built = solc_compile(request, FIXTURE.parent, out / "source", solc=solc)
    evm = built["contracts"][FIXTURE.name]["LegacyValuePayments"]["evm"]
    runtime = evm["deployedBytecode"]["object"]
    sites = source_sites(built["sources"][FIXTURE.name]["ast"])
    selectors = evm["methodIdentifiers"]
    # Native and asset paths share checked arithmetic, but only native caps the rate.
    cases = []
    for asset in [0, *CHILDREN, EMPTY]:
        for receiver in [0, EMPTY]:
            for rate in [0, 3, 9]:
                for fail in [False, True]:
                    cases.append([17, 3, rate, address(asset), address(receiver), fail])
    for child in CHILDREN:
        cases.append([17, 3, 9, address(0), address(child), False])
    for units, overhead, rate in [(0, 0, MAX), (MAX, 1, 1), (MAX, 0, 2), (BALANCE, 1, 1)]:
        for asset in [0, CHILDREN[2]]:
            cases.append([units, overhead, rate, address(asset), address(EMPTY), False])
    types = ["uint256", "uint256", "uint256", "address", "address", "bool"]
    cases = [("pay(uint256,uint256,uint256,address,address,bool)", types, values) for values in cases]
    cases += [("cursor(address)", ["address"], [address(child)]) for child in CHILDREN + [EMPTY]]
    transactions, expected = [], []
    fees = 0
    with Anvil(out / "node") as node:
        sender = node.rpc("eth_accounts")[0]
        deployment = node.transact({"from": sender, "data": "0x" + evm["bytecode"]["object"],
                                   "gas": hex(10000000)})
        if deployment["receipt"]["status"] != "0x1":
            raise HarnessError("payment deployment failed")
        caller = deployment["receipt"]["contractAddress"]
        if node.rpc("eth_getCode", caller, "latest") != "0x" + runtime:
            raise HarnessError("original runtime mismatch")
        node.rpc("anvil_setBalance", caller, hex(BALANCE))
        sender_balance = int(node.rpc("eth_getBalance", sender, "latest"), 16)
        for index, child in enumerate(CHILDREN):
            node.rpc("anvil_setCode", address(child), "0x" + child_code(index))
            if node.rpc("eth_getCode", address(child), "latest") != "0x" + child_code(index):
                raise HarnessError("child runtime mismatch")
        accounts = CHILDREN + [EMPTY, int(sender, 16)]
        observe = [[str(int(caller, 16)), "0"]] + [[str(child), "0"] for child in CHILDREN]
        for index, (signature, types, values) in enumerate(cases):
            selector = selectors[signature]
            payload = encode(types, values)
            node.rpc("anvil_setNextBlockBaseFeePerGas", "0x0")
            record = node.transact({"from": sender, "to": caller, "data": "0x" + selector + payload.hex(),
                                    "gas": hex(300000), "gasPrice": hex(7)})
            receipt = record["receipt"]
            txhash = receipt["transactionHash"]
            trace = node.rpc("debug_traceTransaction", txhash,
                {"enableMemory": True, "disableStack": False, "disableStorage": True})
            write_json(out / "node" / (txhash + ".gas.json"), trace)
            block = node.rpc("eth_getBlockByHash", receipt["blockHash"], False)
            meter, gas_left, _ = evidence(trace, record["call"], record["prestate"], runtime,
                evm["deployedBytecode"]["sourceMap"], sites, coinbase=int(block["miner"], 16))
            transactions.append({"id": str(index), "function": signature.split("(")[0], "args": [
                str(int.from_bytes(payload[i:i + 32], "big")) for i in range(0, len(payload), 32)],
                "selector": str(int(selector, 16)), "sender": str(int(sender, 16)),
                "target": str(int(caller, 16)), "value": "0", "gasPrice": "7",
                "timestamp": str(int(block["timestamp"], 16)),
                "blockNumber": str(int(receipt["blockNumber"], 16)), "observe": observe,
                "observeAccounts": [str(account) for account in accounts], "sourceGas": meter})
            status = "ok" if receipt["status"] == "0x1" else "revert"
            if status == "revert" and record["call"].get("error") != "execution reverted":
                raise HarnessError("unexpected exceptional root")
            # SequenceRunner is a frame model: normalize sender fees and envelope nonce.
            fees += int(receipt["gasUsed"], 16) * int(receipt["effectiveGasPrice"], 16)
            def account_state(account, with_code=False):
                result = {"address": account,
                    "nonce": 0 if account == sender else int(node.rpc("eth_getTransactionCount", account, "latest"), 16),
                    "balance": int(node.rpc("eth_getBalance", account, "latest"), 16) + (fees if account == sender else 0)}
                if with_code:
                    result["code"] = node.rpc("eth_getCode", account, "latest")
                return result
            expected.append({"id": str(index), "status": status, "data": record["call"].get("output", "0x"),
                "sourceGasLeft": gas_left, "deployment": {"creator": account_state(caller),
                    "accounts": [account_state(address(a), True) for a in accounts]},
                "slots": [int(node.rpc("eth_getStorageAt", address(int(a)), hex(int(s)), "latest"), 16)
                          for a, s in observe]})
        initial = {"account": str(int(caller, 16)), "storage": [["0", "0"]], "accountNonce": "1",
            "initialBalances": [[str(int(caller, 16)), str(BALANCE)], [str(int(sender, 16)), str(sender_balance)]],
            "accountCode": [[str(child), "0x" + child_code(i)] for i, child in enumerate(CHILDREN)],
            "paymentChildren": CHILDREN, "emptyChildren": [EMPTY, int(sender, 16)], "transactions": transactions}
        write_json(out / "node-provenance.json", node.provenance)
    write_json(out / "expected.json", expected)
    rows = replay(out, initial, args.optimized)
    if len(rows) != len(expected):
        raise HarnessError("missing model transactions")
    for actual, want in zip(rows, expected):
        for key in ["id", "status", "data", "sourceGasLeft", "deployment"]:
            if actual[key] != want[key]:
                raise HarnessError(f'{want["id"]}: {key}: {actual[key]} != {want[key]}')
        slots = {(int(a, 16), int(slot, 16)): int(value, 16) for a, slot, value in actual["storage"]}
        wanted_slots = {(int(a), int(slot)): value for (a, slot), value in zip(observe, want["slots"])}
        if len(slots) != len(actual["storage"]) or slots != wanted_slots:
            raise HarnessError(f'{want["id"]}: caller/child storage or rollback differs')
    mutations = []
    for mutant in ["native payment", "asset payment", "outer"]:
        folder = out / ("mutant-" + mutant.replace(" ", "-"))
        folder.mkdir()
        altered = replay(folder, initial, args.optimized, mutant)
        if len(altered) != len(rows):
            raise HarnessError("mutant omitted observations")
        witnesses = [i for i, (a, b) in enumerate(zip(altered, rows)) if a != b]
        if not witnesses:
            raise HarnessError("payment guard mutant escaped: " + mutant)
        mutations.append({"guard": mutant, "firstWitness": witnesses[0], "differences": len(witnesses)})
    write_json(out / "mutations.json", mutations)
    write_json(out / "complete.json", {"cases": len(rows), "mutantsDetected": len(mutations), "optimized": args.optimized, "solc": release,
        "fixtureSha256": hashlib.sha256(source.encode()).hexdigest(),
        "head": command(["git", "rev-parse", "HEAD"]).strip(),
        "workingTreeClean": not command(["git", "status", "--porcelain"]).strip(),
        "scope": "original-bytecode/Denote frame evidence; sender fees and nonce normalized"})
    print(f"{len(rows)} original-bytecode payment cases passed")


if __name__ == "__main__":
    main()
