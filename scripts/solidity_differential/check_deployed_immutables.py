"""Actual deployment bindings, inherited reads, getters and delegatecall contexts.

The constructor is executed by solc bytecode. Its captured runtime is checked by
Lean before import. A calldata-sensitive child detects wrong addresses as well
as confusing code identity with address(this). Gas is excluded.
"""
import argparse
import copy
import json
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .anvil import Anvil, SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .check_interface_word_static_call import address, SENDER
from .check_legacy_signature_calls import ORACLE, MASK
from .stateful import replay_three_routes
from .identity import ImplementationIdentity

FIXTURE = Path('Contracts/SolidityImportSmoke/DeployedImmutables.sol')
GETTERS = ['target', 'narrow', 'wide', 'tag', 'enabled', 'fixedValue', 'origin',
           'baseValue', 'ownValue', 'current', 'guarded', 'readTarget']


def declarations(ast, bases):
    result = []
    for contract in ast['nodes']:
        if contract.get('nodeType') != 'ContractDefinition' or contract['id'] not in bases:
            continue
        for node in contract['nodes']:
            if node.get('mutability') == 'immutable':
                result.append({'id': node['id'], 'source': FIXTURE.name, 'contract': contract['name'],
                               'name': node['name'], 'type': node['typeDescriptions']['typeString']})
    return result


def capture(node, creation, decls, refs):
    record = node.transact({'from': SENDER, 'data': creation, 'gas': hex(10000000)})
    if record['receipt']['status'] != '0x1':
        raise HarnessError('immutable constructor failed')
    account = record['receipt']['contractAddress']
    runtime = node.rpc('eth_getCode', account, record['receipt']['blockNumber'])
    raw = bytes.fromhex(runtime[2:])
    bindings = []
    for decl in decls:
        ranges = refs.get(str(decl['id']))
        if ranges:
            start = ranges[0]['start']
            bindings.append({k: v for k, v in decl.items() if k != 'id'} |
                            {'word': '0x' + raw[start:start+32].hex()})
    return {'version': 1, 'codeAddress': account, 'runtimeBytecode': runtime, 'bindings': bindings}


def boundaries(out, decls, runtime, manifest):
    """Malformed evidence and metadata are errors, not successful counterexamples."""
    cases = []
    def case(name, mutate):
        item = {'name': name, 'template': runtime['object'],
                'references': copy.deepcopy(runtime['immutableReferences']),
                'manifest': copy.deepcopy(manifest), 'accept': False}
        mutate(item)
        cases.append(item)
    case('valid', lambda x: x.update(accept=True))
    case('missing', lambda x: x['manifest']['bindings'].pop())
    case('duplicate', lambda x: x['manifest']['bindings'].append(x['manifest']['bindings'][0]))
    case('foreign', lambda x: x['manifest']['bindings'][0].update(contract='Other'))
    case('wrong-type', lambda x: x['manifest']['bindings'][0].update(type='uint256'))
    case('wrong-word', lambda x: x['manifest']['bindings'][0].update(word='0x'+'00'*32))
    case('noncanonical-address', lambda x: x['manifest']['bindings'][0].update(word='0x'+'ff'*32))
    case('bad-code-address', lambda x: x['manifest'].update(codeAddress='0x01'))
    case('truncated-code', lambda x: x['manifest'].update(runtimeBytecode=manifest['runtimeBytecode'][:-2]))
    case('opcode-change', lambda x: x['manifest'].update(runtimeBytecode='0xfe'+manifest['runtimeBytecode'][4:]))
    first = next(iter(runtime['immutableReferences']))
    case('foreign-reference', lambda x: x['references'].update({'999999': x['references'][first]}))
    case('unreferenced-binding', lambda x: x['references'].pop(first))
    case('empty-references', lambda x: x['references'].update({first: []}))
    case('short-range', lambda x: x['references'][first][0].update(length=31))
    case('out-of-range', lambda x: x['references'][first][0].update(start=len(runtime['object'])))
    case('overlap', lambda x: x['references'][first].append(x['references'][first][0]))
    for ident, ranges in runtime['immutableReferences'].items():
        if len(ranges) > 1:
            offset = 2 + 2*ranges[1]['start']
            def mismatch(x):
                code = x['manifest']['runtimeBytecode']
                byte = int(code[offset:offset+2], 16) ^ 1
                x['manifest']['runtimeBytecode'] = code[:offset] + f'{byte:02x}' + code[offset+2:]
            case('inconsistent-repeated-word', mismatch)
            break
    else:
        raise HarnessError('fixture lacks repeated immutable references')
    write_json(out / 'boundary-cases.json', cases)
    decl_terms = ',\n'.join('{ id := %d, source := %s, contract := %s, name := %s, solcType := %s }' %
        (d['id'], *(json.dumps(d[k]) for k in ['source', 'contract', 'name', 'type'])) for d in decls)
    driver = out / 'Boundaries.lean'
    driver.write_text('import Compiler.SolidityImport.DeployedImmutables\n'
        'open Lean Compiler.CompilationModel.SolidityImport.DeployedImmutables\n'
        '#eval show IO Unit from do\n'
        f'  let decls : Array Compiler.CompilationModel.SolidityImport.DeployedImmutables.Declaration := #[{decl_terms}]\n'
        f'  let cases ← IO.ofExcept (Json.parse (← IO.FS.readFile {json.dumps(str(out / "boundary-cases.json"))}))\n'
        '  for row in ← IO.ofExcept cases.getArr? do\n'
        '    let get := fun key => IO.ofExcept (row.getObjVal? key)\n'
        '    let result := check decls (← IO.ofExcept (← get "template").getStr?)\n'
        '      (← get "references") (← get "manifest")\n'
        '    unless result.isOk == (← IO.ofExcept (← get "accept").getBool?) do\n'
        '      let reason := match result with | .ok _ => "accepted" | .error e => e\n'
        '      throw (IO.userError s!"wrong immutable boundary: {(← get \"name\").compress}: {reason}")\n'
        '  for (ty, word, accepted) in [("uint24", 2^24-1, true), ("uint24", 2^24, false),\n'
        '      ("int24", 2^23, true), ("int24", 2^256-1, true),\n'
        '      ("int24", 2^256-2^23, true), ("int24", 2^256-2^23-1, false),\n'
        '      ("bytes4", 1, false), ("bytes4", 0x12345678*2^224, true),\n'
        '      ("bool", 2, false), ("uint256", 2^256, false)] do\n'
        '    unless validPatchWord ty word == accepted do throw (IO.userError "wrong canonical word")\n'
        '  unless scalarWord "int24" (2^24-1) == 2^256-1 &&\n'
        '      scalarWord "int24" (2^23) == 2^256-2^23 &&\n'
        '      scalarWord "int24" 60 == 60 do throw (IO.userError "wrong signed cleanup")\n'
        '  IO.println "immutable boundaries passed"\n')
    command(['turbo-lean', 'eval', driver, '--project-dir', '.', '--timeout-ms', '180000'],
            log=out / 'boundaries.log', timeout=210)
    if 'immutable boundaries passed' not in (out / 'boundaries.log').read_text():
        raise HarnessError('immutable boundary driver did not complete')


def campaign(out, optimized=False, variant=0, mutant=False):
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = FIXTURE.read_text()
    if mutant:
        source = source.replace('address(this) == original', 'address(this) == address(this)')
    (out / FIXTURE.name).write_text(source)
    settings = {'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 200},
                'metadata': {'bytecodeHash': 'none'}}
    compiled = solc_compile({'language': 'Solidity', 'sources': {FIXTURE.name: {'content': source}},
        'settings': {**settings, 'outputSelection': {'*': {'': ['ast'], '*': ['evm.bytecode.object',
            'evm.deployedBytecode', 'evm.methodIdentifiers']}}}}, out, out / 'solc',
        solc=Path.cwd() / '.lake/solidity-import/solc-0.7.6')
    contracts = compiled['contracts'][FIXTURE.name]
    contract = contracts[FIXTURE.stem]['evm']
    ast = compiled['sources'][FIXTURE.name]['ast']
    bases = next(n['linearizedBaseContracts'] for n in ast['nodes'] if n.get('name') == FIXTURE.stem)
    decls = declarations(ast, bases)
    code, child, proxy = address(0), address(1), address(2)
    values = [child, 0xffffff if variant else 37, (1<<128)-1 if variant else 93,
              bytes.fromhex('abcdef01'), bool(variant), -8388608 if variant else -1]
    creation = '0x' + contract['bytecode']['object'] + encode(
        ['address','uint24','uint128','bytes4','bool','int24'], values).hex()
    with Anvil(out / 'capture') as node:
        manifest = capture(node, creation, decls, contract['deployedBytecode']['immutableReferences'])
    if manifest['codeAddress'] != code:
        raise HarnessError('unexpected immutable deployment address')
    write_json(out / 'deployment.json', manifest)
    boundaries(out, decls, contract['deployedBytecode'], manifest)
    template = Path('Contracts/SolidityImportSmoke/LegacyStaticWordModel.lean').read_text()
    start = template.index('solidity_import imported')
    end = template.index('end SolidityImportSmoke', start)
    template = template[:start] + (f'solidity_import imported from {json.dumps(str(out))} entry "{FIXTURE.name}"\n'
        '  using {\n    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,\n'
        f'    optimizerRuns := {"some 200" if optimized else "none"}, bytecodeHash := "none",\n'
        '    deployedImmutables := some "deployment.json" }\n'
        f'  contract {FIXTURE.stem}\n' + ''.join(f'  function {name}()\n' for name in GETTERS)) + template[end:]
    # Keep the checked binding identity alongside the executable model.
    marker = 'end SolidityImportSmoke.LegacyStaticWordModel'
    report = f'#eval IO.FS.writeFile {json.dumps(str(out / "report.txt"))} imported.report.toText\n'
    template = template.replace(marker, report + marker)
    driver = out / 'Driver.lean'
    driver.write_text(template)
    # A binding must not broaden legacy expression admission, and indirect reads
    # must reject without evidence even in contracts with several state variables.
    for name, roots_text, profile_text, diagnostic in [
            ('signed-read', '  function signedUnused()\n', template, 'does not support type int24'),
            ('missing-indirect', '  function readTarget()\n',
             template.replace('deployedImmutables := some "deployment.json"',
                              'deployedImmutables := none'), 'requires a checked deployed binding')]:
        start = profile_text.index('  function ')
        stop = profile_text.index('#eval IO.FS.writeFile', start)
        rejected = out / (name + '.lean')
        # Compile-mode main would be irrelevant after an import rejection.
        rejected.write_text(profile_text[:start] + roots_text + profile_text[stop:])
        try:
            command(['turbo-lean', 'eval', rejected, '--project-dir', '.', '--timeout-ms', '180000'],
                    log=out / (name + '.log'), timeout=210)
        except HarnessError:
            log = (out / (name + '.log')).read_text()
            if '[solidity-import:unsupported]' not in log or diagnostic not in log:
                raise HarnessError('unexpected immutable import rejection: ' + name + '\n' + log)
        else:
            raise HarnessError('unsupported immutable read admitted: ' + name)
    selectors = [int(contract['methodIdentifiers'][name+'()'], 16) for name in GETTERS]
    write_json(out / 'selectors.json', selectors)
    command(['lake','env','lean','--run',driver,'compile',out/'selectors.json',out/'model.yul'],
            log=out/'compile.log', timeout=900)
    model = solc_compile({'language':'Yul','sources':{'Model.yul':{'content':(out/'model.yul').read_text()}},
        'settings':{'evmVersion':'osaka','optimizer':{'enabled':True,'runs':466},
                    'outputSelection':{'*':{'*':['evm.bytecode.object']}}}},out,out/'model-solc',solc=SOLC)
    model_code = next(iter(model['contracts']['Model.yul'].values()))['evm']['bytecode']['object']
    mock = solc_compile({'language':'Solidity','sources':{ORACLE.name:{'content':ORACLE.read_text()}},
        'settings':{'evmVersion':'osaka','optimizer':{'enabled':True,'runs':466},
                    'outputSelection':{'*':{'*':['evm.bytecode.object','evm.deployedBytecode.object']}}}},
        out,out/'mock-solc',solc=SOLC)['contracts'][ORACLE.name]['SignatureCallOracle']['evm']
    mock_code = '0x'+mock['bytecode']['object']+encode(
        ['uint256','bool','uint256','uint256'],[0,False,32,MASK]).hex()
    proxy_code = '0x'+contracts['ImmutableDelegateProxy']['evm']['bytecode']['object']+encode(['address'],[code]).hex()
    environment = {'program':'hash-static-oracle-v1','accounts':[str(int(child,16))],
                   'emptyAccounts':[], 'gas':'1000000','recoveries':[]}
    initial = [(child,'0x'+i.to_bytes(32,'big').hex(),'0x'+v.to_bytes(32,'big').hex())
               for i,v in enumerate([0,0,32,MASK])]
    all_results = {}
    for label, account in [('direct',code),('delegate',proxy)]:
        txs, expected = [], {}
        words = [int(child,16), values[1], values[2], int.from_bytes(values[3],'big')<<224,
                 int(values[4]),91,int(code,16),17,29,int(account,16),values[1],
                 int.from_bytes(keccak(keccak(text='read(address)')[:4]+encode(['address'],[account])),'big')]
        for i,(name,word) in enumerate(zip(GETTERS,words,strict=True)):
            txs.append({'id':str(i),'function':name,'args':[],'sender':SENDER,'target':account,
                'data':'0x'+contract['methodIdentifiers'][name+'()'],'value':'0x0',
                'timestamp':1000000100+i,'blockNumber':4+i})
            expected[str(i)] = ('ok','0x'+word.to_bytes(32,'big').hex())
            if label == 'delegate' and name == 'guarded':
                expected[str(i)] = ('revert','0x'+(keccak(text='Error(string)')[:4]+encode(['string'],['delegate'])).hex())
        adapters = {'source':EVM(out/label/'A',[creation,mock_code,proxy_code],initial),
            'model':Denote(out/label/'B',driver,account,initial,byte_call_environment=environment,
                identity=ImplementationIdentity(driver, [out/'deployment.json', out/FIXTURE.name]),
                account_code=[(child,'0x'+mock['deployedBytecode']['object'])]),
            'compiled':EVM(out/label/'C',['0x'+model_code,mock_code,proxy_code],initial)}
        result = replay_three_routes(txs,adapters)
        mismatches = [(route,row['id']) for route,rows in result['observations'].items()
                      for row in rows if (row['status'],row['data']) != expected[row['id']]]
        write_json(out/label/'results.json',result | {'expectationMismatches':mismatches})
        if result['divergences']:
            raise HarnessError(f'immutable route divergence: {label}')
        if mutant and label == 'delegate':
            want = {(route, str(GETTERS.index('guarded'))) for route in adapters}
            if set(mismatches) != want:
                raise HarnessError('guard mutation lacks completed counterexamples on every route')
        elif mismatches:
            raise HarnessError(f'immutable behavior mismatch: {label}: {mismatches}')
        all_results[label] = {'transactions':txs,'expected':expected}
    write_json(out/'complete.json', {'optimized':optimized,'variant':variant,'mutant':mutant,'results':all_results})
    print('deployed immutable source/model/generated checks passed')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--optimized',action='store_true')
    p.add_argument('--mutant',action='store_true')
    p.add_argument('--variant',type=int,choices=(0,1),default=0)
    args=p.parse_args()
    campaign(args.output,args.optimized,args.variant,args.mutant)

if __name__ == '__main__':
    main()
