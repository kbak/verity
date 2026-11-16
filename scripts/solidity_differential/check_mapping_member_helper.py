"""Mapping helper transport must retain the existing struct-member mapping route."""
import argparse
from pathlib import Path

from .check_storage_reference_routes import (
    CONTRACT, FIXTURE, SIGNATURES, build_source, control_inputs, require_outcome, run_routes,
)
from .engine import HarnessError, write_json
from .hash_execution import compile_generated, pinned_compiler
from .pinned_sequence import SENDERS, create_address
from .storage_reference_oracle import specification
from .storage_sequence_execution import prepare_model


def run(output):
    output = output.resolve()
    text = FIXTURE.read_text()
    anchor = 'return bucket.records[key];'
    if text.count(anchor) != 1:
        raise HarnessError('mapping member helper anchor changed')
    text = text.replace(anchor, 'return lookup(bucket.records, key);')
    text = text.replace('    function locate(bytes32 key)',
        '    function lookup(mapping(bytes32 => Record) storage rows, bytes32 key)\n'
        '        internal view returns (Record storage) { return rows[key]; }\n\n'
        '    function locate(bytes32 key)')
    solc, compiler = pinned_compiler()
    source, built = build_source(output, text, solc)
    spec = control_inputs(specification(create_address(SENDERS[0]), SENDERS[0], 0))
    driver, snapshot = prepare_model(output / 'imported', source, CONTRACT,
                                     list(SIGNATURES.values()), compiler)
    compiled = compile_generated(output / 'imported', snapshot, solc)
    result = run_routes(output / 'execution', spec, source, built, driver, compiled)
    require_outcome(result)
    write_json(output / 'complete.json', {'status': 'passed', 'threeRoutes': True})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    run(**vars(parser.parse_args()))
