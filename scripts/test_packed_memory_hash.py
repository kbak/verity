"""Independent packed-layout anchors; no Lean or EVM required for these checks."""
import unittest

from keccak256 import keccak_256
from solidity_differential.check_packed_memory_hash import (
    CONCRETE, CONCRETE_HASH, CONCRETE_PREIMAGE, FIXTURE, MOD, SHIFTS,
    packed_preimage, replay_memory, variants, vectors, word,
)


class PackedMemoryHashTests(unittest.TestCase):
    def test_concrete_fixed_expectation(self):
        payload = packed_preimage(*CONCRETE)
        self.assertEqual(payload.hex(), CONCRETE_PREIMAGE)
        self.assertEqual(len(payload), 58)
        self.assertEqual(keccak_256(payload).hex(), CONCRETE_HASH)

    def test_signed_and_unsigned_widths(self):
        payload = packed_preimage((1 << 160) - 1, -(1 << 23), (1 << 23) - 1, MOD - 1)
        self.assertEqual(payload, b'\xff' * 20 + b'\x80\0\0\x7f\xff\xff' + b'\xff' * 32)
        self.assertEqual(packed_preimage(0, -1, 0, 0), bytes(20) + b'\xff' * 3 + bytes(35))

    def test_out_of_range_fields_are_not_silently_truncated(self):
        for values in ((1 << 160, 0, 0, 0), (0, 1 << 23, 0, 0),
                       (0, 0, -(1 << 23) - 1, 0), (0, 0, 0, MOD)):
            with self.subTest(values=values), self.assertRaises(OverflowError):
                packed_preimage(*values)

    def test_overlapping_writes_match_width_specification(self):
        for values in vectors():
            for shift in SHIFTS:
                self.assertEqual(replay_memory(values, shift), packed_preimage(*values))

    def test_padded_encoding_is_detected_by_unchanged_expectation(self):
        padded = b''.join(map(word, CONCRETE))
        self.assertEqual(len(padded), 128)
        self.assertNotEqual(padded.hex(), CONCRETE_PREIMAGE)
        self.assertNotEqual(keccak_256(padded).hex(), CONCRETE_HASH)

    def test_source_mutations_leave_original_unchanged(self):
        source = FIXTURE.read_text()
        rows = variants(source)
        self.assertEqual(rows['original'], source)
        self.assertEqual(rows['renamed'].replace('renamedPacked', 'hashPacked'), source)
        self.assertIn('abi.encode(account, left, right, salt)', rows['padded'])
        self.assertIn('xor(left, 1)', rows['changed-body'])


if __name__ == '__main__':
    unittest.main()
