import importlib.util
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

MODULE = Path(__file__).resolve().parents[1] / 'tools/summarize-cpu-samples.py'
spec = importlib.util.spec_from_file_location('cpu_sampling', MODULE)
cpu = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cpu)


class CpuSamplingTests(unittest.TestCase):
    def fixture(self, prefix):
        # lld has an extra page between the header and executable LOADs.
        Path(str(prefix) + '.maps').write_text(
            '100000-101000 r--p 00000000 00:00 0 /example\n'
            '103000-104000 r-xp 00002000 00:00 0 /example\n')

    def test_pie_header_bias_and_caller_return_boundary(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / 'sample'
            self.fixture(prefix)
            Path(str(prefix) + '.samples').write_bytes(struct.pack('<QQQQ', 50, 0x103015, 7, 0x103030))
            with patch.object(cpu.subprocess, 'check_output', side_effect=[
                    'Type: DYN (Position-Independent Executable file)',
                    'LOAD 0x000000 0x000000 0x000000 0x1000 0x1000 R 0x1000']), \
                 patch.object(cpu, 'symbols', return_value=[(0x3010, 0x10, 'leaf'), (0x3020, 0x10, 'caller')]):
                result = cpu.summarize(prefix, stack_depth=1)
            phase = result['phases']['all']
            self.assertEqual(phase['top'][0]['symbol'], 'example:leaf')
            self.assertEqual({x['symbol'] for x in phase['cumulative_top']}, {'example:leaf', 'example:caller'})

    def test_truncated_records_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / 'sample'
            Path(str(prefix) + '.maps').write_text('')
            Path(str(prefix) + '.samples').write_bytes(b'bad')
            with self.assertRaisesRegex(ValueError, 'truncated'):
                cpu.summarize(prefix)

    def test_phase_boundaries_do_not_attribute_other_intervals(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / 'sample'
            Path(str(prefix) + '.maps').write_text('')
            Path(str(prefix) + '.samples').write_bytes(b''.join(struct.pack('<QQQ', t, 0, 7) for t in [1, 10, 19, 20]))
            phases = Path(tmp) / 'phases.json'
            phases.write_text('{"events":{"lower_start":10,"lower_end":20}}')
            result = cpu.summarize(prefix, phases)
            self.assertEqual(result['phases']['all']['samples'], 4)
            self.assertEqual(result['phases']['lower']['samples'], 2)

    def test_nonzero_dynamic_header_address_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / 'sample'
            self.fixture(prefix)
            Path(str(prefix) + '.samples').write_bytes(b'')
            with patch.object(cpu.subprocess, 'check_output', side_effect=[
                    'Type: DYN (Shared object file)', 'LOAD 0x000000 0x100000 0x100000']), \
                 self.assertRaisesRegex(ValueError, 'unsupported nonzero'):
                cpu.summarize(prefix)


if __name__ == '__main__':
    unittest.main()
