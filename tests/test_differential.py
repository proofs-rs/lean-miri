import unittest

from tools.differential import (
    ClassifiedResult,
    Comparison,
    Outcome,
    ProcessResult,
    classify_result,
    compare,
)


class FixedAdapter:
    def __init__(self, outcome, observation):
        self.value = ClassifiedResult(outcome, observation, "test adapter fixture")

    def classify(self, result):
        return self.value


class DifferentialScaffoldTests(unittest.TestCase):
    def setUp(self):
        self.failed_process = ProcessResult(("engine",), 1, "", "failed")

    def test_nonzero_exit_code_is_not_classified_without_an_adapter(self):
        with self.assertRaisesRegex(ValueError, "explicit result adapter"):
            classify_result(self.failed_process, None)

    def test_nonzero_exit_code_and_empty_output_cannot_be_called_ub(self):
        result = ProcessResult(("engine",), 1, "", "")
        with self.assertRaisesRegex(ValueError, "exit status alone is insufficient"):
            classify_result(result, FixedAdapter(Outcome.UB, "return code was nonzero"))

    def test_launch_failure_overrides_adapter_and_stays_inconclusive(self):
        broken = ProcessResult(("engine",), None, "", "", "FileNotFoundError: engine")
        crashed = classify_result(broken, FixedAdapter(Outcome.NORMAL, "adapter guessed normal"))
        normal = classify_result(
            ProcessResult(("engine",), 0, "value=1", ""),
            FixedAdapter(Outcome.NORMAL, "value=1"),
        )
        self.assertEqual(Outcome.OTHER, crashed.outcome)
        self.assertEqual(Comparison.INCONCLUSIVE, compare(crashed, normal).comparison)

    def test_same_category_with_different_observation_is_not_a_match(self):
        left = classify_result(self.failed_process, FixedAdapter(Outcome.UB, "out-of-bounds read at 4"))
        right = classify_result(self.failed_process, FixedAdapter(Outcome.UB, "out-of-bounds read at 8"))
        result = compare(left, right)
        self.assertEqual(Comparison.DIFFERENT, result.comparison)

    def test_equal_supported_observations_match(self):
        left = classify_result(self.failed_process, FixedAdapter(Outcome.PANIC, "panic: bounds"))
        right = classify_result(self.failed_process, FixedAdapter(Outcome.PANIC, "panic: bounds"))
        self.assertEqual(Comparison.MATCH, compare(left, right).comparison)

    def test_unsupported_category_remains_inconclusive(self):
        left = classify_result(self.failed_process, FixedAdapter(Outcome.UNSUPPORTED, "feature X"))
        right = classify_result(self.failed_process, FixedAdapter(Outcome.UNSUPPORTED, "feature X"))
        self.assertEqual(Comparison.INCONCLUSIVE, compare(left, right).comparison)

    def test_missing_observation_cannot_create_false_match(self):
        left = ClassifiedResult(Outcome.NORMAL, None, "adapter evidence")
        right = ClassifiedResult(Outcome.NORMAL, None, "adapter evidence")
        self.assertEqual(Comparison.INCONCLUSIVE, compare(left, right).comparison)


if __name__ == "__main__":
    unittest.main()
