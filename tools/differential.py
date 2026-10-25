"""Differential-runner primitives with deliberately explicit result adapters.

This module does not interpret Miri or Lean output. A project-specific adapter
must be grounded in the pinned command interface and provide both a category
and a canonical observation before two executions can be called a match.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Mapping, Protocol, Sequence


class Outcome(str, Enum):
    NORMAL = "normal"
    UB = "ub"
    PANIC = "panic"
    UNSUPPORTED = "unsupported"
    OTHER = "other"


class Comparison(str, Enum):
    MATCH = "match"
    DIFFERENT = "different"
    INCONCLUSIVE = "inconclusive"


@dataclass(frozen=True)
class ProcessResult:
    command: tuple[str, ...]
    returncode: int | None
    stdout: str
    stderr: str
    launch_error: str | None = None


@dataclass(frozen=True)
class ClassifiedResult:
    outcome: Outcome
    observation: str | None
    evidence: str


@dataclass(frozen=True)
class DifferentialResult:
    comparison: Comparison
    reason: str


@dataclass(frozen=True)
class DifferentialExecution:
    left_process: ProcessResult
    right_process: ProcessResult
    left: ClassifiedResult
    right: ClassifiedResult
    comparison: DifferentialResult


class ResultAdapter(Protocol):
    """An explicit engine-specific mapping from a process result to semantics."""

    def classify(self, result: ProcessResult) -> ClassifiedResult:
        """Return a category and grounded evidence, or raise on ambiguity."""


def run_command(
    command: Sequence[str],
    *,
    cwd: Path,
    env: Mapping[str, str] | None = None,
    timeout: float | None = None,
) -> ProcessResult:
    """Run an argv vector without a shell; classification remains a separate step."""
    argv = tuple(command)
    if not argv:
        raise ValueError("command must not be empty")
    try:
        completed = subprocess.run(
            argv,
            cwd=cwd,
            env=dict(env) if env is not None else None,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        return ProcessResult(argv, None, stdout, stderr, f"{type(exc).__name__}: {exc}")
    return ProcessResult(argv, completed.returncode, completed.stdout, completed.stderr)


def classify_result(result: ProcessResult, adapter: ResultAdapter | None) -> ClassifiedResult:
    """Require an engine-specific adapter; exit codes have no built-in meaning."""
    if adapter is None:
        raise ValueError("an explicit result adapter is required for classification")
    if result.launch_error is not None or result.returncode is None:
        reason = result.launch_error or "process completed without an exit status"
        return ClassifiedResult(Outcome.OTHER, None, f"infrastructure failure: {reason}")
    classified = adapter.classify(result)
    if not isinstance(classified, ClassifiedResult):
        raise TypeError("result adapter must return ClassifiedResult")
    if not isinstance(classified.outcome, Outcome):
        raise TypeError("result adapter must return one of the defined Outcome values")
    if not classified.evidence.strip():
        raise ValueError("result adapter must cite evidence for its classification")
    if classified.outcome in (Outcome.UB, Outcome.PANIC) and not (
        result.stdout.strip() or result.stderr.strip()
    ):
        raise ValueError(
            f"{classified.outcome.value} classification requires diagnostic output; "
            "a nonzero exit status alone is insufficient"
        )
    if classified.observation is not None and not classified.observation.strip():
        raise ValueError("canonical observation must be non-empty when provided")
    return classified


def compare(left: ClassifiedResult, right: ClassifiedResult) -> DifferentialResult:
    """Compare categories and canonical observations, avoiding category-only matches."""
    if left.outcome in (Outcome.UNSUPPORTED, Outcome.OTHER) or right.outcome in (
        Outcome.UNSUPPORTED,
        Outcome.OTHER,
    ):
        return DifferentialResult(
            Comparison.INCONCLUSIVE,
            f"inconclusive outcomes: {left.outcome.value} vs {right.outcome.value}",
        )
    if left.outcome is not right.outcome:
        return DifferentialResult(
            Comparison.DIFFERENT,
            f"outcome categories differ: {left.outcome.value} vs {right.outcome.value}",
        )
    if left.observation is None or right.observation is None:
        return DifferentialResult(
            Comparison.INCONCLUSIVE,
            "both adapters must provide canonical observations before a match can be reported",
        )
    if left.observation != right.observation:
        return DifferentialResult(Comparison.DIFFERENT, "canonical observations differ")
    return DifferentialResult(Comparison.MATCH, "outcomes and canonical observations agree")


def run_differential(
    left_command: Sequence[str],
    right_command: Sequence[str],
    *,
    cwd: Path,
    left_adapter: ResultAdapter,
    right_adapter: ResultAdapter,
    left_env: Mapping[str, str] | None = None,
    right_env: Mapping[str, str] | None = None,
    timeout: float | None = None,
) -> DifferentialExecution:
    """Run both engines and compare adapter-classified, normalized observations."""
    left_process = run_command(left_command, cwd=cwd, env=left_env, timeout=timeout)
    right_process = run_command(right_command, cwd=cwd, env=right_env, timeout=timeout)
    left = classify_result(left_process, left_adapter)
    right = classify_result(right_process, right_adapter)
    return DifferentialExecution(left_process, right_process, left, right, compare(left, right))
