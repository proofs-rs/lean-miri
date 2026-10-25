#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

python3 "$repo_root/tests/data_race/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/data_race.rs" \
  "$repo_root/tests/data_race/reference.rs.in" \
  "$tmp_dir/data_race_reference.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/data_race_reference.rs" \
  -o "$tmp_dir/data_race_reference"
(
  cd "$repo_root"
  lake build Miri.Concurrency.GlobalStateVerification Miri.Concurrency.AtomicAccess Miri.Concurrency.Scheduler Miri.Concurrency.Join Miri.Concurrency.Lifecycle Miri.Concurrency.Deadline
)
"$tmp_dir/data_race_reference" > "$tmp_dir/source.out"
sed '/^sync:/d' "$tmp_dir/source.out" > "$tmp_dir/global-source.out"
sed -n '/^sync:/p' "$tmp_dir/source.out" > "$tmp_dir/sync-source.out"
(cd "$repo_root" && lake env lean --run tests/data_race/GlobalState.lean) \
  > "$tmp_dir/lean.out"
if ! diff -u "$tmp_dir/global-source.out" "$tmp_dir/lean.out"; then
  echo "Lean global clock/reuse results differ from extracted pinned Miri methods" >&2
  exit 1
fi
(cd "$repo_root" && lake env lean --run tests/data_race/AllocationSyncClock.lean) \
  > "$tmp_dir/sync-lean-all.out"
sed '/^sync:bounds:/d' "$tmp_dir/sync-lean-all.out" > "$tmp_dir/sync-lean.out"
if ! diff -u "$tmp_dir/sync-source.out" "$tmp_dir/sync-lean.out"; then
  echo "Lean allocation synchronization clocks differ from extracted pinned Miri method" >&2
  exit 1
fi
python3 "$repo_root/tests/data_race/extract_thread_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/thread.rs" \
  "$repo_root/tests/data_race/thread_reference.rs.in" \
  "$tmp_dir/thread_reference.rs"
rustc --edition=2024 -Awarnings "$tmp_dir/thread_reference.rs" \
  -o "$tmp_dir/thread_reference"
"$tmp_dir/thread_reference" > "$tmp_dir/thread_source.out"
(cd "$repo_root" && lake env lean --run tests/data_race/ThreadManager.lean) \
  > "$tmp_dir/thread_lean.out"
if ! diff -u "$tmp_dir/thread_source.out" "$tmp_dir/thread_lean.out"; then
  echo "Lean thread-manager results differ from extracted pinned Miri methods" >&2
  exit 1
fi
(cd "$repo_root" && lake env lean --run tests/data_race/LifecycleObligations.lean) \
  > "$tmp_dir/lifecycle.out"
if ! diff -u "$repo_root/tests/data_race/LifecycleObligations.expected" \
    "$tmp_dir/lifecycle.out"; then
  echo "thread callback/TLS obligations changed or were completed implicitly" >&2
  exit 1
fi
(cd "$repo_root" && lake env lean --run tests/data_race/AtomicAccess.lean) \
  > "$tmp_dir/atomic-access.out"
if ! diff -u "$repo_root/tests/data_race/AtomicAccess.expected" \
    "$tmp_dir/atomic-access.out"; then
  echo "atomic intrinsic preflight behavior changed" >&2
  exit 1
fi
python3 "$repo_root/tests/data_race/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/data_race.rs" \
  "$repo_root/tests/data_race/atomic_access_reference.rs.in" \
  "$tmp_dir/atomic_access_reference.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/atomic_access_reference.rs" \
  -o "$tmp_dir/atomic_access_reference"
"$tmp_dir/atomic_access_reference" > "$tmp_dir/atomic-source-all.out"
sed -n '/^atomic:/p' "$tmp_dir/atomic-source-all.out" > "$tmp_dir/atomic-source.out"
sed -n '/^atomic:/p' "$tmp_dir/atomic-access.out" > "$tmp_dir/atomic-lean.out"
if ! diff -u "$tmp_dir/atomic-source.out" "$tmp_dir/atomic-lean.out"; then
  echo "Lean atomic access checks differ from extracted pinned Miri method" >&2
  exit 1
fi
(cd "$repo_root" && lake env lean --run tests/data_race/Scheduler.lean) \
  > "$tmp_dir/scheduler.out"
if ! diff -u "$repo_root/tests/data_race/Scheduler.expected" "$tmp_dir/scheduler.out"; then
  echo "scheduler decisions or explicit environment obligations changed" >&2
  exit 1
fi
python3 "$repo_root/tests/data_race/extract_scheduler_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/scheduler.rs" \
  "$repo_root/tests/data_race/scheduler_reference.rs.in" \
  "$tmp_dir/scheduler_reference.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/scheduler_reference.rs" \
  -o "$tmp_dir/scheduler_reference"
"$tmp_dir/scheduler_reference" > "$tmp_dir/scheduler-source.out"
sed -n '/^scheduler:candidates:/p' "$tmp_dir/scheduler.out" > "$tmp_dir/scheduler-lean-source-cases.out"
if ! diff -u "$tmp_dir/scheduler-source.out" "$tmp_dir/scheduler-lean-source-cases.out"; then
  echo "Lean runnable-thread order differs from extracted pinned scheduler iterator" >&2
  exit 1
fi
(
  cd "$repo_root"
  lake env lean --run tests/data_race/DetachedJoinRuntime.lean
) > "$tmp_dir/detached-join-runtime.out"
if ! diff -u "$repo_root/tests/data_race/DetachedJoinRuntime.expected" \
    "$tmp_dir/detached-join-runtime.out"; then
  echo "detached join rejection ordering or side-effect guards changed" >&2
  exit 1
fi
(
  cd "$repo_root"
  lake env lean --run tests/data_race/JoinAndTermination.lean
) > "$tmp_dir/join-termination.out"
if ! diff -u "$repo_root/tests/data_race/JoinAndTermination.expected" \
    "$tmp_dir/join-termination.out"; then
  echo "termination reporting or join/wakeup obligations changed" >&2
  exit 1
fi
(
  cd "$repo_root"
  lake env lean --run tests/data_race/Deadline.lean
) > "$tmp_dir/deadline.out"
if ! diff -u "$repo_root/tests/data_race/Deadline.expected" \
    "$tmp_dir/deadline.out"; then
  echo "deadline sweep or timeout callback sequencing changed" >&2
  exit 1
fi
echo "matched source-extracted vector-index reuse predicates and SeqCst fence updates"
echo "matched source-extracted thread creation, lookup, count, activation, blocking, and detach methods"
echo "verified explicit unblock-callback and ordered TLS-cleanup obligations"
echo "verified atomic ordering conversion, alignment staging, read-only rules, and fence NOP"
echo "matched read-only and callback-order cases against extracted atomic_access_check"
echo "matched runnable-thread rotation against extracted pinned scheduler iterator"
echo "verified distinct Miri termination categories and ordered join/wakeup obligations"
echo "verified source-ordered deadline mutations and timeout callback obligations"
