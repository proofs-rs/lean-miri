"""Source-order regression for the detached-thread join error path."""

from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
UPSTREAM = ROOT / "upstream/miri-source/src/concurrency/thread.rs"
LEAN = ROOT / "Miri/Interpreter/ThreadMachine.lean"
UPSTREAM_SHA256 = "6df8d025689d9fea1ee60a7db0ca493667725b8947d80df12c7754165487a6a6"
LEAN_SHA256 = "6dca48f885f192be0fd565dea6c340ce2fe181c01113572d191ad4b340cfb846"


def body_after(source: str, marker: str, end: str) -> str:
    start = source.index(marker)
    finish = source.index(end, start)
    return source[start:finish]


def test_detached_join_fails_before_join_state_or_sync_effects() -> None:
    upstream = UPSTREAM.read_text()
    lean = LEAN.read_text()
    assert sha256(upstream.encode()).hexdigest() == UPSTREAM_SHA256
    assert sha256(lean.encode()).hexdigest() == LEAN_SHA256

    source_exclusive = body_after(
        upstream,
        "fn join_thread_exclusive(",
        "fn active_thread(",
    )
    source_join = body_after(
        upstream,
        "fn join_thread(\n",
        "fn join_thread_exclusive(",
    )
    source_checks = [
        "join_status == ThreadJoinStatus::Joined",
        "joined_thread_id == this.machine.threads.active_thread",
        "BlockReason::Join(joined_thread_id)",
        "this.join_thread(joined_thread_id",
    ]
    assert [source_exclusive.index(token) for token in source_checks] == sorted(
        source_exclusive.index(token) for token in source_checks
    )
    detached = source_join.index("join_status == ThreadJoinStatus::Detached")
    marked = source_join.index("join_status = ThreadJoinStatus::Joined")
    sync = source_join.index("handle_thread_join(thread_mgr.active_thread")
    assert detached < marked < sync
    assert detached < source_join.index("after_join(this, joined_thread_id")

    lean_join = body_after(lean, "def joinExclusive ", "def takeJoin ")
    lean_checks = [
        "thread.joinStatus == .Joined",
        "joined == manager.activeThread",
        "thread.isBlockedOn (.Join joined)",
        "thread.joinStatus == .Detached",
        "ThreadStacks.installManager",
    ]
    assert [lean_join.index(token) for token in lean_checks] == sorted(
        lean_join.index(token) for token in lean_checks
    )
    detached = lean_join.index("thread.joinStatus == .Detached")
    assert detached < lean_join.index("afterJoin h choice joined value dest")
    assert detached < lean_join.index("ThreadStacks.installManager")


if __name__ == "__main__":
    test_detached_join_fails_before_join_state_or_sync_effects()
    print("detached join source-order checks passed")
