#!/usr/bin/env python3
"""Extract the pinned Miri vector-clock methods into the standalone Rust shim."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_BLOB = "723dfd29651525198b7590553f1ef5e72b952eba"
EXPECTED_DATA_RACE_BLOB = "acf45c84bcc6d0f491ef5306ef6662390b96d11a"

VECTOR_ONLY_NA_READ_TYPE = """#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NaReadType {
    Read,
    Retag,
}
"""

DATA_RACE_TESTS = "    reference::emit_data_race_cases();"

DATA_RACE_HELPERS = r"""
fn result_code(result: Result<(), DataRace>) -> &'static str {
    if result.is_ok() { "ok" } else { "race" }
}

fn timestamp_type_code(timestamp: &VTimestamp) -> &'static str {
    match timestamp.read_type() {
        NaReadType::Read => "read",
        NaReadType::Retag => "retag",
    }
}

fn raw_clock_at(clock: &VClock, index: VectorIdx) -> String {
    clock[index].time_and_read_type.to_string()
}

fn atomic_size_code(cell: &MemoryCellClocks) -> String {
    match cell.atomic() {
        None => "none".to_owned(),
        Some(atomic) => match atomic.size {
            None => "mixed-reads".to_owned(),
            Some(size) => size.to_string(),
        },
    }
}

fn write_type_code(write_type: NaWriteType) -> &'static str {
    match write_type {
        NaWriteType::Allocate => "allocate",
        NaWriteType::Write => "write",
        NaWriteType::Retag => "retag",
        NaWriteType::Deallocate => "deallocate",
    }
}

pub(super) fn emit_data_race_cases() {
    for ordering in [
        AtomicOrdering::Relaxed,
        AtomicOrdering::Acquire,
        AtomicOrdering::Release,
        AtomicOrdering::AcqRel,
        AtomicOrdering::SeqCst,
    ] {
        let rw = AtomicRwOrd::from(ordering);
        let rw_code = match rw {
            AtomicRwOrd::Relaxed => "relaxed",
            AtomicRwOrd::Acquire => "acquire",
            AtomicRwOrd::Release => "release",
            AtomicRwOrd::AcqRel => "acqrel",
            AtomicRwOrd::SeqCst => "seqcst",
        };
        let read = std::panic::catch_unwind(|| AtomicReadOrd::from(ordering));
        let read_code = match read {
            Ok(AtomicReadOrd::Relaxed) => "relaxed",
            Ok(AtomicReadOrd::Acquire) => "acquire",
            Ok(AtomicReadOrd::SeqCst) => "seqcst",
            Err(_) => "invalid",
        };
        let write = std::panic::catch_unwind(|| AtomicWriteOrd::from(ordering));
        let write_code = match write {
            Ok(AtomicWriteOrd::Relaxed) => "relaxed",
            Ok(AtomicWriteOrd::Release) => "release",
            Ok(AtomicWriteOrd::SeqCst) => "seqcst",
            Err(_) => "invalid",
        };
        let fence = std::panic::catch_unwind(|| AtomicFenceOrd::from(ordering));
        let fence_code = match fence {
            Ok(AtomicFenceOrd::Acquire) => "acquire",
            Ok(AtomicFenceOrd::Release) => "release",
            Ok(AtomicFenceOrd::AcqRel) => "acqrel",
            Ok(AtomicFenceOrd::SeqCst) => "seqcst",
            Err(_) => "invalid",
        };
        println!("ordering:{rw_code}:{read_code}:{write_code}:{fence_code}");
    }

    let i0 = VectorIdx::from(0);
    let i1 = VectorIdx::from(1);
    let i2 = VectorIdx::from(2);
    let zero = VTimestamp::ZERO;
    let t1 = VTimestamp::new(1, NaReadType::Read, DUMMY_SP);
    let t2 = VTimestamp::new(2, NaReadType::Read, DUMMY_SP);
    let t3 = VTimestamp::new(3, NaReadType::Read, DUMMY_SP);

    let mut released = ThreadClockSet::default();
    released.clock = VClock::new_with_index(i0, t1);
    released.apply_release_fence();
    println!("fence:release:{}", released.fence_release[i0].time_and_read_type);
    let mut acquired = ThreadClockSet::default();
    acquired.clock = VClock::new_with_index(i0, t1);
    acquired.fence_acquire = VClock::new_with_index(i0, t2);
    acquired.apply_acquire_fence();
    println!("fence:acquire:{}", acquired.clock[i0].time_and_read_type);

    let mut retag_cell = MemoryCellClocks::new(t2, i0);
    let mut older = ThreadClockSet::default();
    older.clock = VClock::new_with_index(i0, t1);
    let retag_result = retag_cell.non_atomic_read_detect(&mut older, i0, NaReadType::Retag, DUMMY_SP);
    println!("cell:retag-race:{}:{}:{}", result_code(retag_result), older.clock[i0].time_and_read_type, timestamp_type_code(&older.clock[i0]));

    let mut read_cell = MemoryCellClocks::new(t1, i0);
    let mut later = ThreadClockSet::default();
    later.clock = VClock::new_with_index(i0, t3);
    let read_result = read_cell.non_atomic_read_detect(&mut later, i0, NaReadType::Read, DUMMY_SP);
    println!("cell:non-atomic-read:{}:{}", result_code(read_result), read_cell.read[i0].time_and_read_type);

    let mut atomic_cell = MemoryCellClocks::new(zero, i0);
    let mut atomic_thread = ThreadClockSet::default();
    atomic_thread.clock = VClock::new_with_index(i1, t1);
    let atomic_result = atomic_cell.atomic_read_detect(&atomic_thread, i1, 4);
    let atomic_read = match atomic_cell.atomic() {
        Some(atomic) => raw_clock_at(&atomic.read_vector, i1),
        None => "missing-atomic-state".to_owned(),
    };
    println!("cell:atomic-read:{}:{}:{}", result_code(atomic_result), atomic_size_code(&atomic_cell), atomic_read);

    let mut unordered_mixed_write_cell = atomic_cell.clone();
    let mut unordered_mixed_write_thread = ThreadClockSet::default();
    unordered_mixed_write_thread.clock = VClock::new_with_index(i0, t1);
    let unordered_mixed_write_result = unordered_mixed_write_cell.atomic_write_detect(&unordered_mixed_write_thread, i0, 16);
    println!("cell:mixed-size-write-race:{}:{}", result_code(unordered_mixed_write_result), atomic_size_code(&unordered_mixed_write_cell));

    let mut ordered_mixed_write_cell = atomic_cell.clone();
    let mut ordered_mixed_write_thread = ThreadClockSet::default();
    ordered_mixed_write_thread.clock = VClock::new_with_index(i1, t2);
    let ordered_mixed_write_result = ordered_mixed_write_cell.atomic_write_detect(&ordered_mixed_write_thread, i1, 8);
    let size_change_clock = match ordered_mixed_write_cell.atomic() {
        Some(atomic) => raw_clock_at(&atomic.write_vector, i1),
        None => "missing-atomic-state".to_owned(),
    };
    println!("cell:ordered-size-change:{}:{}:{}", result_code(ordered_mixed_write_result), atomic_size_code(&ordered_mixed_write_cell), size_change_clock);

    let mut different_size_thread = ThreadClockSet::default();
    different_size_thread.clock = VClock::new_with_index(i0, t1);
    let different_size_result = atomic_cell.atomic_read_detect(&different_size_thread, i0, 8);
    println!("cell:mixed-size-reads:{}:{}", result_code(different_size_result), atomic_size_code(&atomic_cell));

    let mut racing_atomic_cell = read_cell.clone();
    let mut racing_atomic_thread = ThreadClockSet::default();
    racing_atomic_thread.clock = VClock::new_with_index(i2, t1);
    let atomic_write_result = racing_atomic_cell.atomic_write_detect(&racing_atomic_thread, i2, 4);
    let write_vector_time = match racing_atomic_cell.atomic() {
        Some(atomic) => raw_clock_at(&atomic.write_vector, i2),
        None => "missing-atomic-state".to_owned(),
    };
    println!("cell:atomic-write-race:{}:{}", result_code(atomic_write_result), write_vector_time);

    let mut clean_write_cell = MemoryCellClocks::new(zero, i0);
    let mut clean_write_thread = ThreadClockSet::default();
    clean_write_thread.clock = VClock::new_with_index(i0, t1);
    let clean_write_result = clean_write_cell.non_atomic_write_detect(&mut clean_write_thread, i0, NaWriteType::Retag, DUMMY_SP);
    println!("cell:non-atomic-write:{}:{}:{}:{}", result_code(clean_write_result), write_type_code(clean_write_cell.write_type), clean_write_cell.read[i0].time_and_read_type, atomic_size_code(&clean_write_cell));

    let mut published = MemoryCellClocks::new(zero, i0);
    let mut publisher = ThreadClockSet::default();
    publisher.clock = VClock::new_with_index(i0, t1);
    let release_store_result = published.store_release(&publisher, i0, 4);
    let published_raw = match published.atomic() {
        Some(atomic) => raw_clock_at(&atomic.sync_vector, i0),
        None => "missing-atomic-state".to_owned(),
    };
    println!("cell:store-release:{}:{}", result_code(release_store_result), published_raw);

    let mut acquire_thread = ThreadClockSet::default();
    acquire_thread.clock = VClock::new_with_index(i1, t1);
    let acquire_result = published.load_acquire(&mut acquire_thread, i1, 4, None);
    println!("cell:load-acquire:{}:{}", result_code(acquire_result), acquire_thread.clock[i0].time_and_read_type);

    let mut relaxed_thread = ThreadClockSet::default();
    relaxed_thread.clock = VClock::new_with_index(i1, t1);
    let relaxed_result = published.load_relaxed(&mut relaxed_thread, i1, 4, None);
    println!("cell:load-relaxed:{}:{}", result_code(relaxed_result), relaxed_thread.fence_acquire[i0].time_and_read_type);

    let mut relaxed_store_cell = published.clone();
    let mut release_fence_thread = ThreadClockSet::default();
    release_fence_thread.clock = VClock::new_with_index(i1, t1);
    release_fence_thread.fence_release = VClock::new_with_index(i2, t2);
    let relaxed_store_result = relaxed_store_cell.store_relaxed(&release_fence_thread, i1, 4);
    let relaxed_sync = match relaxed_store_cell.atomic() {
        Some(atomic) => format!("{}:{}", raw_clock_at(&atomic.sync_vector, i0), raw_clock_at(&atomic.sync_vector, i2)),
        None => "missing-atomic-state:missing-atomic-state".to_owned(),
    };
    println!("cell:store-relaxed:{}:{}", result_code(relaxed_store_result), relaxed_sync);

    let mut rmw_release_cell = published.clone();
    let mut rmw_thread = ThreadClockSet::default();
    rmw_thread.clock = VClock::new_with_index(i2, t2);
    let rmw_release_result = rmw_release_cell.rmw_release(&rmw_thread, i2, 4);
    let rmw_release_sync = match rmw_release_cell.atomic() {
        Some(atomic) => format!("{}:{}", raw_clock_at(&atomic.sync_vector, i0), raw_clock_at(&atomic.sync_vector, i2)),
        None => "missing-atomic-state:missing-atomic-state".to_owned(),
    };
    println!("cell:rmw-release:{}:{}", result_code(rmw_release_result), rmw_release_sync);

    let mut rmw_relaxed_cell = published.clone();
    let mut rmw_relaxed_thread = ThreadClockSet::default();
    rmw_relaxed_thread.clock = VClock::new_with_index(i2, t1);
    rmw_relaxed_thread.fence_release = VClock::new_with_index(i2, t2);
    let rmw_relaxed_result = rmw_relaxed_cell.rmw_relaxed(&rmw_relaxed_thread, i2, 4);
    let rmw_relaxed_sync = match rmw_relaxed_cell.atomic() {
        Some(atomic) => format!("{}:{}", raw_clock_at(&atomic.sync_vector, i0), raw_clock_at(&atomic.sync_vector, i2)),
        None => "missing-atomic-state:missing-atomic-state".to_owned(),
    };
    println!("cell:rmw-relaxed:{}:{}", result_code(rmw_relaxed_result), rmw_relaxed_sync);

    let mut bytes = [MemoryCellClocks::new(zero, i0), MemoryCellClocks::new(zero, i0)];
    let mut range_thread = ThreadClockSet::default();
    range_thread.clock = VClock::new_with_index(i0, t1);
    for byte in &mut bytes {
        let result = byte.non_atomic_read_detect(&mut range_thread, i0, NaReadType::Retag, DUMMY_SP);
        assert!(result.is_ok());
    }
    println!("alloc:two-byte-retag:ok:{}:{}", timestamp_type_code(&bytes[0].read[i0]), timestamp_type_code(&bytes[1].read[i0]));

    let mut atomic_bytes = vec![MemoryCellClocks::new(zero, i0); 4];
    let mut publisher = ThreadClockSet::default();
    publisher.clock = VClock::new_with_index(i0, t1);
    let mut store_ok = true;
    for byte in &mut atomic_bytes {
        store_ok &= byte.store_release(&publisher, i0, 4).is_ok();
    }
    let mut reader = ThreadClockSet::default();
    reader.clock = VClock::new_with_index(i1, t1);
    let mut load_ok = true;
    for byte in &mut atomic_bytes {
        load_ok &= byte.load_acquire(&mut reader, i1, 4, None).is_ok();
    }
    println!("alloc:atomic-range-load:{}:{}:{}", if store_ok && load_ok { "ok" } else { "race" },
        reader.clock[i0].time_and_read_type, reader.clock[i1].time_and_read_type);

    let mut rmw_clock = VClock::new_with_index(i0, t1);
    rmw_clock.set_at_index(&VClock::new_with_index(i1, t1), i1);
    rmw_clock.set_at_index(&VClock::new_with_index(i2, t2), i2);
    let mut rmw_thread = ThreadClockSet::default();
    rmw_thread.clock = rmw_clock;
    let mut rmw_ok = true;
    for byte in &mut atomic_bytes {
        rmw_ok &= byte.load_acquire(&mut rmw_thread, i2, 4, None).is_ok();
        rmw_ok &= byte.rmw_release(&rmw_thread, i2, 4).is_ok();
    }
    println!("alloc:atomic-range-rmw:{}:{}:{}:{}", if rmw_ok { "ok" } else { "race" },
        rmw_thread.clock[i0].time_and_read_type, rmw_thread.clock[i1].time_and_read_type,
        rmw_thread.clock[i2].time_and_read_type);
}
"""


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def section(source: str, start: str, end: str) -> str:
    first = source.index(start)
    last = source.index(end, first)
    return source[first:last].rstrip()


def extract(source_path: Path, template_path: Path, data_race_path: Path | None = None) -> str:
    source_bytes = source_path.read_bytes()
    actual_blob = git_blob_sha1(source_bytes)
    if actual_blob != EXPECTED_BLOB:
        raise ValueError(
            f"pinned vector_clock.rs blob mismatch: expected {EXPECTED_BLOB}, got {actual_blob}"
        )
    source = source_bytes.decode("utf-8")

    vector_idx = section(source, "/// A vector clock index", "/// The size of the vector clock")
    timestamp = section(
        source,
        "/// The time-stamps recorded in the data-race detector",
        "/// A vector clock for detecting data-races",
    )
    clock_and_impl = section(
        source,
        "/// A vector clock for detecting data-races",
        "impl Clone for VClock {",
    )
    clone_impl = section(source, "impl Clone for VClock {", "impl PartialOrd for VClock {")
    partial_ord_impl = section(
        source,
        "impl PartialOrd for VClock {",
        "impl Index<VectorIdx> for VClock {",
    )
    index_impl = section(
        source,
        "impl Index<VectorIdx> for VClock {",
        "/// Test vector clock ordering operations",
    )

    generated = template_path.read_text(encoding="utf-8")
    fragments = {
        "// @VECTOR_IDX@": vector_idx,
        "// @VTIMESTAMP@": timestamp,
        "// @VCLOCK_AND_IMPL@": clock_and_impl,
        "// @CLONE_IMPL@": clone_impl,
        "// @PARTIAL_ORD_IMPL@": partial_ord_impl,
        "// @INDEX_IMPL@": index_impl,
    }
    for marker, fragment in fragments.items():
        if generated.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one {marker} marker")
        generated = generated.replace(marker, fragment)

    race_declarations = VECTOR_ONLY_NA_READ_TYPE
    race_implementations = ""
    race_tests = ""
    if data_race_path is not None:
        race_bytes = data_race_path.read_bytes()
        actual_race_blob = git_blob_sha1(race_bytes)
        if actual_race_blob != EXPECTED_DATA_RACE_BLOB:
            raise ValueError(
                "pinned data_race.rs blob mismatch: expected "
                f"{EXPECTED_DATA_RACE_BLOB}, got {actual_race_blob}"
            )
        race_source = race_bytes.decode("utf-8")
        race_declarations = "\n\n".join((
            section(
                race_source,
                "/// Valid atomic read-write orderings",
                "/// The current set of vector clocks describing",
            ),
            section(
                race_source,
                "/// The current set of vector clocks describing",
                "/// Error returned by finding a data race",
            ),
            section(
                race_source,
                "/// Error returned by finding a data race",
                "/// Extra metadata associated with a thread",
            ),
        ))
        race_implementations = "\n\n".join((
            section(
                race_source,
                "impl AtomicMemoryCellClocks {",
                "impl MemoryCellClocks {",
            ),
            section(
                race_source,
                "impl MemoryCellClocks {",
                "impl GlobalDataRaceHandler {",
            ),
        )) + DATA_RACE_HELPERS
        race_tests = DATA_RACE_TESTS

    for marker, fragment in (
        ("// @DATA_RACE_DECLARATIONS@", race_declarations),
        ("// @DATA_RACE_IMPLEMENTATIONS@", race_implementations),
        ("// @DATA_RACE_TESTS@", race_tests),
    ):
        if generated.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one {marker} marker")
        generated = generated.replace(marker, fragment)

    generated = generated.replace("pub(super)", "pub")
    generated = generated.replace(
        "SmallVec<[VTimestamp; SMALL_VECTOR]>", "Vec<VTimestamp>"
    )
    generated = generated.replace("smallvec::smallvec!", "vec!")
    return generated


def main() -> None:
    if len(sys.argv) not in (4, 5):
        raise SystemExit(
            "usage: extract_reference.py PINNED_VECTOR_CLOCK_RS RUST_TEMPLATE OUTPUT_RS "
            "[PINNED_DATA_RACE_RS]"
        )
    source_path, template_path, output_path = map(Path, sys.argv[1:4])
    data_race_path = Path(sys.argv[4]) if len(sys.argv) == 5 else None
    generated = extract(source_path, template_path, data_race_path)
    output_path.write_text(generated, encoding="utf-8")
    print(f"extracted hash-checked Miri vector-clock methods ({EXPECTED_BLOB})")
    if data_race_path is not None:
        print(f"extracted hash-checked Miri data-race clock methods ({EXPECTED_DATA_RACE_BLOB})")


if __name__ == "__main__":
    main()
