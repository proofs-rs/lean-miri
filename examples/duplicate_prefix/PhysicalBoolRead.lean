import duplicate_prefix.PhysicalScalarReturn
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.PhysicalBoolRead
open Miri.ABI Miri.Memory Miri.Interpreter
open Lean Elab
private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique bool scalar helper {suffix}"
elab "read_target" : term => return mkConst (← sourceName ".Miri.Memory.readTargetUInt")

theorem bool_encode (layout : TargetDataLayout) (value : Bool) :
    target_bytes layout (Size.ofBytes 1) (if value then 1 else 0) =
      Except.ok #[if value then 1 else 0] := by
  cases value <;> unfold_internal ".Miri.Memory.targetUIntBytes" <;>
    simp [Size.ofBytes, bind, Except.bind, pure, Except.pure, Id.run, List.range'_succ,
      List.forIn_cons, List.forIn_nil]

theorem bool_decode (layout : TargetDataLayout) (value : Bool) :
    read_target layout #[if value then 1 else 0] = .ok (if value then 1 else 0) := by
  cases value <;> unfold_internal ".Miri.Memory.readTargetUInt" <;>
    simp [bind, Except.bind, pure, Except.pure, Id.run, List.range'_succ,
      List.forIn_cons, List.forIn_nil]

theorem read_bool {Extra : Type} (allocation : Allocation Provenance Extra)
    (layout : TargetDataLayout) (value : Bool)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (size : allocation.byteSize = Size.ofBytes 1)
    (mask : allocation.initializationMask = InitMask.new (Size.ofBytes 1) true)
    (snapshot : AllocationCopy.snapshot allocation = #[if value then 1 else 0]) :
    Allocation.readScalar allocation layout (allocRange Size.ZERO (Size.ofBytes 1)) false =
      .ok (Scalar.fromBool value) := by
  have slice := AllocationCopy.full_bytes_ok allocation storage
  unfold Allocation.getBytesUnchecked at slice
  rw [size,snapshot] at slice
  have initialized : allocation.initializationMask.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 1)) =
      .ok (.ok ()) := by
    rw [mask]
    simp [InitMask.isRangeInitialized, InitMask.new, allocRange, AllocRange.endExclusive, AllocRange.end,
      Size.add, Size.ZERO, Size.ofBytes, Except.mapError, bind, Except.bind, pure, Except.pure]
  unfold Allocation.readScalar
  erw [initialized]
  simp only [Except.mapError, bind, Except.bind, pure, Except.pure]
  erw [slice]
  simp only [bind, Except.bind]
  rw [bool_decode]
  cases value <;> rfl

theorem written_snapshot {Extra : Type} (allocation : Allocation Provenance Extra)
    (layout : TargetDataLayout) (value : Bool)
    (size : allocation.byteSize = Size.ofBytes 1)
    (encoding : target_bytes layout allocation.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot allocation)) :
    AllocationCopy.snapshot allocation = #[if value then 1 else 0] := by
  rw [size,bool_encode] at encoding
  exact (Except.ok.inj encoding).symm

theorem read_written_bool {Extra : Type} (allocation : Allocation Provenance Extra)
    (layout : TargetDataLayout) (value : Bool)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (size : allocation.byteSize = Size.ofBytes 1)
    (mask : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (encoding : target_bytes layout allocation.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot allocation)) :
    Allocation.readScalar allocation layout (allocRange Size.ZERO (Size.ofBytes 1)) false =
      .ok (Scalar.fromBool value) := by
  apply read_bool allocation layout value storage size
  · simpa only [size] using mask
  · exact written_snapshot allocation layout value size encoding

#print axioms read_written_bool

#print axioms read_bool

#print axioms bool_encode
#print axioms bool_decode
end DuplicatePrefix.PhysicalBoolRead

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalBoolRead.bool_encode,
      ``DuplicatePrefix.PhysicalBoolRead.bool_decode, ``DuplicatePrefix.PhysicalBoolRead.read_bool,
      ``DuplicatePrefix.PhysicalBoolRead.written_snapshot, ``DuplicatePrefix.PhysicalBoolRead.read_written_bool] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical bool read dependency {dependency}"
