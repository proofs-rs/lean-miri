import Lean
import Miri.Interpreter.GlobalMemoryCopyMachine

/-! Straight-line composition of the original copy driver. The effect
equations in this internal lemma must be discharged by the canonical machine
bridges; they are not a client safety contract or a replacement interpreter. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.CopyComposition
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter

open Lean Elab in
private def original (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected one original copy helper {suffix}"

open Lean Elab in
elab "composition_memory_hook" : term =>
  return mkConst (← original ".GlobalMemoryCopyMachine.memoryHook")

open Lean Elab in
elab "composition_raw" : term =>
  return mkConst (← original ".GlobalMemoryCopyMachine.raw")

open Lean Elab in
elab "composition_access" : term =>
  return mkConst (← original ".GlobalMemoryCopyMachine.access")

open Lean Elab in
elab "composition_snapshot" : term =>
  return mkConst (← original ".GlobalMemoryCopyMachine.snapshotChecks")

theorem generic_copy_success {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (source dest : Pointer (Option Provenance)) (size destSize : Size)
    (repeatCount : UInt64) (nonoverlapping : Bool)
    (srcId dstId : AllocId) (srcOffset dstOffset : Size)
    (srcProv dstProv : ProvenanceExtra)
    (srcAlloc readAlloc dstAlloc writeAlloc resultAlloc : Allocation Provenance BorrowTree)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : MachineHooks.State K U)
    (finalMemory : MemoryState Provenance BorrowTree K)
    (sourceCheck : composition_memory_hook (fun state =>
      (MemoryCopyMachine.genericHooks config addresses arithmetic).pointerAccess
        state.machine.memory state source size) s0 =
      .ok (some (srcId, srcOffset, srcProv)) s1)
    (multiply : Size.mul size repeatCount = .ok destSize)
    (destinationCheck : composition_memory_hook (fun state =>
      (MemoryCopyMachine.genericHooks config addresses arithmetic).pointerAccess
        state.machine.memory state dest destSize) s1 =
      .ok (some (dstId, dstOffset, dstProv)) s2)
    (probeId : (MemoryCopyMachine.genericHooks config addresses arithmetic).tryGetAllocId
      s2.machine.memory ⟨s2.machine, none⟩ source size.bytes = some srcId)
    (probe : composition_memory_hook (fun state =>
      (MemoryCopyMachine.genericHooks config addresses arithmetic).beforeAllocationAccess
        state.machine.memory state srcId) s2 = .ok () s3)
    (sourceRaw : composition_raw config false srcId s3 = .ok srcAlloc s4)
    (notGhost : config.ghostMode = false)
    (readAccess : composition_access config false srcAlloc srcId srcProv
      (allocRange srcOffset size) s4 = .ok readAlloc s5)
    (snapshot : composition_snapshot config readAlloc (allocRange srcOffset size)
      arithmetic.pointerSize s5 = .ok () s6)
    (destinationRaw : composition_raw config true dstId s6 = .ok dstAlloc s7)
    (destinationBefore : composition_memory_hook (fun state =>
      (MemoryCopyMachine.genericHooks config addresses arithmetic).beforeAllocationAccess
        state.machine.memory state dstId) s7 = .ok () s8)
    (writeAccess : composition_access config true dstAlloc dstId dstProv
      (allocRange dstOffset destSize) s8 = .ok writeAlloc s9)
    (copy : Allocation.copyRepeatedly readAlloc (allocRange srcOffset size) dstOffset
      repeatCount arithmetic.pointerSize (srcId == dstId) nonoverlapping writeAlloc =
      .ok () resultAlloc)
    (commit : s9.machine.memory.setLiveAllocation dstId resultAlloc = .ok finalMemory) :
    GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest size repeatCount
      nonoverlapping s0 = .ok () {s9 with machine := {s9.machine with memory := finalMemory}} := by
  unfold GlobalMemoryCopyMachine.genericCopy
  simp only [bind, EStateM.bind]
  rw [sourceCheck]
  simp only [multiply, pure, EStateM.pure, EStateM.bind]
  rw [destinationCheck]
  simp only
  simp only [get, getThe, MonadStateOf.get, EStateM.get, probeId, EStateM.bind]
  rw [probe]
  simp only
  rw [sourceRaw]
  simp only
  simp only [notGhost, Bool.false_eq_true, ↓reduceIte, EStateM.bind]
  rw [readAccess]
  simp only
  rw [snapshot]
  simp only
  rw [destinationRaw]
  simp only
  rw [destinationBefore]
  simp only
  rw [writeAccess]
  simp only
  rw [copy]
  simp only [EStateM.get, commit, EStateM.bind]
  rfl

#print axioms generic_copy_success

end DuplicatePrefix.CopyComposition

open Lean Elab Command in
run_cmd do
  let declaration := ``DuplicatePrefix.CopyComposition.generic_copy_success
  for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "{declaration} depends on unapproved axiom {dependency}"
