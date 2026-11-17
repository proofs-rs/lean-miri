import duplicate_prefix.AllocationCopy
import Miri.Interpreter.GlobalAllocationMachine

/-! Data-only compiler images use the real adjust_from_tcx byte/provenance
conversion. Mutability and initialization are retained, including readonly and
uninitialized bytes. No relocation callback is invoked for an empty provenance
map. -/
namespace DuplicatePrefix.GlobalDataOnlyConversion
open Lean Elab Tactic in
elab "unfold_global_data " suffix:str : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := found | throwError "expected one source definition {suffix.getString}"
  evalTactic (← `(tactic| unfold $(mkIdent name)))

open Miri.ABI Miri.Memory Miri.Interpreter
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

set_option autoImplicit false in
structure Facts (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) : Prop where
  bytes : AllocationCopy.snapshot converted = AllocationCopy.snapshot source
  size : converted.byteSize = source.byteSize
  storage : converted.len = source.len
  mask : converted.initializationMask = source.initializationMask
  provenance : converted.provenanceMap = ProvenanceMap.new
  align : converted.align = source.align
  mutability : converted.mutability = source.mutability
  native : converted.nativeBuffer = none

theorem adjust_exists {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (target : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (state : State) (empty : source.provenanceMap = ProvenanceMap.new) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source target
        (fun _ _ current => .ok (AllocationCopy.snapshot source) current)
        pointer state = .ok converted state ∧ Facts source converted := by
  have emptyMap : ProvenanceMap.fromPresortedPtrs (#[] : Array (Size × Provenance)) = .ok ProvenanceMap.new := by
    simp only [ProvenanceMap.fromPresortedPtrs]
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    rfl
  cases source
  rename_i raw size provenance mask align mutability extra native
  change provenance = ProvenanceMap.new at empty
  subst provenance
  simp [AllocationCopy.snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len, Allocation.adjustFromTcx, ProvenanceMap.new,
    emptyMap, List.forIn_nil,
    bind, Bind.bind, pure, Pure.pure, Except.pure, Id.run, Except.toOption]
  constructor <;> rfl

end DuplicatePrefix.GlobalDataOnlyConversion

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GlobalDataOnlyConversion.adjust_exists) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved data-only global conversion dependency {dependency}"
