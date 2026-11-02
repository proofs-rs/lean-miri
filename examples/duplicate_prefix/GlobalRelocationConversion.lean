import duplicate_prefix.GlobalRelocationRootPointer
import duplicate_prefix.GlobalAllocationAttributes
import duplicate_prefix.PhysicalScalarReturn

/-! One real relocation, with its target described by cached compiler-global
metadata. The output bytes are the encoded target address, and the output
provenance retains the concrete relocation. Only allocation attributes are
shared with empty-reference clients; byte equality and empty provenance are
intentionally absent from Attributes. -/
namespace DuplicatePrefix.GlobalRelocationConversion
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev Attributes (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) : Prop :=
  GlobalAllocationAttributes.Attributes source converted

open Lean Elab in
elab "relocation_read" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".Miri.Memory.readTargetUInt" then some name else none
  let [name] := names | throwError "expected original target integer read"
  Lean.Meta.mkConstWithFreshMVarLevels name

theorem zero_word (layout : TargetDataLayout) :
    relocation_read layout #[0,0,0,0,0,0,0,0] = .ok (0 : U128) := by
  unfold_global_data ".Miri.Memory.readTargetUInt"
  simp [bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Id.run,List.range'_succ,List.forIn_cons,List.forIn_nil]

theorem singleton_zero {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (base : UInt64) (root : BorTag)
    (targetSource source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,targetSource.byteSize,targetSource.align,targetSource.mutability,some (.memory targetSource)⟩)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? provenance.allocId = some root)
    (addressCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
      some ⟨provenance.allocId,base⟩)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (rawBytes : AllocationCopy.snapshot source = #[0,0,0,0,0,0,0,0])
    (relocation : source.provenanceMap.ptrs = #[(Size.ZERO,provenance)])
    (noFragments : source.provenanceMap.byteFragments = none) :
    ∃ converted : Allocation Provenance Unit, ∃ encoded : Array UInt8,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
        (PointerSource.globalRootPointer choices hooks externStatic) before = .ok converted before ∧
      Attributes source converted ∧
      target_bytes layout (Size.ofBytes 8) (BitVec.ofNat 128 base.toNat) = .ok encoded ∧
      encoded.size = 8 ∧ AllocationCopy.snapshot converted = encoded ∧
      converted.provenanceMap.ptrs = #[(Size.ZERO,Provenance.concrete provenance.allocId root)] ∧
      converted.provenanceMap.byteFragments = none := by
  have pointer := GlobalRelocationRootPointer.cached choices hooks externStatic before tracker provenance 0 base root
    targetSource descriptor enabled rootCached addressCached arithmetic
  simp only [UInt64.add_zero] at pointer
  obtain ⟨encoded,encoding,encodedSize⟩ := PhysicalScalarReturn.target_word_exists layout (BitVec.ofNat 128 base.toNat)
  have provenanceResult : ∃ result : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs #[(Size.ZERO,Provenance.concrete provenance.allocId root)] = .ok result ∧
      result.ptrs = #[(Size.ZERO,Provenance.concrete provenance.allocId root)] ∧ result.byteFragments = none := by
    simp only [ProvenanceMap.fromPresortedPtrs]
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    simp
  obtain ⟨resultProvenance,provenanceResult,provenancePtrs,provenanceFragments⟩ := provenanceResult
  cases source
  rename_i raw size map mask align mutability extra native
  cases map
  rename_i ptrs fragments
  change ptrs = _ at relocation
  change fragments = none at noFragments
  subst ptrs
  subst fragments
  have rawEq : raw = #[0,0,0,0,0,0,0,0] := by
    simpa [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
      pure,Pure.pure,Except.pure,Except.toOption] using rawBytes
  subst raw
  simp only [Allocation.adjustFromTcx,AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size,ProvenanceMap.ptrs,ProvenanceMap.byteFragments]
  unfold_global_data ".Miri.Memory.pointerSize"
  simp only [Pointer.new,Size.ofBytes] at pointer
  simp only [Size.ofBytes] at encoding
  simp only [Size.ZERO] at provenanceResult provenancePtrs
  simp [width,Size.fromBits,PointerWidth.bits,Except.toOption,Pointer.new,zero_word,pointer,encoding,provenanceResult,provenancePtrs,provenanceFragments,encodedSize,Size.ZERO,Size.ofBytes,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Id.run,List.forIn_cons,List.forIn_nil]
  refine ⟨?_,provenancePtrs,provenanceFragments⟩
  constructor <;> first | rfl | exact encodedSize
end DuplicatePrefix.GlobalRelocationConversion

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GlobalRelocationConversion.zero_word,
      ``DuplicatePrefix.GlobalRelocationConversion.singleton_zero] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved real global relocation conversion dependency {dependency}"
