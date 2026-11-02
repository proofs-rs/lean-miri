import empty_function.CanonicalLatentProtect
import empty_function.WildcardCanonical
namespace EmptyFunction.CanonicalLatentPreflight
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- Classification of this ordinary latent family, using initial metadata.
It is a subset for a family theorem; it does not replace CurrentInputDraft. -/
def Ordinary (_s : Static) (p : Packet) : Prop :=
  ∀ id, ChoiceAdmission.SelectedId p id → ∃ source : Allocation CtfeProvenance Unit,
    p.before.machine.memory.live.find? (fun row => row.1 == id) = none ∧
    p.before.machine.memory.hasFunctionPointer id = false ∧
    p.before.machine.memory.hasVaListId id = false ∧
    p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩ ∧
    ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩

def Hit (p : Packet) (tracker : MachineHooks.BorrowState) :
    Option RetagPipeline.ResolvedLocation → Prop
  | none => True
  | some result => ChoiceAdmission.SelectedId p result.allocId ∧
      (result.parentProvenance = .wildcard ∨ ∃ tag, result.parentProvenance = .concrete tag ∧ tracker.global.rootTag? result.allocId = some tag)

/-- Actual canonical preflight is derived from the raw original pointer even
at a newly pushed/reserved-tag prefix. No operation success is an input law. -/
theorem resolve (s : Static) (metadata : Metadata s) (positive : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) (ordinary : Ordinary s p)
    (current : State) (memory : current.machine.memory = p.before.machine.memory)
    (addresses : current.machine.user.addresses = p.before.machine.user.addresses) :
    ∃ answer, s.cfg.retag.resolveAllocation destination.place.mplace.ptr current = .ok answer current ∧
      Hit p input.tracker answer := by
  have effective : InputDraft.effectivePointer p = some destination.place.mplace.ptr := by
    simp [InputDraft.effectivePointer,destination.encoding]
  obtain ⟨binding,_ensure,_synchronize⟩ := ConcreteProtection.bindings s metadata positive
  cases destination.pointer with
  | integer encoding =>
    refine ⟨none,?_,trivial⟩
    rw [binding]
    exact UnitProtection.resolve_integer _ _ encoding current
  | concrete id tag base tables encoding cached backing parent latentRoot =>
    have selected := ChoiceAdmission.SelectedId.concrete destination.place.mplace.ptr tag effective encoding
    obtain ⟨source,absent,noFunction,noVaList,descriptor,targets⟩ := ordinary id selected
    have ptr : destination.place.mplace.ptr = Pointer.new (some (.concrete id tag))
        (Size.ofBytes destination.place.mplace.ptr.offset.bytes) := by
      cases ptrEq : destination.place.mplace.ptr with
      | mk offset provenance =>
        simp_all [Pointer.new]
        cases offset
        rfl
    refine ⟨some ⟨id,Size.ofBytes (destination.place.mplace.ptr.offset.bytes-base),.concrete tag⟩,?_,selected,Or.inr ⟨tag,rfl,?_⟩⟩
    · rw [binding,ptr]
      apply UnitProtection.resolve_concrete _ id tag _ base (ConcreteProtection.source_truncate s metadata.pointerSize)
      change current.machine.user.addresses.baseAddr.find? _ = _
      rw [addresses]
      exact cached
    · exact latentRoot absent _ descriptor (Or.inl rfl)
  | wildcard encoding mode tables selected =>
    obtain ⟨answer,resolved,_typed,hits⟩ := WildcardCanonical.resolve s metadata positive p.before current memory addresses
      input.tracker destination.place.mplace.ptr destination.pointer encoding
    refine ⟨answer,resolved,?_⟩
    cases answer with
    | none => trivial
    | some result =>
      obtain ⟨row,member,equal,exposed,geometry,_backing⟩ := hits
      subst result
      exact ⟨ChoiceAdmission.SelectedId.wildcard destination.place.mplace.ptr row effective encoding member rfl exposed geometry,Or.inl rfl⟩
end EmptyFunction.CanonicalLatentPreflight
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.CanonicalLatentPreflight." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent preflight axiom {dependency} in {name}"
