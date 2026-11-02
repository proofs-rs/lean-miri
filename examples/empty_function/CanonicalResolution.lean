import empty_function.InitializationPrefix
import empty_function.WildcardCanonical
namespace EmptyFunction.CanonicalResolution
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Pure initial backing of the exact selected effective pointer. -/
def Hit (s : Static) (p : Packet) : Option RetagPipeline.ResolvedLocation → Prop
  | none => True
  | some result => ChoiceAdmission.SelectedId p result.allocId ∧ InputDraft.Backing s p.before result.allocId

/-- Resolution is unchanged by entry tag reservation and raw frame push. Its
lookup facts concern the original caller; no future allocation/root success or
choice/resource condition is assumed. This applies equally to memory and local
return representations, including inclusive projected endpoints. -/
theorem resolve (s : Static) (metadata : Metadata s) (p : Packet)
    (input : InputDraft.CurrentInputDraft s p)
    (pointer : Pointer (Option Provenance)) (effective : InputDraft.effectivePointer p = some pointer)
    (current : State) (memory : current.machine.memory = p.before.machine.memory)
    (addresses : current.machine.user.addresses = p.before.machine.user.addresses) :
    ∃ answer, s.cfg.retag.resolveAllocation pointer current = .ok answer current ∧ Hit s p answer := by
  have positive := InitializationPrefix.capacity_positive s
  have supplied := input.effective pointer effective
  obtain ⟨binding,_ensure,_synchronize⟩ := ConcreteProtection.bindings s metadata positive
  cases supplied with
  | integer encoding =>
    refine ⟨none,?_,trivial⟩
    rw [binding]
    exact UnitProtection.resolve_integer _ _ encoding current
  | concrete id tag base tables encoding cached backing parent latentRoot =>
    have selected : ChoiceAdmission.SelectedId p id := .concrete pointer tag effective encoding
    have ptr : pointer = Pointer.new (some (.concrete id tag)) (Size.ofBytes pointer.offset.bytes) := by
      cases pointerEq : pointer with
      | mk offset provenance =>
        simp_all [Pointer.new]
        cases offset
        rfl
    refine ⟨some ⟨id,Size.ofBytes (pointer.offset.bytes-base),.concrete tag⟩,?_,selected,backing⟩
    rw [binding,ptr]
    apply UnitProtection.resolve_concrete _ id tag _ base (ConcreteProtection.source_truncate s metadata.pointerSize)
    change current.machine.user.addresses.baseAddr.find? _ = _
    rw [addresses]
    exact cached
  | wildcard encoding mode tables selected =>
    obtain ⟨answer,resolved,_typed,hits⟩ := WildcardCanonical.resolve s metadata positive p.before current memory addresses
      input.tracker pointer (input.effective pointer effective) encoding
    refine ⟨answer,resolved,?_⟩
    cases answer with
    | none => trivial
    | some result =>
      obtain ⟨row,member,equal,exposed,geometry,backing⟩ := hits
      subst result
      exact ⟨.wildcard pointer row effective encoding member rfl exposed geometry,backing⟩

end EmptyFunction.CanonicalResolution
