import empty_function.CanonicalResolution
import empty_function.WildcardCandidateExact
namespace EmptyFunction.CanonicalResolutionUniform
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- One initial pure lookup chooses the same actual answer at every entry
prefix that has only reserved a tag or pushed/cached frames. In particular no
condition is imposed on the new global tracker passed to a small retag leaf. -/
theorem resolve (s : Static) (metadata : Metadata s) (p : Packet)
    (input : InputDraft.CurrentInputDraft s p)
    (pointer : Pointer (Option Provenance)) (effective : InputDraft.effectivePointer p = some pointer) :
    ∃ answer,
      (∀ current : State, current.machine.memory = p.before.machine.memory →
        current.machine.user.addresses = p.before.machine.user.addresses →
        s.cfg.retag.resolveAllocation pointer current = .ok answer current) ∧
      CanonicalResolution.Hit s p answer := by
  have positive := InitializationPrefix.capacity_positive s
  obtain ⟨binding,_ensure,_synchronize⟩ := ConcreteProtection.bindings s metadata positive
  cases input.effective pointer effective with
  | integer encoding =>
    refine ⟨none,?_,trivial⟩
    intro current _ _
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
    intro current _ addresses
    rw [binding,ptr]
    apply UnitProtection.resolve_concrete _ id tag _ base (ConcreteProtection.source_truncate s metadata.pointerSize)
    change current.machine.user.addresses.baseAddr.find? _ = _
    rw [addresses]
    exact cached
  | wildcard encoding mode tables selected =>
    obtain ⟨answer,allocated,classification⟩ := WildcardResolution.allocation p.before pointer tables mode
    cases answer with
    | none =>
      have raw : p.before.machine.user.addresses.ptrGetAlloc
          (Pointer.new Provenance.wildcard pointer.offset) 0 (WildcardResolution.lookup p.before)
          (ConcreteProtection.source s).pointers.arithmetic = .ok none := by
        simp [GlobalAddressState.ptrGetAlloc,Pointer.new,allocated,pure,Except.pure,bind,Except.bind]
      refine ⟨none,?_,trivial⟩
      intro current memory addresses
      rw [binding]
      dsimp only [WildcardResolution.lookup] at raw
      simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,encoding,raw,
        memory,addresses,get,getThe,MonadStateOf.get,EStateM.get,
        pure,EStateM.pure,bind,EStateM.bind,set,EStateM.set,Id.run]
    | some id =>
      obtain ⟨row,member,same,exposed,geometry⟩ := classification
      subst id
      refine ⟨some ⟨row.allocId,Size.ofBytes (pointer.offset.bytes-row.address),.wildcard⟩,?_,
        .wildcard pointer row effective encoding member rfl exposed geometry,
        selected row member exposed geometry⟩
      intro current memory addresses
      exact WildcardCandidateExact.resolve s metadata positive p.before current memory addresses pointer
        encoding row member tables mode exposed geometry

end EmptyFunction.CanonicalResolutionUniform
