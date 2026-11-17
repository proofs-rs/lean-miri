import duplicate_prefix.CurrentCallSupportChain

/-! Reverse presentation of the existing sufficient candidate resource domain.
The extracted raw chain corresponds to the GIVEN optional interpretation; its
canonical completion need not equal that interpretation outside the chain.
Neither ordinary-input necessity nor family/copy coverage is asserted. -/
namespace DuplicatePrefix.CurrentCallSupportChainExtraction
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath CurrentCallSupportChain
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Functional actual physical parents make every ancestor of a physical
extension either an old ancestor or an actual physical ancestor of its end. -/
theorem physical_split {tree : BorrowTree} {C : Completion}
    (model : ParentInterpretation tree C) {first last query : UniIndex}
    (path : Path tree first last) :
    Below C query last ↔ Below C query first ∨ Path tree query last := by
  constructor
  · intro below
    induction path generalizing query with
    | refl => exact .inl below
    | @step parent child earlier node present edge ih =>
      cases below with
      | refl => exact .inr (.refl _ node present)
      | @step actualParent _ actual prior =>
        have equal : actualParent=parent := Option.some.inj
          (Option.some.inj (actual.symm.trans (model.physical child node present parent edge)))
        subst actualParent
        rcases ih prior with old | physical
        · exact .inl old
        · exact .inr (.step physical node present edge)
  · intro ancestry
    rcases ancestry with old | physical
    · exact CompletedBorrowAncestry.below_trans old (model.physical_below path)
    · exact model.physical_below physical

/-- Frozen append changes exactly the terminal physical segment. -/
theorem append_member {tree : BorrowTree} {grant terminal query : UniIndex}
    (chain : Chain tree grant) (path : Path tree grant terminal) :
    (chain.append path).Member query ↔ chain.Member query ∨ Path tree query terminal := by
  cases chain with
  | root previous =>
    constructor
    · exact fun member=>.inr member
    · intro member
      rcases member with old | current
      · exact CompletedBorrowAncestry.path_trans old path
      · exact current
  | link prior edge =>
    constructor
    · intro member
      rcases member with previous | current
      · exact .inl (.inl previous)
      · exact .inr current
    · intro member
      rcases member with previous | current
      · rcases previous with inherited | oldPath
        · exact .inl inherited
        · exact .inr (CompletedBorrowAncestry.path_trans oldPath path)
      · exact .inr current

/-- Existing issuance extracts one raw chain with EXACT ancestry correspondence
at its terminal under the supplied C. Other C edges are not reconstructed or
asserted equal to the canonical completion of that chain. -/
theorem extract {before tracker id allocation C grant}
    (model : ParentInterpretation allocation.extra C)
    (issued : SpatialDelegation before tracker id allocation C grant) :
    ∃ chain : Chain allocation.extra grant,∀ index,Below C index grant ↔ chain.Member index := by
  induction issued with
  | allocated cap =>
    obtain ⟨node,present,parentless,_,_⟩:=cap.rootNode
    refine ⟨.root (.refl _ node present),?_⟩
    intro index
    constructor
    · intro below
      cases below with
      | refl => exact .refl _ node present
      | step edge prior => rw [model.primaryNone] at edge;cases edge
    · exact model.physical_below
  | @concrete parent child issued path ih =>
    obtain ⟨chain,correspondence⟩:=ih
    refine ⟨chain.append path,?_⟩
    intro index
    constructor
    · intro below
      apply (append_member chain path).mpr
      rcases (physical_split model path).mp below with previous | physical
      · exact .inl ((correspondence index).mp previous)
      · exact .inr physical
    · intro member
      apply (physical_split model path).mpr
      rcases (append_member chain path).mp member with previous | physical
      · exact .inl ((correspondence index).mpr previous)
      · exact .inr physical
  | @wildcard origin root originNode rootNode earlier position originRoot issued originAt exposed rootAt parentless older before originSlot rootSlot path edge ih =>
    obtain ⟨chain,correspondence⟩:=ih
    let step : Link allocation.extra origin root :=
      ⟨originRoot,root,originNode,rootNode,earlier,position,originAt,exposed,rootAt,parentless,older,before,
        originSlot,rootSlot,path,.refl _ rootNode rootAt⟩
    refine ⟨.link chain step,?_⟩
    intro index
    constructor
    · intro below
      cases below with
      | refl => exact .inr (.refl _ rootNode rootAt)
      | @step actualParent _ actual prior =>
        have equal : actualParent=origin := Option.some.inj (Option.some.inj (actual.symm.trans edge))
        subst actualParent
        exact .inl ((correspondence index).mp prior)
    · intro member
      rcases member with previous | physical
      · exact .step edge ((correspondence index).mpr previous)
      · exact model.physical_below physical

/-- Both current token support and ALL actual retained-guard clauses transport
along the exact terminal ancestry equivalence. No byte bound follows here. -/
theorem carries {allocation : Allocation Provenance BorrowTree} {C : Completion}
    {held : ProtectedTags} {grant : UniIndex} {byte : Nat} {demand : Demand}
    (chain : Chain allocation.extra grant)
    (correspondence : ∀ index,Below C index grant ↔ chain.Member index)
    (embedding : Embeds allocation held C grant byte demand) :
    Carries allocation held chain byte demand := by
  intro segment member lower upper index node present
  have resource:=embedding segment member lower upper index node present
  exact ⟨fun onChain=>resource.1 ((correspondence index).mpr onChain),
    fun clash=>(correspondence index).mp (resource.2 clash)⟩

/-- The resource witness therefore has the raw-chain presentation without any
additional restriction on its sufficient domain. Storage bounds and actual row
coverage are deliberately not inferred from a possibly vacuous embedding. -/
theorem extract_support {before tracker id allocation C grant byte demand}
    (model : ParentInterpretation allocation.extra C)
    (issued : SpatialDelegation before tracker id allocation C grant)
    (embedding : Embeds allocation tracker.global.protectedTags C grant byte demand) :
    ∃ chain : Chain allocation.extra grant,
      (∀ index,Below C index grant ↔ chain.Member index) ∧
      Carries allocation tracker.global.protectedTags chain byte demand := by
  obtain ⟨chain,correspondence⟩:=extract model issued
  exact ⟨chain,correspondence,carries chain correspondence embedding⟩

/-- A physically bounded, represented byte retains those separate witnesses
and its fixed actual pointer/family value while only the support chain is
extracted. No family or program-copy coherence is reconstructed. -/
theorem extract_at {before tracker id allocation C byte demand}
    (model : ParentInterpretation allocation.extra C)
    (pointer : PointerInstance) (_pointerId : pointer.allocation=id)
    (binding : PointerBinds allocation pointer)
    (issued : SpatialDelegation before tracker id allocation C pointer.grant)
    (within : byte<allocation.len)
    (covered : ∃ segment,segment∈allocation.extra.locations.entries.toList ∧
      segment.range.start.toNat≤byte ∧ byte<segment.range.stop.toNat)
    (embedding : Embeds allocation tracker.global.protectedTags C pointer.grant byte demand) :
    ∃ chain : Chain allocation.extra pointer.grant,
      (∀ index,Below C index pointer.grant ↔ chain.Member index) ∧
      Carries allocation tracker.global.protectedTags chain byte demand ∧
      PointerBinds allocation pointer ∧ byte<allocation.len ∧
      ∃ segment,segment∈allocation.extra.locations.entries.toList ∧
        segment.range.start.toNat≤byte ∧ byte<segment.range.stop.toNat := by
  obtain ⟨chain,correspondence,support⟩:=extract_support model issued embedding
  exact ⟨chain,correspondence,support,binding,within,covered⟩

end
end DuplicatePrefix.CurrentCallSupportChainExtraction
