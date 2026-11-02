import empty_function.ConcreteRights
import empty_function.WildcardRights

namespace EmptyFunction.ChildSuccess
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Every raw allocator either supplies a fresh vacant slot or returns its
explicit index-exhaustion outcome. Reusable slots need no append room. -/
theorem allocate_total (tree : BorrowTree) (currentTag tag : BorTag)
    (input : TreeRuntimeInput.TreeFormed tree currentTag)
    (fresh : tree.tagMapping.get tag = none) :
    (∃ mapping index, tree.tagMapping.insert tag = .Inserted mapping index ∧
      mapping.get tag = some index ∧ tree.nodes.get index = none) ∨
    tree.tagMapping.insert tag = .Error tree.tagMapping (.IndexSpaceExhausted tree.tagMapping.mapping.size) := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    by_cases room : tree.tagMapping.mapping.size ≤ 4294967295
    · apply Or.inl
      let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
      let mapping : UniKeyMap BorTag := {
        mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
        deassigned := tree.tagMapping.deassigned }
      have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
        simp [UniKeyMap.insert, available, UniIndex.ofNat?, room, fresh, mapping, index]
      have endEq : index.toNat = tree.nodes.data.size := by
        simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
        exact input.appendAligned available
      have vacant : tree.nodes.get index = none := by
        unfold UniValMap.get
        simp [endEq]
      have selected : mapping.get tag = some index := by
        simp [mapping, UniKeyMap.get, Array.find?_push]
        have emptyFind : tree.tagMapping.mapping.find? (fun _ => false) = none :=
          Array.find?_eq_none.mpr (by intro row member; simp)
        rw [emptyFind]
        rfl
      exact ⟨mapping,index,inserted,selected,vacant⟩
    · apply Or.inr
      simp [UniKeyMap.insert,available,UniIndex.ofNat?,room]
  | some index =>
    apply Or.inl
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned.pop }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, fresh, mapping]
    have vacant := (input.reuseValid index available).2
    have selected : mapping.get tag = some index := by
      simp [mapping, UniKeyMap.get, Array.find?_push]
      have emptyFind : tree.tagMapping.mapping.find? (fun _ => false) = none :=
        Array.find?_eq_none.mpr (by intro row member; simp)
      rw [emptyFind]
      rfl
    exact ⟨mapping,index,inserted,selected,vacant⟩

/-- Invert actual successful zero-child insertion. The only numeric check is
performed by the source allocator; no size/fuel condition is assumed. -/
theorem inserted_of_success (tree : BorrowTree) (currentTag tag : BorTag)
    (input : TreeRuntimeInput.TreeFormed tree currentTag)
    (fresh : tree.tagMapping.get tag = none)
    (parent : ProvenanceExtra) (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset parent tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) :
    ∃ mapping index, tree.tagMapping.insert tag = .Inserted mapping index ∧
      mapping.get tag = some index ∧ tree.nodes.get index = none := by
  rcases allocate_total tree currentTag tag input fresh with allocated | exhausted
  · exact allocated
  · simp [BorrowTree.newChild,exhausted] at created

/-- A concrete successful unit retag carries its release certificate and old
rights for arbitrary existing trees, including full vectors with reusable slots. -/
theorem concrete (tree : BorrowTree) (currentTag tag : BorTag)
    (input : TreeRuntimeInput.TreeFormed tree currentTag)
    (fresh : tree.tagMapping.get tag = none)
    (parentTag : BorTag) (parent : UniIndex)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset (.concrete parentTag) tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) (protections : ProtectedTags) :
    after.releaseProtector tag protections = ⟨after,.Released⟩ ∧ Preservation.OldNodeRights tree after := by
  obtain ⟨mapping,index,inserted,selected,vacant⟩ :=
    inserted_of_success tree currentTag tag input fresh (.concrete parentTag) offset initial after created
  obtain ⟨parentNode,present⟩ := input.parentPresent parentTag parent tagged
  have released := Release.concrete_zero_release tree parentTag tag index parent parentNode mapping
    inserted tagged present vacant selected (input.vacantClean index vacant) offset initial protections
  have rights := ConcreteRights.constructor_of_insert tree tag parentTag parent parentNode mapping index
    fresh inserted tagged present vacant offset initial
  exact ⟨by simpa only [created] using released,by simpa only [created] using rights⟩

/-- Wildcard children are new roots; no parent-vs-child tag ordering is needed. -/
theorem wildcard (tree : BorrowTree) (currentTag tag : BorTag)
    (input : TreeRuntimeInput.TreeFormed tree currentTag)
    (fresh : tree.tagMapping.get tag = none)
    (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset .wildcard tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) (protections : ProtectedTags) :
    after.releaseProtector tag protections = ⟨after,.Released⟩ ∧ Preservation.OldNodeRights tree after := by
  obtain ⟨mapping,index,inserted,selected,vacant⟩ :=
    inserted_of_success tree currentTag tag input fresh .wildcard offset initial after created
  have released := Release.wildcard_zero_release tree tag index mapping inserted selected
    (input.vacantClean index vacant) offset initial protections
  have rights := WildcardRights.constructor_of_insert tree tag mapping index fresh inserted vacant offset initial
  exact ⟨by simpa only [created] using released,by simpa only [created] using rights⟩

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ChildSuccess." ||
        (name.toString.startsWith "_private." && name.toString.contains "ChildSuccess") ||
        name == ``ConcreteRights.constructor_of_insert || name == ``WildcardRights.constructor_of_insert then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved child-success axiom {dependency} in {name}"
  logInfo m!"Audited {total} child-success declarations"
#print axioms concrete
#print axioms wildcard
end EmptyFunction.ChildSuccess
