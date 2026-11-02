import duplicate_prefix.CurrentCallResourceNormalization
namespace DuplicatePrefix.CurrentCallNoUniformOrigin
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A new parentless grant cannot have one issued completed origin covering
both bytes when every exposed origin is actually revoked at one of them.
This excludes a joint issuance/content witness, not structural completions. -/
theorem no_uniform_origin (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (grant : UniIndex) (grantNode : TreeNode)
    (present : allocation.extra.nodes.get grant=some grantNode) (parentless : grantNode.parent=none)
    (notRoot : grant≠allocationRoot)
    (revoked : ∀ origin node,allocation.extra.nodes.get origin=some node → node.isExposed=true →
      ∃ byte,byte<2 ∧ ∃ segment∈allocation.extra.locations.entries.toList,
        segment.range.start.toNat≤byte ∧ byte<segment.range.stop.toNat ∧
        (RawState segment.data origin node).permission=.Disabled) :
    ¬∃ completion,ParentInterpretation allocation.extra completion ∧
      SpatialDelegation before tracker id allocation completion grant ∧
      ∀ byte,byte<2 → Embeds allocation held completion grant byte .exclusive := by
  rintro ⟨completion,model,issued,contents⟩
  have rootBelow := issued.root_below model
  have edge : ∃ origin,completion.parents[grant.toNat]?=some (some origin) := by
    cases rootBelow with
    | refl => exact False.elim (notRoot rfl)
    | step edge _ => exact ⟨_,edge⟩
  obtain ⟨origin,edge⟩ := edge
  obtain ⟨node,nodeAt,exposed,_⟩ := model.virtual_parent present parentless edge
  obtain ⟨byte,small,segment,member,start,stop,disabled⟩ := revoked origin node nodeAt exposed
  have token := ((contents byte small) segment member start stop origin node nodeAt).1
    (Below.step edge (.refl origin))
  simp only [denote,disabled,tokens,List.not_mem_nil] at token

/-- The two-byte split-origin specialization consumed by the actual trace.
The permission equations refer to actual saved segments, not a fabricated table. -/
theorem two_exposed (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (grant : UniIndex) (grantNode : TreeNode)
    (present : allocation.extra.nodes.get grant=some grantNode) (parentless : grantNode.parent=none)
    (notRoot : grant≠allocationRoot)
    (first second : UniIndex) (firstNode secondNode : TreeNode)
    (firstAt : allocation.extra.nodes.get first=some firstNode) (secondAt : allocation.extra.nodes.get second=some secondNode)
    (only : ∀ index node,allocation.extra.nodes.get index=some node → node.isExposed=true → index=first ∨ index=second)
    (left right : RangeMapSegment LocationTree)
    (leftMember : left∈allocation.extra.locations.entries.toList) (rightMember : right∈allocation.extra.locations.entries.toList)
    (leftStart : left.range.start.toNat≤0) (leftStop : 0<left.range.stop.toNat)
    (rightStart : right.range.start.toNat≤1) (rightStop : 1<right.range.stop.toNat)
    (firstDisabled : (RawState right.data first firstNode).permission=.Disabled)
    (secondDisabled : (RawState left.data second secondNode).permission=.Disabled) :
    ¬∃ completion,ParentInterpretation allocation.extra completion ∧
      SpatialDelegation before tracker id allocation completion grant ∧
      ∀ byte,byte<2 → Embeds allocation held completion grant byte .exclusive := by
  apply no_uniform_origin before tracker id allocation held grant grantNode present parentless notRoot
  intro index node atNode exposed
  rcases only index node atNode exposed with same | same
  · subst index
    have equal : node=firstNode := Option.some.inj (atNode.symm.trans firstAt)
    subst node
    exact ⟨1,by decide,right,rightMember,rightStart,rightStop,firstDisabled⟩
  · subst index
    have equal : node=secondNode := Option.some.inj (atNode.symm.trans secondAt)
    subst node
    exact ⟨0,by decide,left,leftMember,leftStart,leftStop,secondDisabled⟩

end
end DuplicatePrefix.CurrentCallNoUniformOrigin
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallNoUniformOrigin" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved split-origin separation dependency {dependency}"
