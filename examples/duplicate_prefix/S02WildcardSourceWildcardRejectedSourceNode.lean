import duplicate_prefix.S02WildcardSourceWildcardSharedLenFull

namespace DuplicatePrefix.S02WildcardSourceWildcardRejectedSourceNode
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Real shared Ref/len retains the protected concrete source node for the
later active Return, including its hidden exposure state and tag lookup. -/
theorem preserved
    {before : DuplicatePrefixCallSpecification.Before}
    (address len : UInt64)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourcePacket : S02WildcardSourceWildcardBothPacket.SourcePacket reference output machine)
    (tracker held : MachineHooks.BorrowState)
    (sourceTree finalTree : BorrowTree)
    (sourceEq : sourceTree = output.child.tree)
    (raw : GeneralBorrowRawShared.Input sourceTree tracker.global)
    (rawTag : raw.parentTag = reference.tracker.global.nextPointerTag)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree raw.selected tracker held) :
    ∃ node : TreeNode,
      finalTree.nodeAt raw.parent = some node ∧
      finalTree.indexOfTag raw.parentTag = some raw.parent ∧
      node.tag = raw.parentTag ∧ node.isExposed = false := by
  have originalTagged : sourceTree.indexOfTag reference.tracker.global.nextPointerTag =
      some sourcePacket.child := by
      rw [sourceEq]
      simpa only [sourcePacket.entryEq,Allocation.setExtra,Allocation.mapExtra] using sourcePacket.tagged
  have sameParent : raw.parent = sourcePacket.child := by
    have tagged : sourceTree.indexOfTag reference.tracker.global.nextPointerTag = some raw.parent := by
      rw [←rawTag]
      exact raw.tagged
    exact Option.some.inj (tagged.symm.trans originalTagged)
  have originalPresent : sourceTree.nodeAt raw.parent = some sourcePacket.node := by
    rw [sameParent,sourceEq]
    simpa only [sourcePacket.entryEq,Allocation.setExtra,Allocation.mapExtra] using sourcePacket.present
  obtain ⟨node,present,sameTag,_sameParent,exposure,tagged⟩ :=
    graph.oldNodes raw.parent sourcePacket.node originalPresent
  refine ⟨node,present,?_,?_,?_⟩
  · rw [rawTag]
    rw [sourcePacket.same] at tagged
    exact tagged
  · rw [rawTag]
    exact sameTag.trans sourcePacket.same
  · exact exposure.trans sourcePacket.hidden

end
end DuplicatePrefix.S02WildcardSourceWildcardRejectedSourceNode

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardRejectedSourceNode.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard rejected-node dependency {dependency}"
