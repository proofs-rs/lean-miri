import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.GenericAsMutReleasePlan
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Graph, Write ownership and bytewise activity for a mutable helper's one
protector. No successful release or canonical tree layout is supplied. -/
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) where
  anchor : UniIndex
  root : UniIndex
  lower : UInt64
  upper : UInt64
  positive : lower.toNat < upper.toNat
  fits : tree.nodes.data.size ≤ 4294967296
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  node : TreeNode
  anchorPresent : tree.nodeAt anchor = some node
  notExposed : node.isExposed = false
  roots : tree.roots = #[root]
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag tag = some anchor
  well : tree.locations.WellFormed
  within : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write lower upper
  owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor .Write)
    lower upper tree.locations

noncomputable def release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) :=
  tree.releaseProtector tag protections

private theorem complete_result (result : BorrowTree.ProtectorReleaseResult) (done : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result with | mk tree status => cases done;rfl

/-- The real release and retained ownership follow from the input contract. -/
theorem released (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (input : Input tree protections tag) :
    (release tree protections tag).status = .Released ∧
    OwnedOn (GeneralBorrowRange.LocationOwned (release tree protections tag).tree protections input.anchor .Write)
      input.lower input.upper (release tree protections tag).tree.locations :=
  GeneralBorrowFreshReleaseLoop.release tree protections tag input.anchor input.root .Write input.lower input.upper
    input.positive input.fits input.depth input.children input.node input.anchorPresent input.notExposed input.roots input.covered
    input.tagPresent (GeneralBorrowFreshActiveWithin.active_on tree input.anchor .Write input.lower input.upper input.well input.within) input.owned

/-- Derive the source helper-pop plan; the release status is internal. -/
theorem to_plan (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (input : Input entry.allocation.extra protections tag) :
    StackPopRelease.Plan protections [(id,tag)] memory
      (StackPopRelease.commitTree memory id entry (release entry.allocation.extra protections tag).tree) :=
  .live id tag entry _ [] memory _ present (complete_result _ (released _ _ _ input).1) (.nil _)

end DuplicatePrefix.GenericAsMutReleasePlan
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GenericAsMutReleasePlan.released,``DuplicatePrefix.GenericAsMutReleasePlan.to_plan] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generic asmut release dependency {dependency}"
