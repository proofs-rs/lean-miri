import duplicate_prefix.GeneralBorrowAuthorizationMetadata
import duplicate_prefix.GeneralBorrowFreshMetadataChildSifa
import duplicate_prefix.GeneralBorrowSifaWritableFrame
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired

namespace DuplicatePrefix.CurrentCallEmptyEntrySifaWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization GeneralBorrowSharedAuthorizationGeometry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Full authorization transport uses permission metadata globally and exact
scalar states only on its support. Hidden extensions and SIFA rewrites fit the
same finite-data interface; no operational success is assumed. -/
private theorem transport (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (nextDepth : GeneralBorrowExposure.ParentDepth after.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.tag = node.tag ∧ next.isExposed = node.isExposed ∧
        ((newLocation.perms.get index).getD next.defaultLocationState).permission =
        ((oldLocation.perms.get index).getD node.defaultLocationState).permission)
    (back : ∀ index next,after.nodes.get index = some next → next.isExposed = true →
      ∃ node,before.nodes.get index = some node)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization before oldLocation protections root position maximum kind support)
    (nodes : ∀ query,support query → after.nodes.get query = before.nodes.get query)
    (slots : ∀ query,support query → newLocation.perms.get query = oldLocation.perms.get query) :
    DuplicatePrefixResidualWriteRepaired.Authorization after newLocation protections root position maximum kind support := by
  have count (query : UniIndex) (removed : List UniIndex) :
      residualCount after newLocation protections kind removed query =
      residualCount before oldLocation protections kind removed query := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension before after oldLocation newLocation
      protections depth size _ back removed query kind
    intro index node present
    obtain ⟨next,found,parent,tag,exposed,permission⟩ := metadata index node present
    refine ⟨next,found,parent,exposed,?_⟩
    simp only [effective,tag,permission]
  have removal (removed : List UniIndex) (legal : Removal after newLocation protections maximum kind removed) :
      Removal before oldLocation protections maximum kind removed := by
    refine ⟨legal.distinct,?_⟩
    intro index member
    obtain ⟨node,present,allowed⟩ := legal.allowed index member
    have exposed : node.isExposed = true := by
      cases kind with
      | Read => simp only [removable,Bool.false_eq_true] at allowed
      | Write =>
        cases flag : node.isExposed
        · simp only [removable,flag,Bool.false_and,Bool.false_eq_true] at allowed
        · rfl
    obtain ⟨oldNode,oldPresent⟩ := back index node present exposed
    obtain ⟨next,found,parent,tag,exposure,permission⟩ := metadata index oldNode oldPresent
    have equal := Option.some.inj (found.symm.trans present)
    subst next
    refine ⟨oldNode,oldPresent,?_⟩
    simpa only [removable,effective,aboveMaximum,tag,exposure,permission] using allowed
  refine ⟨old.rooted,?_,?_,?_,?_,?_,?_⟩
  · intro query included
    rw [nodes query included];exact old.present query included
  · intro query node included present child member
    rw [nodes query included] at present
    exact old.children query node included present child member
  · intro query included
    obtain ⟨node,present⟩ := old.present query included
    apply covers_of_path after nextDepth root query
    apply path_extension before after _ root query
      (GeneralBorrowWildcardControlWitness.path_of_covers before depth root query node present (old.covers query included))
    intro index node present
    obtain ⟨next,found,parent,_⟩ := metadata index node present
    exact ⟨next,found,parent⟩
  · intro query node included present
    rw [nodes query included] at present
    simpa only [slots query included] using old.possible query node included present
  · intro entry exit legalEntry legalExit subset query node included present retained
    rw [nodes query included] at present
    have initial := old.queries entry exit (removal entry legalEntry) (removal exit legalExit)
      subset query node included present retained
    simpa only [residualRelation,count,slots query included] using initial
  · intro physical
    obtain ⟨query,node,included,present,witness⟩ := old.witness physical
    refine ⟨query,node,included,?_,?_⟩
    · rw [nodes query included];exact present
    · simpa only [Supports,slots query included] using witness

/-- The repaired callback contract on a current row survives the constructor's
real ancestor-SIFA update. Exact node state is required only outside that path;
the row is the same arbitrary current visitor row on both sides. -/
theorem current_row (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (startNode : TreeNode) (present : tree.nodes.get start = some startNode)
    (current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree current protections root position maximum .Write support)
    (outside : ∀ query, support query → ¬Path tree query start) :
    DuplicatePrefixResidualWriteRepaired.Authorization (sourceUpdateSifa tree start .None).1
      current protections root position maximum .Write support := by
  let after := (sourceUpdateSifa tree start .None).1
  have shape : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape tree :=
    GeneralBorrowSifaView.preserves tree start .None
  let nextDepth := GeneralBorrowFreshMetadata.parent_depth tree after shape depth
  have size : tree.nodes.size ≤ after.nodes.size := by
    rw [GeneralBorrowFreshMetadata.node_size tree after shape]
    exact Nat.le_refl _
  refine transport tree after current current protections depth nextDepth size ?_ ?_
    root position maximum .Write support old ?_ (fun _ _ => rfl)
  · intro index node found
    obtain ⟨next,lookup,tag,parent,children,permission,exposure⟩ :=
      GeneralBorrowFreshMetadataChildSifa.node_fields tree start .None index node found
    refine ⟨next,lookup,parent,tag,exposure,?_⟩
    have same := GeneralBorrowSifaWritableFrame.effective_shape current current index node next rfl permission
    exact congrArg Prod.fst same
  · intro index next found _
    obtain ⟨node,lookup,_⟩ := GeneralBorrowFreshMetadata.node_exists after tree shape.symm index next found
    exact ⟨node,lookup⟩
  · intro query included
    exact congrArg Prod.fst
      (GeneralBorrowSifaOutsidePath.frame tree depth start startNode present query (outside query included) .None)

end DuplicatePrefix.CurrentCallEmptyEntrySifaWrite
