import duplicate_prefix.DuplicatePrefixCrossKindMaskedGuard
import duplicate_prefix.DuplicatePrefixReadWriteScalarAuthorization
import duplicate_prefix.GeneralBorrowSnapshotReadState
namespace DuplicatePrefix.DuplicatePrefixReadWriteMaskedAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCrossKindMaskedGuard
open GeneralBorrowSnapshotReadState (wildcard)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The original Read query guards both arbitrary masked Write queries,
including different entry and exit removal masks. No legality or nesting is
needed for this contributor-set implication. -/
theorem guards (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (before after : List UniIndex) (read : AccessRelatedness)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (classified : relation location root index node maximum .Read rootPosition = some (wildcard read)) :
    DuplicatePrefixReadWriteScalarAuthorization.Guards read
      (residualRelation tree location protections root index node maximum .Write rootPosition before)
      (residualRelation tree location protections root index node maximum .Write rootPosition after) := by
  constructor
  · intro localRead
    subst read
    exact ⟨local_read_residual_write tree location protections before root index node maximum rootPosition coherent short covers classified,
      local_read_residual_write tree location protections after root index node maximum rootPosition coherent short covers classified⟩
  · intro foreignRead
    subst read
    constructor
    · intro localWrite
      exact residual_local_write_not_foreign_read tree location protections before root index node maximum rootPosition coherent short covers localWrite classified
    · intro localWrite
      exact residual_local_write_not_foreign_read tree location protections after root index node maximum rootPosition coherent short covers localWrite classified

/-- The raw original Read scalar query, its actual recurse decision, and old
Write authorization derive a real Read transition retaining authorization for
both original masked Write classifications. This is a scalar bridge; updating
contributor masks after a lost node is a separate simulation obligation. -/
theorem visit (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (before after : List UniIndex) (read : AccessRelatedness)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (classified : relation location root index node maximum .Read rootPosition = some (wildcard read))
    (rawRead : Scalar ((location.perms.get index).getD node.defaultLocationState) .Read (protections.contains node.tag)
      (relation location root index node maximum .Read rootPosition))
    (recurse : skip ((location.perms.get index).getD node.defaultLocationState) .Read read = false)
    (oldWrite : DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((location.perms.get index).getD node.defaultLocationState) .Write (protections.contains node.tag)
      (residualRelation tree location protections root index node maximum .Write rootPosition before)
      (residualRelation tree location protections root index node maximum .Write rootPosition after)) :
    ∃ recorded next delta,
      ((location.perms.get index).getD node.defaultLocationState).recordNewAccess .Read read = .Recorded recorded ∧
      recorded.performAccess .Read read (protections.contains node.tag) = .Success next delta ∧
      DuplicatePrefixCallbackVisitAuthorization.Authorized next .Write (protections.contains node.tag)
        (residualRelation tree location protections root index node maximum .Write rootPosition before)
        (residualRelation tree location protections root index node maximum .Write rootPosition after) := by
  have readCompatible : GeneralBorrowProtectedReadCompatible.Compatible
      ((location.perms.get index).getD node.defaultLocationState) read (protections.contains node.tag) := by
    rw [classified] at rawRead
    cases read <;> rcases rawRead.2 with skipped | compatible
    · have impossible : (false : Bool) = true := recurse.symm.trans skipped
      cases impossible
    · exact compatible
    · have impossible : (false : Bool) = true := recurse.symm.trans skipped
      cases impossible
    · exact compatible
  have scheduled : GeneralBorrowEvents.Scheduled ((location.perms.get index).getD node.defaultLocationState) .Read read := by
    apply GeneralBorrowEvents.recurse_scheduled
    cases actualSkip : ((location.perms.get index).getD node.defaultLocationState).skipIfKnownNoop .Read read with
    | Recurse => rfl
    | SkipSelfAndChildren =>
      have skipped := (skip_source _ _ _).mpr actualSkip
      have impossible : (false : Bool) = true := recurse.symm.trans skipped
      cases impossible
  exact DuplicatePrefixReadWriteScalarAuthorization.visit _ read _ _ _ readCompatible scheduled oldWrite
    (guards tree location protections root index node maximum rootPosition before after read coherent short covers classified)
end DuplicatePrefix.DuplicatePrefixReadWriteMaskedAuthorization
