import duplicate_prefix.S05ZeroCellJointCertificate
import duplicate_prefix.DuplicatePrefixBorrowAuthorization

/-! One closed obstruction to the conservative raw callback contract for the
accepted finite caller. This is neither an ordinary-input exclusion nor a
whole-call error/NoUB theorem. The subset-pair condition overapproximates the
fixed-origin joint interpretation. -/
namespace DuplicatePrefix.S05ZeroCellContractQuery
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

abbrev tree := S05ZeroCellJointCertificate.raw
noncomputable def location : LocationTree := (tree.locations.entries[0]'(by cbv)).data
def dNode : TreeNode := (tree.nodeAt (ix 2)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩
def aNode : TreeNode := (tree.nodeAt (ix 1)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩
def vNode : TreeNode := (tree.nodeAt (ix 4)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩

theorem concrete_nodes : tree.nodeAt (ix 1) = some aNode ∧
    tree.nodeAt (ix 2) = some dNode ∧ tree.nodeAt (ix 4) = some vNode ∧
    ix 2 ∈ aNode.children.toList := by cbv <;> exact List.Mem.head _

theorem legal_removals : Removal tree location {} (some (tag 4)) .Write [] ∧
    Removal tree location {} (some (tag 4)) .Write [ix 4] := by
  refine ⟨empty_removal _ _ _ _ _,⟨by decide +kernel,?_⟩⟩
  intro index member
  have same : index = ix 4 := by simpa using member
  subst index
  exact ⟨vNode,concrete_nodes.2.2.1,by cbv⟩

theorem query_data :
    residualRelation tree location {} (ix 1) (ix 2) dNode (some (tag 4)) .Write 1 [] = some .EitherAccess ∧
    residualRelation tree location {} (ix 1) (ix 2) dNode (some (tag 4)) .Write 1 [ix 4] = some .ForeignAccess ∧
    (location.perms.get (ix 2)).getD dNode.defaultLocationState = ⟨.Disabled,true,.Read⟩ := by cbv

theorem query_rejected : ¬ DuplicatePrefixCallbackVisitAuthorization.Authorized
    ((location.perms.get (ix 2)).getD dNode.defaultLocationState) .Write (({} : ProtectedTags).contains dNode.tag)
    (residualRelation tree location {} (ix 1) (ix 2) dNode (some (tag 4)) .Write 1 [])
    (residualRelation tree location {} (ix 1) (ix 2) dNode (some (tag 4)) .Write 1 [ix 4]) := by
  rw [query_data.1,query_data.2.1,query_data.2.2]
  cbv

/-- Child closure forces D into ANY support rooted at A; the legal pair then
violates precisely the exit-skip clause of queries. -/
theorem no_authorization (support : UniIndex → Prop) :
    ¬ Authorization tree location {} (ix 1) 1 (some (tag 4)) .Write support := by
  intro authorization
  have dSupported := authorization.children (ix 1) aNode authorization.rooted
    concrete_nodes.1 (ix 2) concrete_nodes.2.2.2
  have result := authorization.queries [] [ix 4] legal_removals.1 legal_removals.2
    (by intro i impossible; cases impossible) (ix 2) dNode dSupported concrete_nodes.2.1 (by decide +kernel)
  exact query_rejected result

/-- The corresponding residual callback required by Row cannot be supplied. -/
theorem no_row : ¬ DuplicatePrefixBorrowAuthorization.Row tree location {}
    (some (ix 5)) (some (ix 3)) (some (tag 4)) := by
  intro row
  have size : 1 < tree.roots.size := by cbv
  have atA : tree.roots[1]'size = ix 1 := by cbv
  have different : (some (ix 3) : Option UniIndex) ≠ some (tree.roots[1]'size) := by
    rw [atA]
    decide +kernel
  obtain ⟨support,_,write⟩ := row.callbacks 1 size different
  rw [atA] at write
  exact no_authorization support write

/-- Thus the normalized source's positive-window borrow clause fails. This
states a conservative contract obstruction, not invalidity of the caller. -/
theorem no_positive_borrow : ¬ DuplicatePrefixBorrowAuthorization.Positive tree {}
    (some (ix 5)) (some (ix 3)) (some (tag 4)) 0 2 := by
  intro input
  have valid : 0 < tree.locations.entries.size := by cbv
  have start : (tree.locations.entries[0]'valid).range.start.toNat < (2 : UInt64).toNat := by cbv
  have stop : (0 : UInt64).toNat < (tree.locations.entries[0]'valid).range.stop.toNat := by cbv
  obtain ⟨row⟩ := input.rows 0 valid (by decide) start stop
  exact no_row row

end DuplicatePrefix.S05ZeroCellContractQuery
