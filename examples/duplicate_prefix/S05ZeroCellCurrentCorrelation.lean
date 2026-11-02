import duplicate_prefix.S05ZeroCellJointCertificate
import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.OrdinaryBorrowAuthority

/-! Current finite correlation for the accepted packet. The precise side
replays the generated Tree Borrows events with the already fixed original1
origins. This is neither an ordinary-input predicate nor a preservation theorem
for arbitrary interpretations. -/
namespace DuplicatePrefix.S05ZeroCellCurrentCorrelation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

namespace Precise
def entryRead := S05ZeroCellJointCertificate.precise.performBorrowAccessRange
  (.concrete (tag 6)) Size.ZERO (Size.ofBytes 2) .Read
  S05ZeroCellActualCallInit.PureTree.held .VisitChildrenOfAccessed
def entryChild := entryRead.tree.newChild Size.ZERO (.concrete (tag 6)) (tag 8)
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
def sharedRead := entryChild.tree.performBorrowAccessRange
  (.concrete S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag)
  Size.ZERO (Size.ofBytes 2) .Read S05ZeroCellActualCallSharedStmt.PureTree.global.protectedTags
  .VisitChildrenOfAccessed
def sharedChild := sharedRead.tree.newChild Size.ZERO
  (.concrete S05ZeroCellActualCallSharedStmt.PureTree.initialGlobal.nextPointerTag)
  S05ZeroCellActualCallSharedStmt.PureTree.global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen false
def lenRead := sharedChild.tree.performBorrowAccessRange
  (.concrete S05ZeroCellActualCallLenReturn.PureTree.parent) Size.ZERO (Size.ofBytes 2)
  .Read S05ZeroCellActualCallLenReturn.PureTree.heldGlobal.protectedTags .VisitChildrenOfAccessed
def lenChild := lenRead.tree.newChild Size.ZERO
  (.concrete S05ZeroCellActualCallLenReturn.PureTree.parent)
  S05ZeroCellActualCallLenReturn.PureTree.tracker.global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true
def lenReleased := lenChild.tree.releaseProtector
  S05ZeroCellActualCallLenReturn.PureTree.tracker.global.nextPointerTag
  S05ZeroCellActualCallLenReturn.PureTree.heldGlobal.protectedTags
def defaultRead := lenReleased.tree.performBorrowAccessRange
  (.concrete S05ZeroCellActualCallAsMutReturn.PureTree.parent) Size.ZERO (Size.ofBytes 2)
  .Read S05ZeroCellActualCallAsMutReturn.PureTree.tracker.global.protectedTags .VisitChildrenOfAccessed
def defaultChild := defaultRead.tree.newChild Size.ZERO
  (.concrete S05ZeroCellActualCallAsMutReturn.PureTree.parent)
  S05ZeroCellActualCallAsMutReturn.PureTree.tracker.global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) (RootReferenceInfo.initial false))
  (RootReferenceInfo.policy false).outsidePermission false
def helperRead := defaultChild.tree.performBorrowAccessRange
  (.concrete S05ZeroCellActualCallAsMutReturn.PureTree.tracker.global.nextPointerTag)
  Size.ZERO (Size.ofBytes 2) .Read S05ZeroCellActualCallAsMutReturn.PureTree.heldGlobal.protectedTags
  .VisitChildrenOfAccessed
def helperChild := helperRead.tree.newChild Size.ZERO
  (.concrete S05ZeroCellActualCallAsMutReturn.PureTree.tracker.global.nextPointerTag)
  S05ZeroCellActualCallAsMutReturn.PureTree.helperTracker.global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside)
  ChildBorrow.fnEntryPolicy.outsidePermission true
def released := helperChild.tree.releaseProtector
  S05ZeroCellActualCallAsMutReturn.PureTree.helperTracker.global.nextPointerTag
  S05ZeroCellActualCallAsMutReturn.PureTree.heldGlobal.protectedTags
end Precise

def raw : BorrowTree := S05ZeroCellActualCallAsMutReturn.PureTree.released.tree
def precise : BorrowTree := Precise.released.tree
def held : ProtectedTags := S05ZeroCellActualCallRepaired.PureTree.held

theorem replay_completed :
    Precise.entryRead.status = .Completed ∧ Precise.entryChild.outcome = .ok () ∧
    Precise.sharedRead.status = .Completed ∧ Precise.sharedChild.outcome = .ok () ∧
    Precise.lenRead.status = .Completed ∧ Precise.lenChild.outcome = .ok () ∧
    Precise.lenReleased.status = .Released ∧ Precise.defaultRead.status = .Completed ∧
    Precise.defaultChild.outcome = .ok () ∧ Precise.helperRead.status = .Completed ∧
    Precise.helperChild.outcome = .ok () ∧ Precise.released.status = .Released := by cbv

/-- Identity and a common two-byte window survive the actual generated events. -/
theorem endpoint_identity :
    raw.nodes.data.size = 11 ∧ precise.nodes.data.size = 11 ∧
    raw.nodes.data.all Option.isSome = true ∧ precise.nodes.data.all Option.isSome = true ∧
    raw.tagMapping = precise.tagMapping ∧
    raw.nodes.data.map (Option.map TreeNode.tag) = precise.nodes.data.map (Option.map TreeNode.tag) ∧
    raw.nodes.data.map (Option.map TreeNode.isExposed) = precise.nodes.data.map (Option.map TreeNode.isExposed) ∧
    raw.locations.entries.size = 1 ∧ precise.locations.entries.size = 1 ∧
    (raw.locations.entries[0]?).map (·.range) = some ⟨0,2⟩ ∧
    (precise.locations.entries[0]?).map (·.range) = some ⟨0,2⟩ := by cbv; decide +kernel

/-- One fixed completed ancestry; neither A nor B is reattached during replay. -/
theorem completed_parents :
    precise.nodes.data.map (Option.map TreeNode.parent) =
      #[some none,some (some (ix 0)),some (some (ix 1)),some (some (ix 0)),
        some (some (ix 2)),some (some (ix 3)),some (some (ix 5)),
        some (some (ix 6)),some (some (ix 7)),some (some (ix 6)),some (some (ix 9))] := by cbv

def node (tree : BorrowTree) (i : Fin 11) : TreeNode :=
  (tree.nodeAt (ix i.val)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩
def state (tree : BorrowTree) (i : Fin 11) : LocationState :=
  let location := ((tree.locations.entries[0]?).map (·.data)).getD default
  (location.perms.get (ix i.val)).getD (node tree i).defaultLocationState
def sourceAncestor (i : Fin 11) : Prop :=
  i.val = 0 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 9 ∨ i.val = 10
/-- The finite rights split is the actual completed parent walk. -/
theorem source_walk :
    GeneralBorrowExposureAncestorFold.walk precise.nodes (precise.nodes.size+1) (ix 10) =
      [ix 10,ix 9,ix 6,ix 5,ix 3,ix 0] := by cbv
instance (i : Fin 11) : Decidable (sourceAncestor i) := by unfold sourceAncestor; infer_instance
def WriteRight (tree : BorrowTree) (i : Fin 11) : Prop :=
  if sourceAncestor i then LocalWrite (state tree i) (held.contains (node tree i).tag)
  else ForeignWrite (state tree i) (held.contains (node tree i).tag)

/-- Query-local rights in both correlated endpoints, on the common byte row.
This asks only for the selected source's actual ancestry relation. -/
theorem current_rights (i : Fin 11) : WriteRight precise i ∧ WriteRight raw i := by
  rcases i with ⟨i,bound⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cbv; simp

/-- The current copy's actual source is the last generated helper grant. -/
theorem source_binding :
    S05ZeroCellActualCallRepaired.PureTree.tag = (tag 13) ∧
    raw.indexOfTag S05ZeroCellActualCallRepaired.PureTree.tag = some (ix 10) ∧
    precise.indexOfTag S05ZeroCellActualCallRepaired.PureTree.tag = some (ix 10) ∧
    precise.nthParent (tag 13) 0 = .ok (tag 13) ∧
    precise.nthParent (tag 13) 1 = .ok (tag 12) ∧
    precise.nthParent (tag 13) 2 = .ok (tag 8) ∧
    precise.nthParent (tag 13) 3 = .ok (tag 6) ∧
    precise.nthParent (tag 13) 4 = .ok (tag 4) ∧
    precise.nthParent (tag 13) 5 = .ok (tag 1) ∧
    precise.nthParent (tag 13) 6 = .error (.missingParent (tag 13) 6) := by cbv; simp

/-- Both physical bytes use the same proved row; no fresh origin is selected
for the second byte. This is the source-relation-specific scalar transfer,
not the four-way candidate Refines inclusion. -/
theorem both_bytes_transfer (byte : Fin 2) (i : Fin 11) :
    (∃ rawSegment preciseSegment,
      raw.locations.entries[0]? = some rawSegment ∧
      precise.locations.entries[0]? = some preciseSegment ∧
      rawSegment.range.start.toNat ≤ byte.val ∧ byte.val < rawSegment.range.stop.toNat ∧
      preciseSegment.range.start.toNat ≤ byte.val ∧ byte.val < preciseSegment.range.stop.toNat) ∧
    WriteRight precise i ∧ (WriteRight precise i → WriteRight raw i) := by
  rcases byte with ⟨byte,bound⟩
  have cases : byte=0 ∨ byte=1 := by omega
  rcases cases with rfl | rfl
  all_goals refine ⟨?_,(current_rights i).1,fun _ => (current_rights i).2⟩
  all_goals refine ⟨(raw.locations.entries[0]?).getD ⟨⟨0,2⟩,default⟩,
    (precise.locations.entries[0]?).getD ⟨⟨0,2⟩,default⟩,?_,?_,?_,?_,?_,?_⟩
  all_goals cbv

end DuplicatePrefix.S05ZeroCellCurrentCorrelation

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCurrentCorrelation." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current correlation dependency {dependency}"
