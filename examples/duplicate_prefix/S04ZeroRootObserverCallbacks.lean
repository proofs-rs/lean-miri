import duplicate_prefix.S04ZeroRootObserverNormal
import duplicate_prefix.GeneralBorrowWildcardRootAuthorization
import duplicate_prefix.S04ZeroLeafCallbackData

namespace DuplicatePrefix.S04ZeroRootObserverCallbacks
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowNodeUpdate DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- Hidden root insertion preserves every masked exposed count, including at
its newly allocated index. No tag ordering or protector restriction is needed. -/
theorem count (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) (query : UniIndex) :
    residualCount (slot.after tag) location protections kind removed query =
      residualCount tree location protections kind removed query := by
  apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension tree (slot.after tag) location location protections depth
    (by rw [slot.size tag];omega)
  · intro old node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag old node present,rfl,rfl,rfl⟩
  · intro old node present exposed
    by_cases same : old = slot.index
    · subst old
      change (tree.nodes.insert slot.index _).get slot.index = some node at present
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      cases exposed
    · exact ⟨node,(GeneralBorrowFreshLocation.get_other tree.nodes slot.index old _ same).symm.trans present⟩

/-- Existing physical-root callbacks retain their support, position and cutoff. -/
theorem old (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (initial : Authorization tree location protections root position maximum kind support) :
    Authorization (slot.after tag) location protections root position maximum kind support := by
  have growth : tree.nodes.size ≤ (tree.nodes.insert slot.index
      (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).size := by
    change tree.nodes.size ≤ (slot.after tag).nodes.size
    rw [slot.size tag]
    omega
  have got := GeneralBorrowWildcardRootAuthorization.insert tree depth slot.index
    (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) slot.vacant rfl rfl growth
    location location protections (by intros;rfl) root position maximum kind support initial
  refine ⟨got.rooted,got.present,got.children,got.covers,got.possible,?_,got.witness⟩
  intro entry exit legalEntry legalExit subset query node included found retained
  exact got.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩
    ⟨legalExit.distinct,legalExit.allowed⟩ subset query node included found retained

/-- The added root is secondary. Its virtual alternative makes its zero-count
callback Foreign for either cutoff branch, and its clean reservation is inactive. -/
theorem new (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (nonempty : 0 < tree.roots.size) (clean : location.perms.get slot.index = none)
    (maximum : Option BorTag) (kind : AccessKind) :
    Authorization (slot.after tag) location protections slot.index tree.roots.size maximum kind
      (fun query => query = slot.index) := by
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have present : (slot.after tag).nodes.get slot.index = some node := GeneralBorrowFreshLocation.get_same _ _ _
  have state : ((location.perms.get slot.index).getD node.defaultLocationState) = ⟨.ReservedFrz false,false,.None⟩ := by rw [clean];rfl
  have relation (removed : List UniIndex) :
      residualRelation (slot.after tag) location protections slot.index slot.index node maximum kind tree.roots.size removed =
        some .ForeignAccess := by
    unfold residualRelation
    rw [count tree slot tag depth location protections kind removed slot.index,S04ZeroLeafCallbackData.vacant_count tree depth location protections slot.index slot.vacant kind removed]
    apply S04ZeroLeafCallbackData.zero_foreign
    have virtual : (tree.roots.size != 0) = true := by simp [Nat.ne_of_gt nonempty]
    simp only [virtual,ite_true]
    omega
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · intro query same
    subst query
    exact ⟨node,present⟩
  · intro query value same found child member
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    cases member
  · intro query same
    subst query
    intro row member walked
    exact walked
  · intro query value same found
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [state]
    rfl
  · intro entry exit legalEntry legalExit subset query value same found retained
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [state,relation,relation]
    exact S04ZeroLeafCallbackData.foreign_authorized kind _
  · intro zero
    omega

end DuplicatePrefix.S04ZeroRootObserverCallbacks
