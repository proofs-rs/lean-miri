import duplicate_prefix.S02WildcardSameDestinationRootRow
import duplicate_prefix.S02DisjointConstructorMap
import duplicate_prefix.GeneralBorrowFreshRangeFrame
import duplicate_prefix.GeneralBorrowWildcardConstructorExact
import duplicate_prefix.GeneralBorrowWildcardConstructorSlot
namespace DuplicatePrefix.S02WildcardSameDestinationRootPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert
/-- Full old destination ownership survives the actual parentless protected
wildcard constructor on a disjoint source window. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64)
    (sourcePositive : Positive tree global.protectedTags none none none offset len)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (old : Positive tree global.protectedTags source selected maximum lower width) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧
    Nonempty (Positive actual.tree global.protectedTags source selected maximum lower width) ∧
    actual.tree.locations.size = tree.locations.size ∧
    (∀ query node,tree.nodeAt query = some node → actual.tree.nodeAt query = some node) ∧
    (∀ oldTag query,tree.indexOfTag oldTag = some query → actual.tree.indexOfTag oldTag = some query) := by
  obtain ⟨mapping,index,inserted,mappingRows,vacant,graph,size,growth⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have nonzero : len ≠ 0 := by intro zero;have positive:=sourcePositive.positive;rw [zero] at positive;contradiction
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero sourcePositive.bounds
  have slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)) index _ (GeneralBorrowFreshLocation.get_same tree.nodes index _)
    change index.toNat < (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).size at bounded
    change index.toNat = tree.nodes.size ∨ index.toNat < tree.nodes.size
    omega
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside offset len
  have frame := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => {location with perms := location.perms.insert index GeneralBorrowFreshChild.inside}) runtime.formed.well sourcePositive.bounds
  have nodeFrame (query : UniIndex) (value : TreeNode) (present : tree.nodeAt query = some value) : model.nodeAt query = some value := by
    have different : query ≠ index := by intro same;change tree.nodes.get query = some value at present;rw [same,vacant] at present;cases present
    exact (GeneralBorrowFreshLocation.get_other tree.nodes index query _ different).trans present
  have positive : Positive model global.protectedTags source selected maximum lower width := by
    refine ⟨old.positive,?_,?_,?_,?_⟩
    · change lower.toNat+width.toNat ≤ _
      dsimp only [model,GeneralBorrowPositiveWildcardConstructor.result]
      rw [frame.2]
      exact old.bounds
    · intro anchor same
      obtain ⟨value,present⟩ := old.sourcePresent anchor same
      exact ⟨value,nodeFrame anchor value present⟩
    · intro same
      change 0 < (tree.roots.push index).size
      simp
    · let predicate (location : LocationTree) := Nonempty (Row tree location global.protectedTags source selected maximum) ∧ location.perms.get index = none
      have initial : OwnedOn predicate lower (lower+width) tree.locations := by
        intro position valid nonempty start stop
        exact ⟨old.rows position valid nonempty start stop,(DuplicatePrefixBorrowContract.vacant_clean runtime) index vacant position valid⟩
      have preserved := S02DisjointConstructorMap.modify_outside tree.locations (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => {location with perms := location.perms.insert index GeneralBorrowFreshChild.inside})
        (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location index GeneralBorrowFreshChild.inside)
        predicate lower (lower+width) runtime.formed.well sourcePositive.bounds outside initial
      intro position valid nonempty start stop
      obtain ⟨⟨oldRow⟩,clean⟩ := preserved position valid nonempty start stop
      obtain ⟨row⟩ := S02WildcardSameDestinationRootRow.row tree mapping index tag runtime.formed.toGraphState vacant slot size graph
        (sourcePositive.wildcardRoot rfl) _ global.protectedTags clean source selected maximum old.sourcePresent oldRow
      exact GeneralBorrowWildcardRootRowPositive.row_locations _ model.locations _ global.protectedTags source selected maximum row
  rw [actual]
  refine ⟨rfl,⟨positive⟩,?_,nodeFrame,?_⟩
  · exact congrArg Size.ofBytes frame.2
  · intro oldTag query mapped
    have different : tag ≠ oldTag := by
      intro same
      have absent := GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh
      change tree.tagMapping.get oldTag = some query at mapped
      unfold UniKeyMap.get at mapped
      rw [←same,absent] at mapped
      cases mapped
    change mapping.get oldTag = some query
    unfold UniKeyMap.get
    rw [mappingRows]
    change (⟨tree.tagMapping.mapping.push (tag,index),mapping.deassigned⟩ : UniKeyMap BorTag).get oldTag = _
    rw [GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag oldTag different index mapping.deassigned]
    exact mapped
end DuplicatePrefix.S02WildcardSameDestinationRootPositive
