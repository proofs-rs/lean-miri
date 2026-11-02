import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowFreshReuseProtection
import duplicate_prefix.GeneralBorrowTagMap
import duplicate_prefix.GeneralBorrowProtector
import duplicate_prefix.GeneralRangeMapOrigins

namespace DuplicatePrefix.GeneralBorrowForestMutableRegister
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestMutableAccess (Data)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Freshness in the allocation map plus actual node/tag coherence implies
freshness for ALL existing nodes. No global protector absence follows from it. -/
theorem node_fresh (tree : BorrowTree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index) :
    ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag := by
  intro index node present same
  have lookup := nodeTags index node present
  have absent : tree.indexOfTag tag = none := by
    unfold BorrowTree.indexOfTag UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh]
    rfl
  rw [same,absent] at lookup
  cases lookup

/-- Actual insertion of a protector for an allocation-fresh tag retains all
old mutable/foreign/cache records. Global unheld/high-water conditions belong
to registration callers; map freshness alone does NOT imply global absence. -/
def protect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (tag : BorTag) (kind : ProtectorKind)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (data : Data tree location protections anchor primary extras) :
    Data tree location (protections.insert tag kind) anchor primary extras := by
  have protectorFresh : GeneralBorrowProtector.Fresh tree tag := by
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    exact fresh row.1 row.2 present
  have projection := GeneralBorrowProtector.normal_projection tree location protections tag kind protectorFresh
  refine {
    base := {
      forest := by rw [projection];exact data.base.forest
      owned := by rw [projection];exact data.base.owned
      rootPath := by rw [projection];exact data.base.rootPath
      region := {
        support := data.base.region.support
        present := data.base.region.present
        children := data.base.region.children
        unexposed := data.base.region.unexposed
        zero := data.base.region.zero
        owned := ?_ }
      supported := data.base.supported
      foreignGraph := by intro query member;rw [projection];exact data.base.foreignGraph query member }
    readZero := data.readZero }
  intro query node member present
  rw [ProtectorInsertion.contains_other protections tag node.tag kind (fresh query node present)]
  exact data.base.region.owned query node member present

/-- The REAL GlobalState.addProtector inserts both global kind and frame-owned
allocation/tag records. Existing slice data transports through that operation. -/
theorem registered (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (tag : BorTag) (kind : ProtectorKind) (anchor primary : UniIndex) (extras : List UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (unheld : global.protectedTags.get tag = none)
    (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location global.protectedTags anchor primary extras)) lower upper tree.locations) :
    (global.addProtector frame allocation tag kind).1.protectedTags.get tag = some kind ∧
    (global.addProtector frame allocation tag kind).2.protectedTags = frame.protectedTags.push (allocation,tag) ∧
    global.protectedTags.get tag = none ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location (global.addProtector frame allocation tag kind).1.protectedTags anchor primary extras))
      lower upper tree.locations := by
  refine ⟨ProtectedTags.get_insert_same _ _ _,rfl,unheld,?_⟩
  intro position valid positive beforeUpper afterLower
  obtain ⟨data⟩ := owned position valid positive beforeUpper afterLower
  exact ⟨protect tree _ global.protectedTags anchor primary extras tag kind (node_fresh tree tag fresh nodeTags) data⟩

end DuplicatePrefix.GeneralBorrowForestMutableRegister
