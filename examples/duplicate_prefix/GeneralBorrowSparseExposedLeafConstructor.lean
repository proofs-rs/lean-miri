import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowSparseExposedLeafExpose
import duplicate_prefix.GeneralBorrowSparseExposedLeafDefaults
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcardAllocator
import duplicate_prefix.GeneralBorrowWildcardRootCache
import duplicate_prefix.GeneralBorrowPositiveWildcardVacantClean
import duplicate_prefix.GeneralBorrowFreshRangeFrame
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedLeafState GeneralBorrowSparseExposedLeafExpose GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert
noncomputable section

def index (tree : BorrowTree) : UniIndex:=⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
def mapping (tree : BorrowTree) (tag : BorTag) : UniKeyMap BorTag:=⟨tree.tagMapping.mapping.push (tag,index tree),tree.tagMapping.deassigned⟩
def after (tree : BorrowTree) (tag : BorTag) (offset len : UInt64) :=
  GeneralBorrowPositiveWildcardConstructor.result tree (mapping tree tag) (index tree) tag
    (.ReservedFrz false) .Read GeneralBorrowFreshDefaultChild.inside offset len

theorem append (tree : BorrowTree) (protections : ProtectedTags)
    (initial : GeneralBorrowStructuralHistoryState.State tree)
    (raw : Every (fun location=>Raw tree location protections) tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (noFree : tree.tagMapping.deassigned.back?=none) (aligned : tree.tagMapping.mapping.size=tree.nodes.data.size)
    (room : tree.nodes.size+1<65536) (offset len : UInt64) (positive : len≠0)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false=
      ⟨after tree tag offset len,.ok ()⟩ ∧
    GeneralBorrowStructuralHistoryState.State (after tree tag offset len) ∧
    Every (fun location=>Raw (after tree tag offset len) location protections) (after tree tag offset len).locations ∧
    GeneralBorrowGcVacantClean.VacantClean (after tree tag offset len) ∧
    (after tree tag offset len).nodes.size=tree.nodes.size+1 ∧
    (after tree tag offset len).locations.size=tree.locations.size := by
  change tree.nodes.data.size+1<65536 at room
  let slot:=index tree
  let node:=WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .Read
  let base:=WildcardHitZeroConstructor.installed tree (mapping tree tag) slot tag (.ReservedFrz false) .Read
  have fits : tree.tagMapping.mapping.size≤4294967295 := by rw [aligned];omega
  have atEnd : slot.toNat=tree.nodes.data.size := by
    simp only [slot,index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size<2^32)]
    exact aligned
  have vacant : tree.nodes.get slot=none:=by simp [UniValMap.get,atEnd]
  have size : (tree.nodes.insert slot node).size=tree.nodes.size+1:=GeneralBorrowFreshNode.append_size tree.nodes slot node atEnd
  have inserted:=GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh noFree fits
  have actual:=GeneralBorrowPositiveWildcardConstructor.append tree tag fresh noFree fits (.ReservedFrz false) .Read GeneralBorrowFreshDefaultChild.inside false
    rfl rfl rfl rfl rfl offset len positive initial.well bounds
  change tree.newChild _ _ _ _ _ _=⟨after tree tag offset len,.ok ()⟩ at actual
  obtain ⟨allocated,chosen,selected,graph,growth⟩:=GeneralBorrowStructuralHistoryWildcardAllocator.select tree initial.toGraphState tag fresh (by change tree.nodes.data.size+1≤4294967295;omega) (.ReservedFrz false) .Read
  have equal:=UniKeyMapInsertResult.Inserted.inj (inserted.symm.trans selected)
  have baseGraph : GeneralBorrowStructuralHistoryState.GraphState base := by
    rw [←equal.1,←equal.2] at graph
    exact graph
  have frame:=GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location=>{location with perms:=location.perms.insert slot GeneralBorrowFreshDefaultChild.inside}) initial.well bounds
  have structural : GeneralBorrowStructuralHistoryState.State (after tree tag offset len):=
    ⟨GeneralBorrowStructuralHistoryState.graph_locations base _ baseGraph,frame.1⟩
  have initialScalar : Every (Scalars base protections) tree.locations := by
    intro position valid query value found
    by_cases same : query=slot
    · subst query
      change (tree.nodes.insert slot node).get slot=some value at found
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      have absent:=clean slot vacant position valid
      exact GeneralBorrowSparseExposedLeafDefaults.vacant_reserved _ slot node _ absent rfl
    · change (tree.nodes.insert slot node).get query=some value at found
      rw [GeneralBorrowFreshLocation.get_other _ slot query node same] at found
      exact (raw position valid).2 query value found
  have scalar:=GeneralBorrowExposureChildAttach.modify_every (Scalars base protections) tree.locations
    (Size.ofBytes offset) (Size.ofBytes len) (fun _ location=>{location with perms:=location.perms.insert slot GeneralBorrowFreshDefaultChild.inside})
    initial.well bounds initialScalar (by
      intro range location good query value found
      by_cases same : query=slot
      · subst query
        change (tree.nodes.insert slot node).get slot=some value at found
        rw [GeneralBorrowFreshLocation.get_same] at found
        cases found
        simp [GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshLocation.get_same,GeneralBorrowFreshDefaultChild.inside,
          GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
      · simpa only [GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshLocation.get_other _ slot query _ same] using good query value found)
  obtain ⟨depth⟩:=initial.depth
  have coherent:=GeneralBorrowWildcardRootCache.constructor tree depth (mapping tree tag) slot tag (.ReservedFrz false) .Read
    GeneralBorrowFreshDefaultChild.inside offset len vacant (by rw [size];omega) initial.well bounds protections (fun position valid=>(raw position valid).1)
  refine ⟨actual,structural,?_,?_,size,congrArg Size.ofBytes frame.2⟩
  · intro position valid
    exact ⟨coherent position valid,scalar position valid⟩
  · exact GeneralBorrowPositiveWildcardVacantClean.preserves tree (mapping tree tag) slot tag (.ReservedFrz false) .Read
      GeneralBorrowFreshDefaultChild.inside offset len initial.well bounds clean
end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafConstructor
