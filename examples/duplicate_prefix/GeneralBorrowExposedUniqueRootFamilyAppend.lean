import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyRead
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcard
import duplicate_prefix.GeneralBorrowHomogeneousFullModify
import duplicate_prefix.TypedRetagEmpty
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyAppend
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def allocated (global : GlobalState) (fresh : global.nextPointerTag.value<18446744073709551615) : GlobalState :=
  {global with nextPointerTag:=TypedRetagEmpty.successorTag global.nextPointerTag fresh}
def registered (global : GlobalState) (fresh : global.nextPointerTag.value<18446744073709551615) (allocation : AllocId) :=
  (allocated global fresh).addProtector {} allocation global.nextPointerTag .StrongProtector
def index (tree : BorrowTree) : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
def mapping (tree : BorrowTree) (global : GlobalState) : UniKeyMap BorTag :=
  ⟨tree.tagMapping.mapping.push (global.nextPointerTag,index tree),tree.tagMapping.deassigned⟩
def locationAfter (tree : BorrowTree) (location : LocationTree) : LocationTree :=
  {location with perms:=location.perms.insert (index tree) GeneralBorrowFreshChild.inside}
def after (tree : BorrowTree) (global : GlobalState) (capacity : UInt64) : BorrowTree :=
  GeneralBorrowPositiveWildcardConstructor.result tree (mapping tree global) (index tree) global.nextPointerTag
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity

/-- Real tag allocation, Strong registration, wildcard parent Read and new
isolated protected reservation, from the generated exposed-root family. -/
theorem append (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536) :
    global.newPointerTag=.ok (allocated global fresh,global.nextPointerTag) ∧
    let held := registered global fresh allocation
    let read := tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read held.1.protectedTags .VisitChildrenOfAccessed
    let built := read.tree.newChild Size.ZERO .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes capacity) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status=.Completed ∧ built=⟨after tree global capacity,.ok ()⟩ ∧
      GeneralBorrowStructuralHistoryState.State (after tree global capacity) ∧
      (after tree global capacity).locations=RangeMapNonempty.homogeneous capacity (locationAfter tree location) ∧
      (after tree global capacity).roots=tree.roots.push (index tree) ∧
      (after tree global capacity).nodeAt (index tree)=some (WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None) ∧
      (locationAfter tree location).perms.get (index tree)=some GeneralBorrowFreshChild.inside ∧
      (locationAfter tree location).exposedCache.nodes.get (index tree)=none ∧
      ∀ root∈roots,∃ node,(after tree global capacity).nodeAt root=some node ∧ node.parent=none ∧ node.children=#[] ∧ node.isExposed=true ∧
        (locationAfter tree location).perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
        (locationAfter tree location).exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode) ∧ node.tag.value<global.nextPointerTag.value := by
  have tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
    intro row member equal
    have bound := family.highWater row (Array.mem_toList_iff.mpr member)
    rw [equal] at bound
    exact (UInt64.lt_irrefl _) bound
  have fits : tree.tagMapping.mapping.size≤4294967295 := by rw [family.aligned];change tree.nodes.size≤_;omega
  have atEnd : (index tree).toNat=tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size<2^32)]
    exact family.aligned
  have bounds : (0:UInt64).toNat+capacity.toNat≤tree.locations.size.bytes.toNat := by
    rw [family.locations]
    simp [RangeMapNonempty.homogeneous,DedupRangeMap.size,Size.ofBytes]
  have read := GeneralBorrowExposedUniqueRootFamilyRead.ranged capacity global tree location roots family
    (registered global fresh allocation).1.protectedTags (by omega)
  have built := GeneralBorrowPositiveWildcardConstructor.append tree global.nextPointerTag tagFresh family.noFree fits (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl 0 capacity family.nonzero family.structural.well bounds
  change tree.newChild Size.ZERO .wildcard global.nextPointerTag (DedupRangeMap.new (Size.ofBytes capacity) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true=⟨after tree global capacity,.ok ()⟩ at built
  have structural := GeneralBorrowStructuralHistoryWildcard.construct tree family.structural global.nextPointerTag tagFresh (by omega) 0 capacity bounds
  dsimp only at structural
  simp only [show Size.ofBytes 0=Size.ZERO from rfl] at structural
  rw [built] at structural
  have locations : (after tree global capacity).locations=RangeMapNonempty.homogeneous capacity (locationAfter tree location) := by
    change (tree.locations.modifyRange Size.ZERO (Size.ofBytes capacity) (fun _ old=>{old with perms:=old.perms.insert (index tree) GeneralBorrowFreshChild.inside})).state=_
    rw [family.locations]
    exact GeneralBorrowHomogeneousFullModify.state capacity family.nonzero location _
  have geometry := GeneralBorrowPositiveWildcardConstructor.geometry tree (mapping tree global) (index tree) global.nextPointerTag
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
  refine ⟨TypedRetagEmpty.allocate_tag global fresh,?_⟩
  dsimp only
  rw [read.2]
  refine ⟨read.1,built,structural.2.1,locations,geometry.1,geometry.2,GeneralBorrowFreshLocation.get_same _ _ _,?_,?_⟩
  · change location.exposedCache.nodes.get (index tree)=none
    unfold UniValMap.get
    have bounded : location.exposedCache.nodes.data.size≤(index tree).toNat := by have b:=family.cacheBound;change location.exposedCache.nodes.data.size≤tree.nodes.data.size at b;omega
    rw [Array.getElem?_eq_none (by omega)]
  · intro root member
    obtain ⟨node,present,parentless,leaf,exposed,unique,cache⟩ := family.leaves root member
    have different : root≠index tree := by
      intro equal
      have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present
      rw [equal,atEnd] at bound
      omega
    have found : (after tree global capacity).nodeAt root=some node :=
      (GeneralBorrowFreshLocation.get_other tree.nodes (index tree) root _ different).trans present
    have tagged := family.structural.allocator.nodeTags root node present
    unfold UniKeyMap.get at tagged
    cases looked : tree.tagMapping.mapping.find? (fun row=>row.1==node.tag) with
    | none => simp [looked] at tagged
    | some row =>
      have key : row.1=node.tag := by simpa only [beq_iff_eq] using Array.find?_some looked
      have bound := family.highWater row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some looked))
      rw [key] at bound
      exact ⟨node,found,parentless,leaf,exposed,(GeneralBorrowFreshLocation.get_other location.perms (index tree) root _ different).trans unique,cache,bound⟩
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyAppend
