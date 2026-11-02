import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyRelease
import duplicate_prefix.GeneralBorrowExposedUniqueRowsCoherent
import duplicate_prefix.GeneralBorrowUniqueRootExposure
import duplicate_prefix.GeneralBorrowWildcardRootCache
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyCycle
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyAppend
open GeneralBorrowExposedUniqueRootFamilyRelease RangeMapNonempty GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

def ended (global : GlobalState) (fresh : global.nextPointerTag.value<18446744073709551615) (allocation : AllocId) : GlobalState :=
  (registered global fresh allocation).1.endCall (registered global fresh allocation).2

def releaseTree (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (allocation : AllocId) (fresh : global.nextPointerTag.value<18446744073709551615) : BorrowTree :=
  {after tree global capacity with locations:=homogeneous capacity (releaseLocation capacity global tree location allocation fresh)}
def finalLocation (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (allocation : AllocId) (fresh : global.nextPointerTag.value<18446744073709551615) : LocationTree :=
  let before := releaseLocation capacity global tree location allocation fresh
  {before with exposedCache:=GeneralBorrowUniqueRootExposure.bump before.exposedCache (index tree)}
def finalTree (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (allocation : AllocId) (fresh : global.nextPointerTag.value<18446744073709551615) : BorrowTree :=
  {(GeneralBorrowExposeRead.marked (releaseTree capacity global tree location allocation fresh) (index tree)
    (WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None)) with
      locations:=homogeneous capacity (finalLocation capacity global tree location allocation fresh)}

private theorem insert_size_of_le {α : Type} (map : UniValMap α) (index : UniIndex) (value : α)
    (bound : map.data.size≤index.toNat) : (map.insert index value).size=index.toNat+1 := by
  have size : (UniValMap.extendTo map.data (index.toNat+1)).size=index.toNat+1 := by
    simp only [UniValMap.extendTo,Array.size_append,Array.size_replicate]
    omega
  simp only [UniValMap.insert,Id.run,pure,UniValMap.size,size]
  simp only [show index.toNat<index.toNat+1 by omega,↓reduceDIte,Array.size_set,size]

/-- One actual new-pointer/Strong/wildcard/Write/release/endCall/exposure cycle
closes the exposed Unique root-family invariant from numeric room alone. -/
theorem cycle (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536) :
    let held := registered global fresh allocation
    let current := written capacity global tree allocation fresh
    let released := current.tree.releaseProtector global.nextPointerTag held.1.protectedTags
    global.newPointerTag=.ok (allocated global fresh,global.nextPointerTag) ∧
      current.status=.Completed ∧ released.status=.Released ∧ released.tree=releaseTree capacity global tree location allocation fresh ∧
      (released.tree.exposeTag (ended global fresh allocation).protectedTags global.nextPointerTag)=
        ⟨finalTree capacity global tree location allocation fresh,.ok ()⟩ ∧
      Family capacity (ended global fresh allocation) (finalTree capacity global tree location allocation fresh)
        (finalLocation capacity global tree location allocation fresh) (roots++[index tree]) := by
  obtain ⟨allocatedTag,readDone,builtExact,structural,locations,rootEq,present,stored,cache,old⟩ :=
    GeneralBorrowExposedUniqueRootFamilyAppend.append capacity global tree location roots family allocation fresh room
  have activated := GeneralBorrowExposedUniqueRootFamilyActivate.activate capacity global tree location roots family allocation fresh room
  have released := GeneralBorrowExposedUniqueRootFamilyRelease.release capacity global tree location roots family allocation fresh room
  let before := after tree global capacity
  let node := WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None
  let middle := releaseLocation capacity global tree location allocation fresh
  let releasedTree := releaseTree capacity global tree location allocation fresh
  let nextLoc := finalLocation capacity global tree location allocation fresh
  let nextTree := finalTree capacity global tree location allocation fresh
  let nextGlobal := ended global fresh allocation
  have atEnd : (index tree).toNat=tree.nodes.data.size := by
    have fit : tree.tagMapping.mapping.size<2^32 := by rw [family.aligned];change tree.nodes.size<2^32;omega
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt fit]
    exact family.aligned
  have newSize : before.nodes.size=tree.nodes.size+1 := GeneralBorrowFreshNode.append_size tree.nodes (index tree) node atEnd
  have releasedEq : ((written capacity global tree allocation fresh).tree.releaseProtector global.nextPointerTag
      (registered global fresh allocation).1.protectedTags).tree=releasedTree := by
    rw [released.1]
    have shape := activated.2.1
    exact congrArg (fun source : BorrowTree=>{source with locations:=homogeneous capacity middle}) shape
  have tagged : releasedTree.indexOfTag global.nextPointerTag=some (index tree) := by
    have mapped := structural.allocator.nodeTags (index tree) node present
    simpa only [releasedTree,releaseTree,BorrowTree.indexOfTag,node,WildcardHitZeroConstructor.rootNode] using mapped
  have newPresent : releasedTree.nodeAt (index tree)=some node := present
  have afterWell : releasedTree.locations.WellFormed := by
    simp [releasedTree,releaseTree,homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr family.nonzero]
  have afterState : GeneralBorrowStructuralHistoryState.State releasedTree :=
    ⟨GeneralBorrowStructuralHistoryState.graph_locations before (homogeneous capacity middle) structural.toGraphState,afterWell⟩
  have oldPresent : ∀ query leaf,tree.nodeAt query=some leaf → query≠index tree → before.nodeAt query=some leaf := by
    intro query leaf found different
    exact (GeneralBorrowFreshLocation.get_other tree.nodes (index tree) query node different).trans found
  have exposedOld : ∀ query leaf,releasedTree.nodeAt query=some leaf → leaf.isExposed=true → query∈roots := by
    intro query leaf found exposed
    by_cases same : query=index tree
    · subst query
      have equal := Option.some.inj (found.symm.trans newPresent)
      subst leaf
      change false=true at exposed
      cases exposed
    · have original : tree.nodeAt query=some leaf := by
        change (tree.nodes.insert (index tree) node).get query=some leaf at found
        rw [GeneralBorrowFreshLocation.get_other _ _ _ _ same] at found
        exact found
      exact family.allNodes query leaf original
  obtain ⟨depth⟩ := family.structural.depth
  have vacant : tree.nodes.get (index tree)=none := by simp [UniValMap.get,atEnd]
  have grows : tree.nodes.size≤(tree.nodes.insert (index tree) node).size := by rw [GeneralBorrowFreshNode.append_size _ _ _ atEnd];omega
  have bounds : (0:UInt64).toNat+capacity.toNat≤tree.locations.size.bytes.toNat := by rw [family.locations];simp [homogeneous,DedupRangeMap.size,Size.ofBytes]
  have initialCoherent : Every (fun loc=>GeneralBorrowExposureCardinality.LocationCoherent tree loc (registered global fresh allocation).1.protectedTags) tree.locations := by
    rw [family.locations]
    intro position valid
    have zero : position=0 := by change position<1 at valid;omega
    subst position
    exact GeneralBorrowExposedUniqueRootFamilyRead.coherent capacity global tree location roots family _
  have insertedCoherent := GeneralBorrowWildcardRootCache.constructor tree depth (mapping tree global) (index tree) global.nextPointerTag
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity vacant grows family.structural.well bounds
    (registered global fresh allocation).1.protectedTags initialCoherent
  change Every (fun loc=>GeneralBorrowExposureCardinality.LocationCoherent before loc (registered global fresh allocation).1.protectedTags) before.locations at insertedCoherent
  have beforeLocations : before.locations=homogeneous capacity (locationAfter tree location) := locations
  have baseCoherent : GeneralBorrowExposureCardinality.LocationCoherent before (locationAfter tree location) (registered global fresh allocation).1.protectedTags := by
    rw [beforeLocations] at insertedCoherent
    exact insertedCoherent 0 (by change 0<1;decide)
  have coherent : GeneralBorrowExposureCardinality.LocationCoherent releasedTree middle nextGlobal.protectedTags := by
    apply GeneralBorrowExposedUniqueRowsCoherent.frame releasedTree (locationAfter tree location) middle
      (registered global fresh allocation).1.protectedTags nextGlobal.protectedTags baseCoherent released.2.2.1
    intro query leaf found exposed
    have member := exposedOld query leaf found exposed
    obtain ⟨oldNode,oldFound,parentless,children,flag,unique,oldCache,below⟩ := old query member
    exact ⟨unique,released.2.2.2 query member⟩
  obtain ⟨nextDepth⟩ := afterState.depth
  have exposeExact := GeneralBorrowUniqueRootExposure.expose releasedTree global.nextPointerTag (index tree) node middle capacity nextGlobal.protectedTags
    tagged newPresent rfl rfl ⟨GeneralBorrowWildcardLeaf.unique,released.2.1,rfl⟩ rfl
  have nextState := GeneralBorrowStructuralHistoryFrames.expose releasedTree afterState global.nextPointerTag nextGlobal.protectedTags
  have everyCoherent : GeneralBorrowPartitionExposeCardinality.Coherent releasedTree nextGlobal.protectedTags := by
    intro position valid
    have zero : position=0 := by change position<1 at valid;omega
    subst position
    exact coherent
  have nextCoherent := GeneralBorrowPartitionExposeCardinality.expose releasedTree nextGlobal.protectedTags (index tree) node newPresent tagged nextDepth everyCoherent
  change releasedTree.exposeTag nextGlobal.protectedTags global.nextPointerTag=⟨nextTree,.ok ()⟩ at exposeExact
  simp only [node,WildcardHitZeroConstructor.rootNode] at nextCoherent
  rw [exposeExact] at nextState nextCoherent
  have differentOld : ∀ query∈roots,query≠index tree := by
    intro query member equal
    obtain ⟨oldNode,found,_⟩ := family.leaves query member
    have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes query oldNode found
    rw [equal,atEnd] at bound
    omega
  have cacheEmpty : middle.exposedCache.nodes.get (index tree)=none := by rw [released.2.2.1];exact cache
  have permsShape : nextLoc.perms=middle.perms := by dsimp only [nextLoc,finalLocation,middle]
  have cacheShape : nextLoc.exposedCache=GeneralBorrowUniqueRootExposure.bump middle.exposedCache (index tree) := by
    dsimp only [nextLoc,finalLocation,middle]
  have rootStored : nextLoc.perms.get (index tree)=some GeneralBorrowWildcardLeaf.unique := released.2.1
  have rootCache : nextLoc.exposedCache.nodes.get (index tree)=some (⟨1,1⟩:ExposedCacheNode) := by
    change (GeneralBorrowUniqueRootExposure.bump middle.exposedCache (index tree)).nodes.get (index tree)=_
    simp only [GeneralBorrowUniqueRootExposure.bump,GeneralBorrowFreshLocation.get_same]
    rw [cacheEmpty]
    rfl
  have nodeShape : nextTree.nodes=releasedTree.nodes.insert (index tree) {node with isExposed:=true} := by
    dsimp only [nextTree,finalTree,GeneralBorrowExposeRead.marked,releasedTree,node]
  have finalPresent : nextTree.nodeAt (index tree)=some {node with isExposed:=true} := by
    unfold BorrowTree.nodeAt
    rw [nodeShape]
    exact GeneralBorrowFreshLocation.get_same releasedTree.nodes (index tree) {node with isExposed:=true}
  have releaseNodes : releasedTree.nodes=before.nodes := by dsimp only [releasedTree,releaseTree,before]
  have originalNodes : before.nodes=tree.nodes.insert (index tree) node := by
    dsimp only [before,after,GeneralBorrowPositiveWildcardConstructor.result,WildcardHitZeroConstructor.installed,node]
  have finalSize : nextTree.nodes.size=tree.nodes.size+1 := by
    rw [show nextTree.nodes.size= (releasedTree.nodes.insert (index tree) {node with isExposed:=true}).size from congrArg UniValMap.size nodeShape]
    rw [GeneralBorrowNodeUpdate.insert_existing_size _ (index tree) node _ newPresent]
    exact newSize
  have emptyProtections : nextGlobal.protectedTags={} := by
    change (global.protectedTags.insert global.nextPointerTag .StrongProtector).remove global.nextPointerTag={}
    rw [family.emptyProtections]
    simp [ProtectedTags.insert,ProtectedTags.remove]
  have highStep := GenericFunctionEntryNumerics.successor_value global.nextPointerTag fresh
  have nextHigh : ∀ row∈nextTree.tagMapping.mapping.toList,row.1.value<nextGlobal.nextPointerTag.value := by
    intro row member
    change row∈(tree.tagMapping.mapping.push (global.nextPointerTag,index tree)).toList at member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    have target : nextGlobal.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+1 := highStep
    apply UInt64.lt_iff_toNat_lt.mpr
    rcases member with previous | same
    · have below := UInt64.lt_iff_toNat_lt.mp (family.highWater row previous)
      omega
    · subst row;change global.nextPointerTag.value.toNat<nextGlobal.nextPointerTag.value.toNat;omega
  refine ⟨allocatedTag,activated.1,by rw [released.1],releasedEq,?_,?_⟩
  · rw [releasedEq];exact exposeExact
  · refine ⟨nextState.1,family.nonzero,rfl,?_,by simp,?_,?_,emptyProtections,?_,?_,?_,nextHigh,?_,?_⟩
    · change tree.roots.push (index tree)=(roots++[index tree]).toArray
      rw [family.rootsEq]
      exact List.push_toArray roots (index tree)
    · exact family.noFree
    · change (tree.tagMapping.mapping.push (global.nextPointerTag,index tree)).size=nextTree.nodes.data.size
      rw [Array.size_push]
      change tree.tagMapping.mapping.size+1=nextTree.nodes.size
      rw [family.aligned,finalSize]
      rfl
    · exact nextCoherent.2 0 (by change 0<1;decide)
    · intro query member
      rcases List.mem_append.mp member with original | current
      · obtain ⟨oldNode,found,parentless,children,flag,unique,oldCache,below⟩ := old query original
        have different := differentOld query original
        have finalFound : nextTree.nodeAt query=some oldNode := by
          unfold BorrowTree.nodeAt
          rw [nodeShape,GeneralBorrowFreshLocation.get_other releasedTree.nodes (index tree) query ({node with isExposed:=true}:TreeNode) different,releaseNodes]
          exact found
        have finalUnique : nextLoc.perms.get query=some GeneralBorrowWildcardLeaf.unique := by
          rw [permsShape]
          exact released.2.2.2 query original
        have finalCache : nextLoc.exposedCache.nodes.get query=some (⟨1,1⟩:ExposedCacheNode) := by
          rw [cacheShape,GeneralBorrowUniqueRootExposure.bump,
            GeneralBorrowFreshLocation.get_other middle.exposedCache.nodes (index tree) query
              _ different]
          rw [released.2.2.1]
          exact oldCache
        exact ⟨oldNode,finalFound,parentless,children,flag,finalUnique,finalCache⟩
      · have same : query=index tree := by simpa only [List.mem_singleton] using current
        subst query
        exact ⟨{node with isExposed:=true},finalPresent,rfl,rfl,rfl,rootStored,rootCache⟩
    · intro query leaf found
      by_cases same : query=index tree
      · simp [same]
      · have original : tree.nodeAt query=some leaf := by
          unfold BorrowTree.nodeAt at found
          rw [nodeShape,GeneralBorrowFreshLocation.get_other releasedTree.nodes (index tree) query ({node with isExposed:=true}:TreeNode) same,releaseNodes,originalNodes,GeneralBorrowFreshLocation.get_other tree.nodes (index tree) query node same] at found
          exact found
        exact List.mem_append_left _ (family.allNodes query leaf original)
    · change nextLoc.exposedCache.nodes.size≤nextTree.nodes.size
      rw [cacheShape,GeneralBorrowUniqueRootExposure.bump,insert_size_of_le]
      · rw [finalSize,atEnd]
        exact Nat.le_refl _
      · rw [released.2.2.1]
        have bound:=family.cacheBound
        change location.exposedCache.nodes.data.size≤tree.nodes.data.size at bound
        omega
    · rw [finalSize,List.length_append,List.length_singleton,family.size]
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyCycle
