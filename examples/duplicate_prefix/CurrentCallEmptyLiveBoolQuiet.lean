import duplicate_prefix.CurrentCallConversionBoolPhase
import duplicate_prefix.CurrentCallSelectedBoolQuietSource
import duplicate_prefix.CurrentCallEmptyEntrySourceData
namespace DuplicatePrefix.CurrentCallEmptyLiveBoolQuiet
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem retain {options remaining span machine tracker frame borrowFrame place}
    (D : CurrentCallConversionBoolPhase.LiveData machine tracker frame borrowFrame place)
    (O : CurrentCallConversionBoolPhase.LiveProtected (options:=options) (remaining:=remaining) (span:=span) D #[])
    (query : UniIndex) (node : TreeNode) (tag : BorTag)
    (present : D.window.allocation.extra.nodes.get query=some node)
    (tagged : node.tag=tag) (leaf : node.children=#[]) (hidden : node.isExposed=false)
    (different : query≠D.window.pointer.grant)
    (inactive : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) D.window.allocation.extra.locations) :
    CurrentCallEmptyEntrySourceData.Leaf O.output.window.allocation.extra tag := by
  have bounds : D.physical.offset.toNat+1≤D.window.allocation.extra.locations.size.bytes.toNat := by
    have inside:=(D.window.window (D.physical.id,D.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [D.window.issued.capability.treeExtent,←D.window.issued.capability.extent]
    exact inside
  obtain ⟨output,child,actual,outputTag,global,_,_,_,_,⟨witness⟩⟩:=CurrentCallResourceFnEntry.correlated_borrow_selected D.window D.runtime borrowFrame D.fresh rfl D.distinct
    (by have short:=D.short;omega) (by have short:=D.short;omega) D.physical.offset 1 rfl rfl (by decide) bounds
  have equal : output=O.operation:=Except.ok.inj (actual.symm.trans O.raw)
  subst output
  let constructor:=ReturnProtection.borrowedState #[] frame borrowFrame machine tracker D.fresh D.physical.id D.physical.entry O.operation.child.tree
  have live : constructor.machine.memory.live.find? (fun row=>row.1==D.physical.id)=some (D.physical.id,{D.physical.entry with allocation:=D.physical.entry.allocation.setExtra O.operation.child.tree}) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory _ _
  have presentCtor : Present (ActualWorld constructor.machine) D.physical.id (D.window.allocation.setExtra O.operation.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    refine List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),?_⟩
    simp only [D.allocation]
  have rootTag : O.operation.global.rootTag? D.physical.id=tracker.global.rootTag? D.physical.id := by rw [global];rfl
  obtain ⟨next,nextAt,nextTag,nextParent,nextLeaf,nextHidden,quiet⟩:=CurrentCallSelectedBoolQuietSource.operation D.window D.runtime borrowFrame D.fresh D.distinct D.short
    D.physical.offset rfl O.operation child O.raw witness outputTag constructor.machine presentCtor rootTag query node present leaf hidden different inactive
  have afterAt : O.output.window.allocation.extra.nodes.get query=some next := by rw [O.extra];exact nextAt
  refine ⟨query,next,?_,afterAt,nextTag.trans tagged,nextLeaf.trans leaf,nextHidden.trans hidden,?_⟩
  · change O.output.window.allocation.extra.tagMapping.get tag=some query
    rw [←nextTag.trans tagged]
    exact O.output.runtime.formed.allocator.nodeTags _ _ afterAt
  · rw [O.extra];exact quiet
end
end DuplicatePrefix.CurrentCallEmptyLiveBoolQuiet
