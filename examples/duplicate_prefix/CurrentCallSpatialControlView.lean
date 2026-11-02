import duplicate_prefix.CurrentCallSpatialCover
import duplicate_prefix.RootZeroCompleteState
namespace DuplicatePrefix.CurrentCallSpatialControlView
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallSpatialCover
set_option autoImplicit false
noncomputable section

def backing {before after : Before} (old : AllocationCover before) (world : ActualWorld after=ActualWorld before) : AllocationCover after :=
  ⟨old.id,old.allocation,by rw [world];exact old.live,old.cells,old.disjoint⟩

def context {before after : Before} (old : CurrentCallSpatialCover.Context before) (world : ActualWorld after=ActualWorld before) : CurrentCallSpatialCover.Context after where
  allocations:=old.allocations.map (fun allocation=>backing allocation world)
  unique:=by simpa only [Array.toList_map,List.map_map,Function.comp_def,backing] using old.unique

theorem issued {before after : Before} {tracker id allocation completion grant}
    (old : SpatialDelegation before tracker id allocation completion grant) (world : ActualWorld after=ActualWorld before) :
    SpatialDelegation after tracker id allocation completion grant := by
  induction old with
  | allocated cap => exact .allocated ⟨by rw [world];exact cap.live,cap.extent,cap.treeExtent,cap.rootSlot,cap.rootNode⟩
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot prior originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge

def role {before after tracker ctx mode offset length} (old : RoleCover before tracker ctx mode offset length)
    (world : ActualWorld after=ActualWorld before) : RoleCover after tracker (context ctx world) mode offset length where
  family:=old.family
  backing:=backing old.backing world
  backingAt:=by
    change backing old.backing world∈(ctx.allocations.map (fun allocation=>backing allocation world)).toList
    rw [Array.toList_map]
    exact List.mem_map.mpr ⟨old.backing,old.backingAt,rfl⟩
  id:=old.id
  covered:=old.covered
  roles:=fun i overlap=>⟨(old.roles i overlap).grant,(old.roles i overlap).binding,issued (old.roles i overlap).issued world,(old.roles i overlap).available⟩

def reindex {before tracker ctx mode offset length nextOffset nextLength}
    (old : RoleCover before tracker ctx mode offset length) (offsetEq : nextOffset=offset) (lengthEq : nextLength=length) :
    RoleCover before tracker ctx mode nextOffset nextLength where
  family:=old.family
  backing:=old.backing
  backingAt:=old.backingAt
  id:=old.id
  covered:=by intro byte request;rw [offsetEq,lengthEq] at request;exact old.covered byte request
  roles:=by
    intro i overlap
    have original : ∃byte,Window old.backing.id offset length byte ∧Window old.backing.id old.backing.cells[i].offset old.backing.cells[i].length byte := by
      simpa only [offsetEq,lengthEq] using overlap
    exact ⟨(old.roles i original).grant,(old.roles i original).binding,(old.roles i original).issued,
      fun byte request cell=>(old.roles i original).available byte (by simpa only [offsetEq,lengthEq] using request) cell⟩

theorem tick_world (options remaining span before) :
    ActualWorld (RootZeroCompleteState.tick options remaining span before)=ActualWorld before := by
  unfold ActualWorld RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
end
end DuplicatePrefix.CurrentCallSpatialControlView
