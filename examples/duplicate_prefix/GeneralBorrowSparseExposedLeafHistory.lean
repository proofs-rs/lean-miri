import duplicate_prefix.GeneralBorrowSparseExposedLeafRange
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedLeafState GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

structure Event (capacity : UInt64) where
  offset : UInt64
  len : UInt64
  kind : AccessKind
  mode : ChildrenVisitMode
  bounds : offset.toNat+len.toNat≤capacity.toNat

/-- Arbitrary well-formed byte partitions retain raw present/default scalar
permissions. This is an initial permission protocol, not caller-history
classification or an arbitrary-Rust safety theorem. -/
structure State (capacity : UInt64) (protections : ProtectedTags) (primary : UniIndex) (extras : List UniIndex) where
  tree : BorrowTree
  geometry : Geometry tree primary extras
  well : tree.locations.WellFormed
  capacityEq : tree.locations.size=Size.ofBytes capacity
  raw : OwnedOn (fun location=>Raw tree location protections) 0 capacity tree.locations

def operation {capacity protections primary extras}
    (s : State capacity protections primary extras) (event : Event capacity) :=
  s.tree.performBorrowAccessRange .wildcard (Size.ofBytes event.offset) (Size.ofBytes event.len) event.kind protections event.mode

structure Output {capacity protections primary extras}
    (s : State capacity protections primary extras) (event : Event capacity) where
  state : State capacity protections primary extras
  actual : state.tree=(operation s event).tree
  completed : (operation s event).status=.Completed

def build {capacity protections primary extras}
    (s : State capacity protections primary extras) (event : Event capacity) : Output s event := by
  let result:=operation s event
  have fits : event.offset.toNat+event.len.toNat<18446744073709551616 := by
    have capacityBound:=UInt64.toNat_lt_size capacity
    change capacity.toNat<18446744073709551616 at capacityBound
    have bounded:=event.bounds
    omega
  have upper : (event.offset+event.len).toNat≤capacity.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    exact event.bounds
  have good:=GeneralBorrowSparseExposedLeafRange.access s.tree protections primary extras s.geometry
    (Size.ofBytes event.offset) (Size.ofBytes event.len) event.kind event.mode s.well 0 capacity s.raw
    (by rw [s.capacityEq];exact event.bounds) (by change 0≤event.offset.toNat;omega) upper
  have frame:=GeneralBorrowFreshReadFrame.frame s.tree .wildcard (Size.ofBytes event.offset) (Size.ofBytes event.len) event.kind protections event.mode
  change result.tree={s.tree with locations:=result.tree.locations} at frame
  have geometry : Geometry result.tree primary extras := by
    rw [frame]
    exact ⟨s.geometry.roots,s.geometry.forest,s.geometry.depth,s.geometry.short,s.geometry.nodes,s.geometry.present⟩
  exact ⟨⟨result.tree,geometry,good.2.2.1,good.2.2.2.trans s.capacityEq,good.2.1⟩,rfl,good.1⟩

def run {capacity protections primary extras} (s : State capacity protections primary extras) :
    List (Event capacity)→State capacity protections primary extras
  | []=>s
  | event::rest=>run (build s event).state rest

inductive Trace {capacity protections primary extras} :
    State capacity protections primary extras→List (Event capacity)→State capacity protections primary extras→Prop where
  | nil (s) : Trace s [] s
  | cons (s event rest final) (completed : (operation s event).status=.Completed)
      (tail : Trace (build s event).state rest final) : Trace s (event::rest) final

/-- Every requested finite NONE Read/Write sequence executes the actual ranged
source visitor and forms reusable effective scalar/graph/cache data internally.
Lazy absent rows are allowed wherever their real default state is possible;
no future operation success, materialization or final profile is an input. -/
theorem run_trace {capacity protections primary extras}
    (s : State capacity protections primary extras) (events : List (Event capacity)) : Trace s events (run s events) := by
  induction events generalizing s with
  | nil => exact .nil s
  | cons event rest ih => exact .cons s event rest _ (build s event).completed (ih _)
end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafHistory
