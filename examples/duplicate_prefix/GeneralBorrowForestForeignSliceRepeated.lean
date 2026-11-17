import duplicate_prefix.GeneralBorrowForestForeignSlice
import duplicate_prefix.GeneralBorrowFreshReadFrame

namespace DuplicatePrefix.GeneralBorrowForestForeignSliceRepeated
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestForeignAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

structure Operation where
  offset : Size
  len : Size
  mode : ChildrenVisitMode

def step (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (kind : AccessKind) (operation : Operation) :=
  tree.performBorrowAccessRange (.concrete tag) operation.offset operation.len kind protections operation.mode

def run (protections : ProtectedTags) (tag : BorTag) (kind : AccessKind) : List Operation → BorrowTree → BorrowTree
  | [], tree => tree
  | operation::rest, tree => run protections tag kind rest (step tree protections tag kind operation).tree

def Completed (protections : ProtectedTags) (tag : BorTag) (kind : AccessKind) : List Operation → BorrowTree → Prop
  | [], _ => True
  | operation::rest, tree => (step tree protections tag kind operation).status = .Completed ∧
      Completed protections tag kind rest (step tree protections tag kind operation).tree

/-- Reindex the raw context after an arbitrary location-map replacement. -/
def context_on_map (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (anchor primary : UniIndex) (extras : List UniIndex) (context : Context tree anchor primary extras) :
    Context {tree with locations := locations} anchor primary extras where
  anchorNode := context.anchorNode
  primaryNode := context.primaryNode
  depth := context.depth
  children := context.children
  anchorPresent := context.anchorPresent
  primaryPresent := context.primaryPresent
  roots := context.roots
  different := context.different
  unexposed := context.unexposed

/-- Arbitrary finite repetition of REAL ranged source operations re-forms the
full slice-local next-input data after EVERY call. The same concrete source,
protection map and access kind are used; each operation may independently choose
its bounded subrange and either visitor mode. No outside-slice ownership or
operation-success premise is supplied. Constructors and MIR calls are separate. -/
theorem complete (protections : ProtectedTags) (tag : BorTag) (anchor primary : UniIndex)
    (extras : List UniIndex) (kind : AccessKind) (operations : List Operation)
    (sliceStart sliceStop : UInt64) (tree : BorrowTree)
    (context : Context tree anchor primary extras) (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed) (fits : tree.nodes.data.size ≤ 4294967296)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData tree location protections anchor primary extras kind)) sliceStart sliceStop tree.locations)
    (requests : ∀ operation ∈ operations,
      operation.offset.bytes.toNat+operation.len.bytes.toNat ≤ tree.locations.size.bytes.toNat ∧
      sliceStart.toNat ≤ operation.offset.bytes.toNat ∧
      (operation.offset.bytes+operation.len.bytes).toNat ≤ sliceStop.toNat) :
    Completed protections tag kind operations tree ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData (run protections tag kind operations tree) location protections anchor primary extras kind))
      sliceStart sliceStop (run protections tag kind operations tree).locations ∧
    (run protections tag kind operations tree).locations.WellFormed ∧
    (run protections tag kind operations tree).locations.size = tree.locations.size := by
  induction operations generalizing tree with
  | nil => exact ⟨True.intro,owned,well,rfl⟩
  | cons operation rest ih =>
    have request := requests operation (by simp)
    have good := GeneralBorrowForestForeignSlice.access tree protections tag anchor primary extras operation.offset operation.len kind operation.mode
      context tagPresent well fits sliceStart sliceStop owned request.1 request.2.1 request.2.2
    let accessed := step tree protections tag kind operation
    change accessed.status = .Completed ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (LocationData accessed.tree location protections anchor primary extras kind))
        sliceStart sliceStop accessed.tree.locations ∧
      accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
    have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) operation.offset operation.len kind protections operation.mode
    change accessed.tree = {tree with locations := accessed.tree.locations} at frame
    have nextContext : Context accessed.tree anchor primary extras := by
      rw [frame]
      exact context_on_map tree _ anchor primary extras context
    have nextTag : accessed.tree.indexOfTag tag = some anchor := by rw [frame];exact tagPresent
    have nextFits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [frame];exact fits
    have nextRequests : ∀ item ∈ rest,
        item.offset.bytes.toNat+item.len.bytes.toNat ≤ accessed.tree.locations.size.bytes.toNat ∧
        sliceStart.toNat ≤ item.offset.bytes.toNat ∧
        (item.offset.bytes+item.len.bytes).toNat ≤ sliceStop.toNat := by
      intro item member
      rw [good.2.2.2]
      exact requests item (by simp [member])
    obtain ⟨tail,finalOwners,finalWell,capacity⟩ := ih accessed.tree nextContext nextTag good.2.2.1 nextFits good.2.1 nextRequests
    exact ⟨⟨good.1,tail⟩,finalOwners,finalWell,capacity.trans good.2.2.2⟩

end DuplicatePrefix.GeneralBorrowForestForeignSliceRepeated
