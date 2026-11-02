import duplicate_prefix.GeneralBorrowForestForeignAccess

namespace DuplicatePrefix.GeneralBorrowForestForeignRepeated
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestForeignAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

abbrev Operation := ChildrenVisitMode × ByteRange

def step (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind)
    (operation : Operation) (location : LocationTree) : LocationTree :=
  source_access_location (source_tree_access_at tree location (some anchor) kind protections operation.1 operation.2)

def run (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) :
    List Operation → LocationTree → LocationTree
  | [], location => location
  | operation::rest, location => run tree protections anchor kind rest (step tree protections anchor kind operation location)

/-- Every actual call in the recursively executed source-operation sequence
has no access error. This is an output predicate, never a caller premise. -/
def Completed (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) :
    List Operation → LocationTree → Prop
  | [], _ => True
  | operation::rest, location =>
      source_access_status (source_tree_access_at tree location (some anchor) kind protections operation.1 operation.2) = none ∧
      Completed tree protections anchor kind rest (step tree protections anchor kind operation location)

/-- Arbitrarily many REAL source accesses in either visitor mode re-form all
next permission/region/cache records by induction. The graph and access kind
are fixed; this does not yet interleave constructors or lift the operation to
a partitioned range/MIR invocation. -/
theorem complete (tree : BorrowTree) (protections : ProtectedTags) (anchor primary : UniIndex)
    (extras : List UniIndex) (kind : AccessKind) (operations : List Operation)
    (context : Context tree anchor primary extras) (fits : tree.nodes.data.size ≤ 4294967296)
    (location : LocationTree) (data : LocationData tree location protections anchor primary extras kind) :
    Completed tree protections anchor kind operations location ∧
      Nonempty (LocationData tree (run tree protections anchor kind operations location) protections anchor primary extras kind) := by
  induction operations generalizing location with
  | nil => exact ⟨True.intro,⟨data⟩⟩
  | cons operation rest ih =>
    obtain ⟨status,⟨next⟩⟩ := GeneralBorrowForestForeignAccess.access tree location protections anchor primary extras kind
      operation.1 operation.2 context data fits
    obtain ⟨tail,finalData⟩ := ih (step tree protections anchor kind operation location) next
    exact ⟨⟨status,tail⟩,finalData⟩

end DuplicatePrefix.GeneralBorrowForestForeignRepeated
