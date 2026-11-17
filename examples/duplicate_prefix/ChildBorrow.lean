import Lean
import Miri.TreeBorrows.TreeState
import Miri.TreeBorrows.RetagPolicy

/-! Actual permission-policy and tag-map components used by Tree Borrows retagging. -/
namespace DuplicatePrefix.ChildBorrow

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.RetagPolicy

def fnEntryLocation : Tree.LocationState := ⟨.ReservedFrz false, true, .None⟩

/- Concrete root and fresh child tags for the duplicate-prefix retag fixture. -/
def rootTag : BorTag := BorTag.one
def childTag : BorTag := ⟨2, by decide⟩

def rootMap : UniKeyMap BorTag := ⟨#[(rootTag, ⟨0⟩)], #[]⟩

theorem root_map_insert_child :
    rootMap.insert childTag = .Inserted ⟨#[(rootTag, ⟨0⟩), (childTag, ⟨1⟩)], #[]⟩ ⟨1⟩ := by
  simp [rootMap, childTag, rootTag, BorTag.one, UniKeyMap.insert, UniKeyMap.get,
    UniIndex.ofNat?, UniIndex.toNat]

theorem root_tag_mapping (capacity : UInt64) :
    (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping = rootMap := by
  rfl

def fnEntryPolicy : NewPermission :=
  ⟨.ReservedFrz false, .ReservedFrz false, .ReservedFrz false,
    some .StrongProtector⟩

theorem mutable_fn_entry_policy_is_reserved :
    RetagPolicy.create ⟨true, true, false⟩ .Mutable .FnEntry
      ⟨false, false⟩ = some fnEntryPolicy := by
  decide

theorem mutable_fn_entry_initial_location (frozen : Bool) :
    RetagPolicy.initialLocationState fnEntryPolicy frozen =
      .ok fnEntryLocation := by
  cases frozen <;> rfl

#print axioms root_map_insert_child
#print axioms mutable_fn_entry_policy_is_reserved
#print axioms mutable_fn_entry_initial_location

end DuplicatePrefix.ChildBorrow
