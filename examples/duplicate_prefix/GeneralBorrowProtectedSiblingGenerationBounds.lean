import duplicate_prefix.TypedRetagEmpty
import duplicate_prefix.GeneralBorrowTagMap
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationBounds
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def KeysBelow (map : UniKeyMap BorTag) (bound : Nat) : Prop := ∀ row ∈ map.mapping,row.1.value.toNat < bound
def ProtectedBelow (tags : ProtectedTags) (bound : Nat) : Prop := ∀ row ∈ tags.entries,row.1.value.toNat < bound

theorem successor_nat (tag : BorTag) (room : tag.value < 18446744073709551615) :
    (TypedRetagEmpty.successorTag tag room).value.toNat = tag.value.toNat+1 := by
  have bounded : tag.value.toNat < 18446744073709551615 := by simpa [UInt64.lt_iff_toNat_lt] using room
  change (tag.value+1).toNat = _
  rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega)]

theorem map_fresh (map : UniKeyMap BorTag) (bound : Nat) (keys : KeysBelow map bound)
    (tag : BorTag) (above : bound ≤ tag.value.toNat) : GeneralBorrowTagMap.Fresh map tag := by
  intro row member same
  have smaller := keys row member
  rw [same] at smaller
  omega

theorem unheld (tags : ProtectedTags) (bound : Nat) (keys : ProtectedBelow tags bound)
    (tag : BorTag) (above : bound ≤ tag.value.toNat) : tags.get tag = none := by
  have absent : tags.entries.find? (fun row => row.1 == tag) = none := by
    apply Array.find?_eq_none.mpr
    intro row member
    have different : row.1 ≠ tag := by intro same;have smaller := keys row member;rw [same] at smaller;omega
    simpa only [beq_iff_eq] using different
  simp only [ProtectedTags.get,absent,Option.map_none]

theorem map_push (map : UniKeyMap BorTag) (bound next : Nat) (keys : KeysBelow map bound)
    (tag : BorTag) (index : UniIndex) (free : Array UniIndex) (tagBound : tag.value.toNat < next) (increasing : bound ≤ next) :
    KeysBelow ⟨map.mapping.push (tag,index),free⟩ next := by
  intro row member
  simp only [Array.mem_push] at member
  rcases member with old | same
  · exact Nat.lt_of_lt_of_le (keys row old) increasing
  · subst row;exact tagBound

theorem protected_insert (tags : ProtectedTags) (bound next : Nat) (keys : ProtectedBelow tags bound)
    (tag : BorTag) (kind : ProtectorKind) (tagBound : tag.value.toNat < next) (increasing : bound ≤ next) :
    ProtectedBelow (tags.insert tag kind) next := by
  intro row member
  change row ∈ (tags.remove tag).entries.push (tag,kind) at member
  simp only [Array.mem_push] at member
  rcases member with old | same
  · have original : row ∈ tags.entries := (Array.mem_filter.mp old).1
    exact Nat.lt_of_lt_of_le (keys row original) increasing
  · subst row;exact tagBound
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationBounds
