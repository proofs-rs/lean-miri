import duplicate_prefix.GeneralBorrowNodeUpdate
namespace DuplicatePrefix.GeneralBorrowTagMap
open Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def Fresh (mapping : UniKeyMap BorTag) (tag : BorTag) : Prop :=
  ∀ entry ∈ mapping.mapping, entry.1 ≠ tag

theorem fresh_find (mapping : UniKeyMap BorTag) (tag : BorTag) (fresh : Fresh mapping tag) :
    (mapping.mapping.find? fun entry => entry.1 == tag) = none := by
  apply Array.find?_eq_none.mpr
  intro entry member
  simpa only [beq_iff_eq] using fresh entry member

theorem fresh_filter (mapping : UniKeyMap BorTag) (tag : BorTag) (fresh : Fresh mapping tag) :
    mapping.mapping.filter (fun entry => entry.1 != tag) = mapping.mapping := by
  apply Array.filter_eq_self.mpr
  intro entry member
  simpa using fresh entry member

theorem insert_free (mapping : UniKeyMap BorTag) (tag : BorTag) (fresh : Fresh mapping tag)
    (index : UniIndex) (available : mapping.deassigned.back? = some index) :
    mapping.insert tag = .Inserted {mapping := mapping.mapping.push (tag,index),deassigned := mapping.deassigned.pop} index := by
  simp [UniKeyMap.insert,available,UniKeyMap.get,fresh_find mapping tag fresh,fresh_filter mapping tag fresh,Id.run,bind,pure]

theorem insert_append (mapping : UniKeyMap BorTag) (tag : BorTag) (fresh : Fresh mapping tag)
    (noFree : mapping.deassigned.back? = none) (fits : mapping.mapping.size ≤ 4294967295) :
    mapping.insert tag = .Inserted {mapping := mapping.mapping.push (tag,⟨UInt32.ofNat mapping.mapping.size⟩),deassigned := mapping.deassigned}
      ⟨UInt32.ofNat mapping.mapping.size⟩ := by
  simp [UniKeyMap.insert,noFree,UniIndex.ofNat?,fits,UniKeyMap.get,
    fresh_find mapping tag fresh,fresh_filter mapping tag fresh,Id.run,bind,pure]

theorem insert_success (mapping : UniKeyMap BorTag) (tag : BorTag) (fresh : Fresh mapping tag)
    (room : mapping.deassigned.back? = none → mapping.mapping.size ≤ 4294967295) :
    ∃ next index, mapping.insert tag = .Inserted next index := by
  cases available : mapping.deassigned.back? with
  | some index => exact ⟨_,index,insert_free mapping tag fresh index available⟩
  | none => exact ⟨_,_,insert_append mapping tag fresh available (room available)⟩

theorem pushed_get_new (mapping : UniKeyMap BorTag) (tag : BorTag) (fresh : Fresh mapping tag)
    (index : UniIndex) (pool : Array UniIndex) :
    (⟨mapping.mapping.push (tag,index),pool⟩ : UniKeyMap BorTag).get tag = some index := by
  simp [UniKeyMap.get,Array.find?_push,fresh_find mapping tag fresh]

theorem pushed_get_old (mapping : UniKeyMap BorTag) (tag query : BorTag) (different : tag ≠ query)
    (index : UniIndex) (pool : Array UniIndex) :
    (⟨mapping.mapping.push (tag,index),pool⟩ : UniKeyMap BorTag).get query = mapping.get query := by
  simp [UniKeyMap.get,Array.find?_push,different]
end DuplicatePrefix.GeneralBorrowTagMap

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTagMap." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic fresh-tag map dependency {dependency}"
