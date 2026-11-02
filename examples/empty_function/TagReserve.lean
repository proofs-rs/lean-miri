import Miri.TreeBorrows.GlobalState
import Lean

namespace EmptyFunction.TagReserve
open Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A finite set represented without imposing any numeric bound on its IDs. -/
def distinct : List AllocId → List AllocId
  | [] => []
  | id :: rest => if id ∈ distinct rest then distinct rest else id :: distinct rest

@[simp] theorem mem_distinct (id : AllocId) (ids : List AllocId) :
    id ∈ distinct ids ↔ id ∈ ids := by
  induction ids generalizing id with
  | nil => simp [distinct]
  | cons first rest ih =>
    simp only [distinct]
    split <;> simp_all

 theorem distinct_nodup (ids : List AllocId) : (distinct ids).Nodup := by
  induction ids with
  | nil => simp [distinct]
  | cons first rest ih => simp only [distinct]; split <;> simp_all

/-- Only distinct IDs absent from the current root-tag cache consume tags.
This includes TypeId IDs: their address path is special, their root-tag path is not. -/
def rootNeed (global : GlobalState) (ids : List AllocId) : Nat :=
  (distinct ids).countP (fun id => (global.rootTag? id).isNone)

@[simp] theorem rootNeed_nil (global : GlobalState) : rootNeed global [] = 0 := rfl

private theorem count_remove (xs : List AllocId) (unique : xs.Nodup)
    (p : AllocId → Bool) (id : AllocId) :
    xs.countP p = (if id ∈ xs ∧ p id = true then 1 else 0) +
      xs.countP (fun other => decide (other ≠ id) && p other) := by
  induction xs with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨absent,restUnique⟩ := List.nodup_cons.mp unique
    have tail := ih restUnique
    by_cases same : first = id
    · subst first
      have eq : rest.countP (fun other => decide (other ≠ id) && p other) = rest.countP p := by
        apply List.countP_congr
        intro other member
        have different : other ≠ id := by intro equal; subst other; exact absent member
        simp [different]
      simp only [List.countP_cons]
      rw [eq]
      simp [absent,Nat.add_comm]
    · simp only [List.countP_cons]
      by_cases member : id ∈ rest <;> cases hp : p id <;> cases hf : p first <;>
        simp [same,Ne.symm same,member,hp] at tail ⊢ <;> omega

 theorem rootNeed_cached_congr (before after : GlobalState) (ids : List AllocId)
    (same : ∀ id ∈ ids, (after.rootTag? id).isNone = (before.rootTag? id).isNone) :
    rootNeed after ids = rootNeed before ids := by
  apply List.countP_congr
  intro id member
  rw [same id ((mem_distinct id ids).mp member)]

 theorem rootNeed_insert (before after : GlobalState) (ids : List AllocId) (id : AllocId)
    (cache : ∀ other, (after.rootTag? other).isNone =
      (decide (other ≠ id) && (before.rootTag? other).isNone)) :
    rootNeed before ids =
      (if id ∈ ids ∧ before.rootTag? id = none then 1 else 0) + rootNeed after ids := by
  have counted := count_remove (distinct ids) (distinct_nodup ids)
    (fun other => (before.rootTag? other).isNone) id
  have eq : (distinct ids).countP (fun other => decide (other ≠ id) &&
      (before.rootTag? other).isNone) = rootNeed after ids := by
    apply List.countP_congr
    intro other _
    rw [cache]
  simpa only [rootNeed,mem_distinct,Option.isNone_iff_eq_none,eq] using counted

 theorem rootNeed_pos (global : GlobalState) (ids : List AllocId) (id : AllocId)
    (member : id ∈ ids) (missing : global.rootTag? id = none) : 0 < rootNeed global ids := by
  apply List.countP_pos_iff.mpr
  exact ⟨id,(mem_distinct id ids).mpr member,by simp [missing]⟩

private theorem new_tag (global : GlobalState)
    (room : global.nextPointerTag.value.toNat + 1 < 2^64) :
    ∃ after, global.newPointerTag = .ok (after,global.nextPointerTag) ∧
      after.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat + 1 ∧
      after.rootPointerTags = global.rootPointerTags ∧
      after.protectedTags = global.protectedTags ∧
      after.trackedPointerTags = global.trackedPointerTags := by
  have notMax : global.nextPointerTag.value ≠ 18446744073709551615 := by
    intro maximum
    rw [maximum] at room
    contradiction
  have nonzero : global.nextPointerTag.value + 1 ≠ 0 := by
    intro zero
    have actual : (global.nextPointerTag.value+1).toNat = global.nextPointerTag.value.toNat+1 := by
      rw [UInt64.toNat_add]
      change (global.nextPointerTag.value.toNat+1) % 2^64 = _
      exact Nat.mod_eq_of_lt room
    rw [zero] at actual
    change 0 = _ at actual
    omega
  let successor : BorTag := ⟨global.nextPointerTag.value+1,nonzero⟩
  refine ⟨{global with nextPointerTag := successor},?_,?_,rfl,rfl,rfl⟩
  · simp [GlobalState.newPointerTag,BorTag.succ,notMax,BorTag.ofUInt64,nonzero,successor]
  · change (global.nextPointerTag.value+1).toNat = _
    rw [UInt64.toNat_add]
    change (global.nextPointerTag.value.toNat+1) % 2^64 = _
    exact Nat.mod_eq_of_lt room

/-- Reserving the entry retag consumes exactly one tag and does not change the
root demand. Whole-local immediates do not take this operation. -/
 theorem child (global : GlobalState) (ids : List AllocId)
    (room : global.nextPointerTag.value.toNat + 1 + rootNeed global ids < 2^64) :
    ∃ after, global.newPointerTag = .ok (after,global.nextPointerTag) ∧
      after.nextPointerTag.value.toNat + rootNeed after ids =
        global.nextPointerTag.value.toNat + 1 + rootNeed global ids ∧
      after.rootPointerTags = global.rootPointerTags ∧
      after.protectedTags = global.protectedTags ∧
      after.trackedPointerTags = global.trackedPointerTags := by
  obtain ⟨after,actual,next,cache,protectors,tracked⟩ := new_tag global (by omega)
  have need : rootNeed after ids = rootNeed global ids := by
    apply rootNeed_cached_congr
    intro id _
    simp only [GlobalState.rootTag?,cache]
  exact ⟨after,actual,by rw [next,need],cache,protectors,tracked⟩

/-- Actual cache lookup/insertion consumes the one demand for this ID. Cached
requests cost zero, and repeated requests therefore do not reserve extra tags. -/
 theorem root (global : GlobalState) (ids : List AllocId) (id : AllocId)
    (member : id ∈ ids)
    (room : global.nextPointerTag.value.toNat + rootNeed global ids < 2^64) :
    ∃ after tag, global.rootPointerTag id = .ok (after,tag) ∧
      after.rootTag? id = some tag ∧
      after.nextPointerTag.value.toNat + rootNeed after ids =
        global.nextPointerTag.value.toNat + rootNeed global ids ∧
      after.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat +
        (if global.rootTag? id = none then 1 else 0) ∧
      rootNeed global ids = (if global.rootTag? id = none then 1 else 0) + rootNeed after ids ∧
      after.protectedTags = global.protectedTags ∧
      after.trackedPointerTags = global.trackedPointerTags := by
  cases cached : global.rootTag? id with
  | some tag =>
    exact ⟨global,tag,GlobalState.rootPointerTag_existing global id tag cached,cached,rfl,by simp [cached],by simp [cached],rfl,rfl⟩
  | none =>
    have positive := rootNeed_pos global ids id member cached
    obtain ⟨next,created,counter,cache,protectors,tracked⟩ := new_tag global (by omega)
    let after : GlobalState := {next with rootPointerTags := next.rootPointerTags.push (id,global.nextPointerTag)}
    have actual : global.rootPointerTag id = .ok (after,global.nextPointerTag) := by
      simp [GlobalState.rootPointerTag,cached,created,after,bind,Except.bind,pure,Except.pure]
    have missing : global.rootPointerTags.find? (fun row => row.1 == id) = none := by
      simpa only [GlobalState.rootTag?,Option.map_eq_none_iff] using cached
    have cacheAfter : ∀ other, (after.rootTag? other).isNone =
        (decide (other ≠ id) && (global.rootTag? other).isNone) := by
      intro other
      by_cases equal : other = id
      · subst other
        simp [after,GlobalState.rootTag?,cache,Array.find?_push,missing]
      · simp only [after,GlobalState.rootTag?,cache,Array.find?_push]
        cases found : global.rootPointerTags.find? (fun row => row.1 == other) with
        | none => simp [equal,Ne.symm equal]
        | some row => simp [equal]
    have count := rootNeed_insert global after ids id cacheAfter
    simp only [member,cached,and_self,↓reduceIte] at count
    have lookup : after.rootTag? id = some global.nextPointerTag := by
      simp [after,GlobalState.rootTag?,cache,Array.find?_push,missing]
    refine ⟨after,global.nextPointerTag,actual,lookup,?_,?_,?_,protectors,tracked⟩
    · change next.nextPointerTag.value.toNat + rootNeed after ids = _
      omega
    · simpa only [after,cached,↓reduceIte] using counter
    · simpa only [cached,↓reduceIte] using count

/-- Counter/cache consumers may interleave protector bookkeeping without
changing their outstanding root reserve. -/
 theorem rootNeed_of_rootPointerTags (before after : GlobalState) (ids : List AllocId)
    (cache : after.rootPointerTags = before.rootPointerTags) :
    rootNeed after ids = rootNeed before ids := by
  apply rootNeed_cached_congr
  intro id _
  simp only [GlobalState.rootTag?,cache]

@[simp] theorem rootNeed_singleton (global : GlobalState) (id : AllocId) :
    rootNeed global [id] = if global.rootTag? id = none then 1 else 0 := by
  simp [rootNeed,distinct,List.countP_cons]

/-- New enclosing stack storage always needs one root tag, irrespective of
its byte length. Cache freshness itself follows from allocation-ID freshness. -/
 theorem singleton_missing (global : GlobalState) (id : AllocId)
    (missing : global.rootTag? id = none)
    (room : global.nextPointerTag.value.toNat + 1 < 2^64) :
    ∃ after tag, global.rootPointerTag id = .ok (after,tag) ∧
      after.rootTag? id = some tag ∧
      after.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat + 1 := by
  obtain ⟨after,tag,actual,lookup,_,cost,_⟩ := root global [id] id (by simp)
    (by simpa [missing] using room)
  exact ⟨after,tag,actual,lookup,by simpa only [missing,↓reduceIte] using cost⟩

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.TagReserve." ||
        (name.toString.startsWith "_private." && name.toString.contains "TagReserve") then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved tag reserve axiom {dependency} in {name}"
  logInfo m!"Audited {total} tag reserve declarations"

#print axioms root
#print axioms child
#print axioms singleton_missing
end EmptyFunction.TagReserve
