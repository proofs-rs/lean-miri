import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFold

namespace DuplicatePrefix.GeneralBorrowVirtualRootsAdapter
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
abbrev State := LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool

/-- The exact source root-loop callback after concrete-root selection and
VisitChildrenOfAccessed have been reduced. -/
def scan (tree : BorrowTree) (primary : UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (root : UniIndex) (state : State) : Id (ForInStep State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    if primary = root then .yield state else
      let first := tree.performWildcardAccessAt state.1 root (some maximum) kind protections true
      if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
      else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

theorem forIn_congr {α β : Type} (items : List α)
    (f g : α → β → Id (ForInStep β))
    (same : ∀ item ∈ items, ∀ state, f item state = g item state) (initial : β) :
    forIn items initial f = forIn items initial g := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons,List.forIn_cons,same item (by simp) initial]
    cases outcome : g item initial <;> simp only [outcome,bind,pure]
    exact ih (fun x member => same x (by simp [member])) _

theorem index_map (primary : UniIndex) (extras : List UniIndex) :
    (List.range' 1 extras.length).map (fun pos => (primary::extras)[pos]!) = extras := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul]
    rw [Nat.add_comm 1 index,List.getElem!_cons_succ]
    exact getElem!_pos extras index right

/-- Indexed form of the actual source callback, before converting the roots
array positions to direct root iteration. -/
def scanAt (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (position : Nat) (state : State) : Id (ForInStep State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    match (primary :: extras)[position]? with
    | none => .yield state
    | some root =>
      if primary = root then .yield state else
        let first := tree.performWildcardAccessAt state.1 root (some maximum) kind protections (position != 0)
        if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
        else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

/-- Exact conversion, including failure/stopped states, of all nonzero source
root positions to direct iteration over the extra roots. -/
theorem indexed (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange) (initial : State) :
    forIn (List.range' 1 extras.length) initial (scanAt tree primary extras maximum kind protections range) =
      forIn extras initial (scan tree primary maximum kind protections range) := by
  calc
    _ = forIn (List.range' 1 extras.length) initial
        (fun pos state => scan tree primary maximum kind protections range (primary::extras)[pos]! state) := by
      apply forIn_congr
      intro pos member state
      obtain ⟨index,bound,position⟩ := List.mem_range'.mp member
      have positionEq : pos = index+1 := by omega
      subst pos
      have selected : (primary::extras)[index+1]? = some extras[index] := by
        simp only [List.getElem?_cons_succ,List.getElem?_eq_getElem bound]
      simp only [scanAt,Nat.one_mul,Nat.add_comm 1 index,selected,show (index+1 != 0) = true from by simp,
        scan,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]
    _ = forIn ((List.range' 1 extras.length).map (fun pos => (primary::extras)[pos]!)) initial
        (scan tree primary maximum kind protections range) := List.forIn_map.symm
    _ = _ := by rw [index_map]

/-- Exact successful-path equality to the frozen adapter. This is an internal
bridge; the public interpreter theorem derives its success premise from data. -/
theorem successful (tree : BorrowTree) (primary : UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (extras : List UniIndex) (different : ∀ root ∈ extras, root ≠ primary)
    (location after : LocationTree)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras location (some maximum) kind protections = ⟨after,.Completed⟩) :
    forIn extras (location,none,false) (scan tree primary maximum kind protections range) = (after,none,false) := by
  induction extras generalizing location with
  | nil =>
    cases completed
    rfl
  | cons root rest ih =>
    have ne : primary ≠ root := Ne.symm (different root (by simp))
    let first := tree.performWildcardAccessAt location root (some maximum) kind protections true
    have good : first.status = .Completed := by
      simp only [GeneralBorrowWildcardVirtualLeafFold.run] at completed
      try dsimp only at completed
      split at completed
      · exact of_decide_eq_true ‹_ = true›
      · have status := congrArg BorrowTree.WildcardLocationAccessResult.status completed
        simp_all [first]
    have tail : GeneralBorrowWildcardVirtualLeafFold.run tree rest first.location (some maximum) kind protections = ⟨after,.Completed⟩ := by
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,show (tree.performWildcardAccessAt location root (some maximum) kind protections true).status = .Completed from good,
        beq_self_eq_true,↓reduceIte] using completed
    rw [List.forIn_cons]
    simp only [scan,show ((none : Option BorrowTree.BorrowTreeAccessStatus) = none ∧ false = false) from ⟨rfl,rfl⟩,
      ↓reduceIte,ne,show (tree.performWildcardAccessAt location root (some maximum) kind protections true).status = .Completed from good,
      bind,pure]
    exact ih (fun query member => different query (by simp [member])) first.location tail

end DuplicatePrefix.GeneralBorrowVirtualRootsAdapter
