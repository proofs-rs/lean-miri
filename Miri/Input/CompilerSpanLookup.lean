import Miri.Input.Model.Types
import Std.Data.HashMap.Lemmas

/-! Exact first-match source positions. Preparation builds a hash index once;
numeric bounds are only bucket keys and the complete original comparator remains
decisive. Kernel theorems equate both indexed and fallback paths with the original
list lookup, including duplicate order and missing values. -/
namespace Miri.Input.CompilerSpanLookup

private def sameSpan (a b : SourceSpanData) : Bool :=
  if a.lo == b.lo && a.hi == b.hi then
    withPtrEq a b (fun _ => a == b) (by intro same; subst b; exact beq_self_eq_true a)
  else false

private theorem sameSpan_eq (a b : SourceSpanData) : sameSpan a b = (a == b) := by
  unfold sameSpan
  split
  · rfl
  · rename_i different
    symm
    apply beq_eq_false_iff_ne.mpr
    intro same
    subst b
    simp at different

private theorem comparator_eq : (⟨sameSpan⟩ : BEq SourceSpanData) = (inferInstance : BEq SourceSpanData) := by
  have same : sameSpan = (fun a b : SourceSpanData => a == b) := by
    funext a b
    exact sameSpan_eq a b
  exact congrArg BEq.mk same

/-- Return the first completely equal span, including original payload, source
positions, hygiene context and filename. Missing spans remain missing. -/
def find (spans : Array SourceSpanData) (wanted : SourceSpanData) : Option Nat :=
  @Array.idxOf? SourceSpanData ⟨sameSpan⟩ spans wanted

@[simp] theorem find_eq (spans : Array SourceSpanData) (wanted : SourceSpanData) :
    find spans wanted = spans.toList.idxOf? wanted := by
  unfold find
  rw [comparator_eq]
  simpa using (List.idxOf?_toArray wanted spans.toList)



/-- Hash collisions retain the complete span comparison. -/
private structure Key where
  span : SourceSpanData
  deriving DecidableEq
private instance : BEq Key where
  beq a b := sameSpan a.span b.span
private instance : LawfulBEq Key where
  rfl := by intro a; change sameSpan a.span a.span = true; rw [sameSpan_eq]; simp
  eq_of_beq := by
    intro a b h
    have same : a.span = b.span := eq_of_beq (by
      change sameSpan a.span b.span = true at h
      rwa [sameSpan_eq] at h)
    cases a; cases b; cases same; rfl
private instance : Hashable Key where
  hash key := mixHash (hash key.span.lo) (hash key.span.hi)
private def build (pairs : List (Key × Nat)) : Std.HashMap Key Nat :=
  pairs.foldr (fun (key, id) table => table.insert key id) {}
private theorem build_lookup (pairs : List (Key × Nat)) (key : Key) :
    (build pairs)[key]? = pairs.lookup key := by
  induction pairs with
  | nil => simp [build]
  | cons pair rest ih =>
    rcases pair with ⟨k,v⟩
    simp only [build, List.foldr_cons, Std.HashMap.getElem?_insert, List.lookup_cons]
    change (if k == key then some v else (build rest)[key]?) = _
    rw [ih, (BEq.comm (a := k) (b := key))]
    cases key == k <;> simp
private def entries (spans : List SourceSpanData) (offset : Nat) : List (Key × Nat) :=
  (spans.zipIdx offset).map fun (span, id) => (⟨span⟩, id)
private theorem entries_lookup (spans : List SourceSpanData) (offset : Nat) (wanted : SourceSpanData) :
    (entries spans offset).lookup (⟨wanted⟩ : Key) = (spans.idxOf? wanted).map (offset + ·) := by
  induction spans generalizing offset with
  | nil => simp [entries]
  | cons span rest ih =>
    simp only [entries, List.zipIdx_cons, List.map_cons, List.lookup_cons]
    change (match sameSpan wanted span with | true => some offset | false => (entries rest (offset + 1)).lookup (⟨wanted⟩ : Key)) = _
    rw [ih, sameSpan_eq, (BEq.comm (a := wanted) (b := span)), List.idxOf?_cons]
    split <;> simp_all [Option.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]
/-- The exact table is part of the type: a provider cannot retain this index
after replacing its canonical spans. Building from right to left preserves the
first index when the input contains fully equal duplicates. -/
structure Prepared (spans : Array SourceSpanData) where
  private mk ::
  private table : Std.HashMap Key Nat
  private exact : table = build (entries spans.toList 0)
/-- Build once after all compiler preparation has finished interning spans. -/
def prepare (spans : Array SourceSpanData) : Prepared spans :=
  ⟨build (entries spans.toList 0), rfl⟩
def Prepared.find {spans : Array SourceSpanData} (prepared : Prepared spans) (wanted : SourceSpanData) : Option Nat :=
  prepared.table[(⟨wanted⟩ : Key)]?
@[simp] theorem Prepared.find_eq {spans : Array SourceSpanData} (prepared : Prepared spans) (wanted : SourceSpanData) :
    prepared.find wanted = spans.toList.idxOf? wanted := by
  unfold Prepared.find
  rw [prepared.exact, build_lookup, entries_lookup]
  simp

/-- Publicly assembled providers may omit the index. Both paths preserve the
same first full match, including duplicate spans and all source metadata. -/
def findUsing (spans : Array SourceSpanData) (prepared : Option (Prepared spans))
    (wanted : SourceSpanData) : Option Nat :=
  match prepared with
  | some cache => cache.find wanted
  | none => find spans wanted
@[simp] theorem findUsing_eq (spans : Array SourceSpanData) (prepared : Option (Prepared spans))
    (wanted : SourceSpanData) : findUsing spans prepared wanted = spans.toList.idxOf? wanted := by
  cases prepared <;> simp [findUsing]
end Miri.Input.CompilerSpanLookup
