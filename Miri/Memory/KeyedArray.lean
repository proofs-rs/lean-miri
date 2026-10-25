import Std

/-! Ordered metadata arrays with an exact key-to-row index.

The index stores only row positions, never values. Payloads therefore occur
once in the ordered rows. A certificate ties each index to those exact rows;
constructors and mutations rebuild both together. Iteration retains source
array order and duplicate-key lookup semantics. -/
namespace Miri.Memory

private def indexStep [BEq K] [Hashable K]
    (state : Nat × Std.HashMap K (Array Nat)) (key : K) : Nat × Std.HashMap K (Array Nat) :=
  (state.1 + 1, state.2.insert key ((state.2.getD key #[]).push state.1))

private def canonicalIndex [BEq K] [Hashable K] (keys : Array K) :
    Nat × Std.HashMap K (Array Nat) :=
  keys.foldl indexStep (0, {})

structure KeyedArray (K V : Type) (keyFn : V → K) [BEq K] [Hashable K] where
  private mk ::
  private keys : Array K
  private rows : Array V
  private indexState : Nat × Std.HashMap K (Array Nat)
  private exact : indexState = canonicalIndex keys
  private aligned : keys.size = rows.size
  private keysMatchRows : keys = rows.map keyFn

namespace KeyedArray

variable {K V : Type} [BEq K] [Hashable K] {keyFn : V → K}

def empty (keyFn : V → K) : KeyedArray K V keyFn :=
  ⟨#[], #[], (0, {}), by rfl, by rfl, by simp⟩

def ofArray (keyFn : V → K) (rows : Array V) : KeyedArray K V keyFn :=
  let keys := rows.map keyFn
  let indexState := canonicalIndex keys
  ⟨keys, rows, indexState, by rfl, by simp [keys], by rfl⟩

def keyOf (_table : KeyedArray K V keyFn) : V → K := keyFn

def toArray (table : KeyedArray K V keyFn) : Array V := table.rows

def toPairs (table : KeyedArray K V keyFn) : Array (K × V) := table.keys.zip table.rows

def find? (table : KeyedArray K V keyFn) (key : K) : Option V := do
  let indices ← table.indexState.2.get? key
  let rowIndex ← indices[0]?
  table.rows[rowIndex]?

/-- Test every same-key row, preserving the historical `Array.any` behavior
for deliberately constructed duplicate metadata keys. -/
def any? (table : KeyedArray K V keyFn) (key : K) (p : V → Bool) : Bool := Id.run do
  let some indices := table.indexState.2.get? key | return false
  for rowIndex in indices do
    if let some value := table.rows[rowIndex]? then
      if p value then return true
  return false

def valuesFor (table : KeyedArray K V keyFn) (key : K) : Array V := Id.run do
  let some indices := table.indexState.2.get? key | return #[]
  let mut values := #[]
  for rowIndex in indices do
    if let some value := table.rows[rowIndex]? then values := values.push value
  return values

def contains (table : KeyedArray K V keyFn) (key : K) : Bool := table.indexState.2.contains key

def isEmpty (table : KeyedArray K V keyFn) : Bool := table.rows.isEmpty

def size (table : KeyedArray K V keyFn) : Nat := table.rows.size

/-- Append while preserving first-row lookup and source iteration order. -/
def push (table : KeyedArray K V keyFn) (value : V) : KeyedArray K V keyFn :=
  let key := keyFn value
  let indexState := indexStep table.indexState key
  ⟨table.keys.push key, table.rows.push value, indexState, by
    dsimp [indexState]
    rw [table.exact]
    simp [canonicalIndex, indexStep]
  , by simpa using table.aligned, by simp [table.keysMatchRows, key]⟩

/-- Filter and reindex a cold metadata table. -/
def filter (table : KeyedArray K V keyFn) (keep : K → V → Bool) : KeyedArray K V keyFn :=
  ofArray keyFn (table.rows.filter fun row => keep (keyFn row) row)

/-- Map rows in source order and rebuild the index, allowing key changes. -/
def mapValues (table : KeyedArray K V keyFn) (f : V → V) : KeyedArray K V keyFn :=
  ofArray keyFn (table.rows.map f)

/-- Map row payloads, reusing the certified index when the mapped rows retain
the exact key sequence. A map that changes keys falls back to a full reindex,
so this preserves the unrestricted semantics of `mapValues`. -/
def mapValuesChecked [DecidableEq K] (table : KeyedArray K V keyFn) (f : V → V) :
    KeyedArray K V keyFn := Id.run do
  let rows := table.rows.map f
  let keys := rows.map keyFn
  if h : keys = table.keys then
    return ⟨table.keys, rows, table.indexState, table.exact,
      by simpa [rows] using table.aligned, h.symm⟩
  else
    return ofArray keyFn rows

private theorem map_modify_preserves (rows : Array V) (i : Nat) (f : V → V)
    (preserves : ∀ row, keyFn (f row) = keyFn row) :
    (rows.modify i f).map keyFn = rows.map keyFn := by
  rw [Array.map_eq_iff]
  intro j
  rw [Array.getElem?_modify]
  by_cases h : i = j
  · subst j
    cases hrow : rows[i]? with
    | none => simp [hrow]
    | some row => simp [hrow, preserves]
  · simp [h]

/-- Apply a key-preserving row update while retaining the certified key
sequence and index. The proof obligation is local to the update function. -/
def modifyAt (table : KeyedArray K V keyFn) (i : Nat) (f : V → V)
    (preserves : ∀ row, keyFn (f row) = keyFn row) : KeyedArray K V keyFn :=
  ⟨table.keys, table.rows.modify i f, table.indexState, table.exact,
    by simpa using table.aligned,
    by rw [map_modify_preserves table.rows i f preserves, table.keysMatchRows]⟩

/-- Update every row at a key's certified positions, retaining the existing
index. -/
def mapValuesForKey (table : KeyedArray K V keyFn) (key : K) (f : V → V)
    (preserves : ∀ row, keyFn (f row) = keyFn row) : KeyedArray K V keyFn := Id.run do
  let some indices := table.indexState.2.get? key | return table
  let mut result := table
  for rowIndex in indices do
    result := result.modifyAt rowIndex f preserves
  return result

end KeyedArray
end Miri.Memory
