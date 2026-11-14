import Lean

/-! Pinned rustc_trait_selection::traits::vtable::prepare_vtable_segments.
Keys must be fully normalized trait references, including all arguments.
Providers consume declaration material; own-entry eligibility is a separate
source algorithm, not a compiler vtable answer supplied to this traversal. -/
namespace Miri.Input.VTableSegments
inductive Segment (α : Type) where
  | metadata
  | ownEntries (traitRef : α) (emitVptr : Bool)
  deriving Repr, BEq
structure Providers (α : Type) where
  directSupertraits : α → Except String (Array α)
  hasOwnEntries : α → Except String Bool
private structure Frame (α : Type) where
  key : α
  emitVptr : Bool
  siblings : List α
private def nextUnvisited [BEq α] (visited : Array α) : List α → Option (α × List α)
  | [] => none
  | key::rest => if visited.contains key then nextUnvisited visited rest else some (key,rest)
private def hasEntries [BEq α] (provider : Providers α) (fuel : Nat) (key : α) :
    Except String Bool := do
  let mut seen := #[]
  let mut pending := [key]
  for _ in [:fuel] do
    let head::tail := pending | return false
    pending := tail
    if seen.contains head then continue
    seen := seen.push head
    if ← provider.hasOwnEntries head then return true
    pending := (← provider.directSupertraits head).toList ++ pending
  if pending.isEmpty then return false
  throw "vtable transitive-entry recursion exhausted"

def prepare [BEq α] (provider : Providers α) (fuel : Nat) (noTraitVptr : Bool) (root : α) :
    Except String (Array (Segment α)) := do
  let mut stack : List (Frame α) := [⟨root,false,[]⟩]
  let mut visited := #[root]
  let mut emitOnNewEntry := false
  let mut diving := true
  let mut result := #[Segment.metadata]
  for _ in [:fuel] do
    let frame::rest := stack | return result
    if diving then
      let supers ← provider.directSupertraits frame.key
      match nextUnvisited visited supers.toList with
      | some (next,siblings) =>
        visited := visited.push next
        stack := ⟨next,emitOnNewEntry,siblings⟩ :: stack
      | none => diving := false
    else
      stack := rest
      let hasEntries ← hasEntries provider fuel frame.key
      result := result.push (.ownEntries frame.key (frame.emitVptr && hasEntries && !noTraitVptr))
      emitOnNewEntry := emitOnNewEntry || hasEntries
      if let some (next,siblings) := nextUnvisited visited frame.siblings then
        visited := visited.push next
        stack := ⟨next,emitOnNewEntry,siblings⟩ :: stack
        diving := true
  if stack.isEmpty then return result
  throw "vtable segment traversal recursion exhausted"
end Miri.Input.VTableSegments
