import Lean
import Miri.TreeBorrows.TreeState
namespace DuplicatePrefix.GeneralBorrowBoundedRelatedness
open Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Select the exact u16 field used by pinned Miri wildcard.rs:98-101. -/
def count (state : ExposedCacheNode) (kind : AccessKind) : UInt16 :=
  match kind with
  | .Read => state.localReads
  | .Write => state.localWrites

/-- Pinned Miri wildcard.rs:114-143, retaining u16 comparisons and the final
only-foreign clamp. This is a client-side source adapter, not new semantics. -/
def rustClassify (total localCount : UInt16) (onlyForeign : Bool) : Option WildcardAccessRelatedness :=
  let relatedness :=
    if total == 0 then none
    else if total == localCount then some .LocalAccess
    else if localCount == 0 then some .ForeignAccess
    else some .EitherAccess
  if onlyForeign then
    match relatedness with
    | some .LocalAccess | none => none
    | some .ForeignAccess | some .EitherAccess => some .ForeignAccess
  else relatedness

/-- The fixed Lean classifier after conversion to Nat. -/
def classify (total localCount : Nat) (onlyForeign : Bool) : Option WildcardAccessRelatedness :=
  let relatedness :=
    if total == 0 then none
    else if total == localCount then some .LocalAccess
    else if localCount == 0 then some .ForeignAccess
    else some .EitherAccess
  if onlyForeign then
    match relatedness with
    | some .LocalAccess | none => none
    | some .ForeignAccess | some .EitherAccess => some .ForeignAccess
  else relatedness

/-- Conversion is injective, so all u16 comparisons have the same outcome
before or after conversion; this fact does not require counter headroom. -/
theorem classify_u16 (total localCount : UInt16) (onlyForeign : Bool) :
    rustClassify total localCount onlyForeign = classify total.toNat localCount.toNat onlyForeign := by
  simp only [rustClassify,classify,beq_iff_eq,←UInt16.toNat_inj,UInt16.toNat_zero]

/-- Exact unchecked-Rust arithmetic expression from pinned wildcard.rs:111.
The only source difference from fixed Lean is addition before conversion.
Under the explicit no-overflow condition below this also describes the checked
Rust addition, which has no overflow panic on these arguments. -/
def rustAccessRelatedness (cache : ExposedCache) (root id : UniIndex)
    (kind : AccessKind) (isWildcardTree onlyForeign : Bool) : Option WildcardAccessRelatedness :=
  let rootState := (cache.nodes.get root).getD {}
  let nodeState := (cache.nodes.get id).getD {}
  rustClassify (count rootState kind + if isWildcardTree then 1 else 0)
    (count nodeState kind) onlyForeign

/-- Numerical precondition for the actual root's virtual-root addition. No
claim that an arbitrary pre-existing cache satisfies it is implicit. -/
def NoOverflow (cache : ExposedCache) (root : UniIndex) (kind : AccessKind) (isWildcardTree : Bool) : Prop :=
  (count ((cache.nodes.get root).getD {}) kind).toNat + (if isWildcardTree then 1 else 0) < 65536

theorem total_toNat (value : UInt16) (isWildcardTree : Bool)
    (bounded : value.toNat + (if isWildcardTree then 1 else 0) < 65536) :
    (value + (if isWildcardTree then 1 else 0 : UInt16)).toNat =
      value.toNat + (if isWildcardTree then 1 else 0) := by
  cases isWildcardTree with
  | false => simp
  | true =>
    change (value+1).toNat = value.toNat+1
    rw [UInt16.toNat_add]
    simp only [UInt16.toNat_one]
    exact Nat.mod_eq_of_lt bounded

/-- Under root counter headroom the fixed Lean operation agrees exactly with
pinned Rust's u16 expression, for both access kinds, both virtual flags, any
node counts and either only-foreign mode. This is operation-level agreement,
not a whole-Miri equivalence or a Rust-history formation theorem. -/
theorem accessRelatedness_eq_rust (cache : ExposedCache) (root id : UniIndex)
    (kind : AccessKind) (isWildcardTree onlyForeign : Bool)
    (bounded : NoOverflow cache root kind isWildcardTree) :
    cache.accessRelatedness root id kind isWildcardTree onlyForeign =
      rustAccessRelatedness cache root id kind isWildcardTree onlyForeign := by
  have total := total_toNat (count ((cache.nodes.get root).getD {}) kind) isWildcardTree bounded
  unfold rustAccessRelatedness
  rw [classify_u16,total]
  cases kind <;> rfl

/-- Non-virtual roots need no extra premise: every u16 value is representable. -/
theorem nonvirtual (cache : ExposedCache) (root id : UniIndex) (kind : AccessKind) (onlyForeign : Bool) :
    cache.accessRelatedness root id kind false onlyForeign = rustAccessRelatedness cache root id kind false onlyForeign := by
  apply accessRelatedness_eq_rust
  simpa only [NoOverflow,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using
    (count ((cache.nodes.get root).getD {}) kind).toNat_lt

/-- The exact virtual-root headroom excludes the 65535 endpoint. A raw
exposure count of 65535 is below 65536 but its virtual +1 is not representable. -/
theorem virtual_iff (cache : ExposedCache) (root : UniIndex) (kind : AccessKind) :
    NoOverflow cache root kind true ↔ (count ((cache.nodes.get root).getD {}) kind).toNat < 65535 := by
  simp only [NoOverflow,↓reduceIte]
  omega

/-- Convenient agreement statement when a history protocol has established a
strict bound for the root counter itself. -/
theorem virtual_of_count_lt (cache : ExposedCache) (root id : UniIndex) (kind : AccessKind) (onlyForeign : Bool)
    (bounded : (count ((cache.nodes.get root).getD {}) kind).toNat < 65535) :
    cache.accessRelatedness root id kind true onlyForeign = rustAccessRelatedness cache root id kind true onlyForeign :=
  accessRelatedness_eq_rust cache root id kind true onlyForeign ((virtual_iff cache root kind).2 bounded)

/-- A concrete counter bound plus virtual-root charge can be discharged by a
bounded history budget. Counting the history and forming the initial counter
bound must be proved by the history protocol using this bridge. -/
theorem noOverflow_of_budget (cache : ExposedCache) (root : UniIndex) (kind : AccessKind)
    (isWildcardTree : Bool) (budget : Nat)
    (counter : (count ((cache.nodes.get root).getD {}) kind).toNat + (if isWildcardTree then 1 else 0) ≤ budget)
    (short : budget < 65536) : NoOverflow cache root kind isWildcardTree :=
  Nat.lt_of_le_of_lt counter short
end DuplicatePrefix.GeneralBorrowBoundedRelatedness
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowBoundedRelatedness.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved bounded relatedness dependency {dependency}"
