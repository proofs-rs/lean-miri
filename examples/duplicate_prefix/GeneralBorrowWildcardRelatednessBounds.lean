import Lean
import Miri.TreeBorrows.TreeState

/-! Bounds for the fixed Lean wildcard classifier. All additions below are Nat
additions from `ExposedCache.accessRelatedness`; no Rust comparison is used. -/
namespace DuplicatePrefix.GeneralBorrowWildcardRelatednessBounds
open Miri.TreeBorrows

/-- The counter selected by the actual access kind, including absent-node defaults. -/
def count (cache : ExposedCache) (index : UniIndex) (kind : AccessKind) : Nat :=
  let state := (cache.nodes.get index).getD {}
  match kind with
  | .Read => state.localReads.toNat
  | .Write => state.localWrites.toNat

/-- A virtual root supplies one foreign possibility. Under the cache counting
bound it precludes both an absent classification and a purely local one. The
only-foreign clamp retains that foreign possibility. -/
theorem virtual_classify (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool)
    (bounded : count cache index kind ≤ count cache root kind) :
    cache.accessRelatedness root index kind true onlyForeign =
      some (if onlyForeign || count cache index kind == 0
        then .ForeignAccess else .EitherAccess) := by
  have nonzero : count cache root kind + 1 ≠ 0 := by omega
  have different : count cache root kind + 1 ≠ count cache index kind := by omega
  by_cases zero : count cache index kind = 0
  all_goals cases kind <;> cases onlyForeign <;>
    simp_all [ExposedCache.accessRelatedness, count, Id.run, pure]

/-- Convenient shape for consumers of the visitor: the relatedness contains a
foreign alternative even when local alternatives also remain. -/
theorem virtual_foreign_or_either (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool)
    (bounded : count cache index kind ≤ count cache root kind) :
    cache.accessRelatedness root index kind true onlyForeign = some .ForeignAccess ∨
    cache.accessRelatedness root index kind true onlyForeign = some .EitherAccess := by
  rw [virtual_classify cache root index kind onlyForeign bounded]
  split <;> simp

/-- The clamp makes every bounded virtual-root query exactly foreign. -/
theorem virtual_only_foreign (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind)
    (bounded : count cache index kind ≤ count cache root kind) :
    cache.accessRelatedness root index kind true true = some .ForeignAccess := by
  rw [virtual_classify cache root index kind true bounded]
  rfl

/-- In particular the walker cannot report missing exposed references at this
query merely because the cache has zero real exposures. -/
theorem virtual_ne_none (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool)
    (bounded : count cache index kind ≤ count cache root kind) :
    cache.accessRelatedness root index kind true onlyForeign ≠ none := by
  rw [virtual_classify cache root index kind onlyForeign bounded]
  simp

theorem virtual_ne_local (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool)
    (bounded : count cache index kind ≤ count cache root kind) :
    cache.accessRelatedness root index kind true onlyForeign ≠ some .LocalAccess := by
  rw [virtual_classify cache root index kind onlyForeign bounded]
  split <;> simp

/-- A simultaneous read/write counting invariant for every node of a component.
It concerns cache data only; it does not assume an access operation succeeds. -/
def Dominates (cache : ExposedCache) (root : UniIndex) : Prop :=
  ∀ index kind, count cache index kind ≤ count cache root kind

theorem dominates_classify (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool) (bounded : Dominates cache root) :
    cache.accessRelatedness root index kind true onlyForeign =
      some (if onlyForeign || count cache index kind == 0
        then .ForeignAccess else .EitherAccess) :=
  virtual_classify cache root index kind onlyForeign (bounded index kind)

/-- Root queries themselves need no cache coherence assumption. -/
theorem root_classify (cache : ExposedCache) (root : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool) :
    cache.accessRelatedness root root kind true onlyForeign =
      some (if onlyForeign || count cache root kind == 0
        then .ForeignAccess else .EitherAccess) :=
  virtual_classify cache root root kind onlyForeign (Nat.le_refl _)

/-- A node with no local alternatives is foreign, including an absent cache row. -/
theorem zero_classify (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (onlyForeign : Bool) (zero : count cache index kind = 0) :
    cache.accessRelatedness root index kind true onlyForeign = some .ForeignAccess := by
  have bounded : count cache index kind ≤ count cache root kind := by omega
  rw [virtual_classify cache root index kind onlyForeign bounded, zero]
  cases onlyForeign <;> rfl

end DuplicatePrefix.GeneralBorrowWildcardRelatednessBounds
