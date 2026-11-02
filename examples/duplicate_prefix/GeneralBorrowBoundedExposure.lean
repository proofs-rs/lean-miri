import duplicate_prefix.GeneralBorrowExposureHistoryBounds
import duplicate_prefix.GeneralBorrowBoundedRelatedness
namespace DuplicatePrefix.GeneralBorrowBoundedExposure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeReadFold DuplicatePrefix.GeneralBorrowExposureHistoryBounds
open DuplicatePrefix.GeneralBorrowBoundedRelatedness
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The source-exact u16 adapter and the fixed Lean operation agree at every
cache query, for either access kind and either virtual/only-foreign flag. -/
def Compatible (cache : ExposedCache) : Prop :=
  ∀ root query kind virtual onlyForeign,
    cache.accessRelatedness root query kind virtual onlyForeign =
      rustAccessRelatedness cache root query kind virtual onlyForeign

theorem compatible_of_within (cache : ExposedCache) (budget : Nat)
    (bounded : Within cache budget) (short : budget+1 < 65536) : Compatible cache := by
  intro root query kind virtual onlyForeign
  apply accessRelatedness_eq_rust
  have counter : (count ((cache.nodes.get root).getD {}) kind).toNat ≤ budget := by
    cases kind with
    | Read => exact (bounded root).1
    | Write => exact (bounded root).2
  apply noOverflow_of_budget cache root kind virtual (budget+1) _ short
  cases virtual <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

/-- A bounded REAL exposure sequence completes and yields counter headroom and
Lean/Rust arithmetic agreement. Initial graph/Ready data remain explicit. The
history allowance counts initial cache witnesses, exposure calls, and one unit
reserved for virtual-root classification; it is NOT merely exposure-count<65536.
No operation success, callback success, trace or poststate is supplied. -/
theorem run_safe_arithmetic (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode) (protections : ProtectedTags) (budget : Nat)
    (locations : tree.locations = DuplicatePrefix.RangeMapNonempty.homogeneous capacity location)
    (ready : ∀ request ∈ requests, Ready tree location root rootNode request)
    (distinct : (requests.map Request.leaf).Nodup)
    (bounded : Within location.exposedCache budget)
    (short : budget+requests.length+1 < 65536) :
    (run protections requests tree).outcome = .ok () ∧
    ∃ finalLocation, (run protections requests tree).tree.locations =
      DuplicatePrefix.RangeMapNonempty.homogeneous capacity finalLocation ∧
      Within finalLocation.exposedCache (budget+requests.length) ∧ Compatible finalLocation.exposedCache := by
  obtain ⟨completed,finalLocation,final,bound⟩ := run_within requests tree location capacity root rootNode protections budget
    locations ready distinct bounded (by omega)
  exact ⟨completed,finalLocation,final,bound,compatible_of_within _ _ bound short⟩

/-- Every finite prefix has the same guarantees, not just the terminal cache.
In particular the bound covers the states at which the next real exposure or
virtual-root query occurs. This does not assert safety of other Rust operations. -/
theorem all_prefixes (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode) (protections : ProtectedTags) (budget : Nat)
    (locations : tree.locations = DuplicatePrefix.RangeMapNonempty.homogeneous capacity location)
    (ready : ∀ request ∈ requests, Ready tree location root rootNode request)
    (distinct : (requests.map Request.leaf).Nodup)
    (bounded : Within location.exposedCache budget)
    (short : budget+requests.length+1 < 65536) :
    ∀ before remaining, requests = before ++ remaining →
      (run protections before tree).outcome = .ok () ∧
      ∃ finalLocation, (run protections before tree).tree.locations =
        DuplicatePrefix.RangeMapNonempty.homogeneous capacity finalLocation ∧
        Within finalLocation.exposedCache (budget+before.length) ∧ Compatible finalLocation.exposedCache := by
  intro before remaining splitEq
  have prefixReady : ∀ request ∈ before, Ready tree location root rootNode request := by
    intro request member
    exact ready request (by rw [splitEq];exact List.mem_append_left _ member)
  have prefixDistinct : (before.map Request.leaf).Nodup := by
    rw [splitEq,List.map_append] at distinct
    exact (List.nodup_append.mp distinct).1
  have size : before.length ≤ requests.length := by rw [splitEq,List.length_append];omega
  exact run_safe_arithmetic before tree location capacity root rootNode protections budget locations prefixReady prefixDistinct bounded (by omega)
end DuplicatePrefix.GeneralBorrowBoundedExposure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowBoundedExposure.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved bounded exposure dependency {dependency}"
