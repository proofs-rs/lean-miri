import duplicate_prefix.GeneralBorrowWildcardVirtualLeaf
import duplicate_prefix.GeneralBorrowWildcardSubtreeStack
import duplicate_prefix.GeneralBorrowExposureAncestorFold

/-! Component completion regressions for the included wildcard postorder repair. -/

namespace DuplicatePrefix.S05DisabledLatentWildcardFailure
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowNodeUpdate GeneralBorrowExposure
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
set_option cbv.maxSteps 1000000
set_option maxRecDepth 65536
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- A three-node component plus an untouched original root, not an entire
diagnostic snapshot or a Rust-history/MIR-call claim. B/W are omitted; cutoff 4
is supplied externally, and V occupies index 3 rather than diagnostic index 4. -/
def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def original : TreeNode := ⟨⟨1,by decide⟩,none,#[],.Disabled,.None,true,none⟩
def a : TreeNode := ⟨⟨2,by decide⟩,none,#[ix 2],.Cell,.Write,false,none⟩
def d : TreeNode := ⟨⟨3,by decide⟩,some (ix 1),#[ix 3],.ReservedFrz false,.Read,false,none⟩
def v : TreeNode := ⟨⟨5,by decide⟩,some (ix 2),#[],.ReservedFrz false,.Read,true,none⟩
def maximum : BorTag := ⟨4,by decide⟩
def cache : ExposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩]⟩⟩
def location : LocationTree := {
  perms := ⟨#[some ⟨.Unique,true,.None⟩,none,some ⟨.Disabled,true,.Read⟩,none]⟩
  exposedCache := cache }
def tree : BorrowTree := {
  tagMapping := ⟨#[(original.tag,ix 0),(a.tag,ix 1),(d.tag,ix 2),(v.tag,ix 3)],#[]⟩
  nodes := ⟨#[some original,some a,some d,some v]⟩
  locations := DedupRangeMap.new (Size.ofBytes 2) location
  roots := #[ix 0,ix 1] }
def afterCache : ExposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩]⟩⟩
def afterV : LocationTree := {
  perms := location.perms.insert (ix 3) ⟨.Disabled,false,.Write⟩
  exposedCache := afterCache }

private theorem index_cases (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    index = ix 0 ∨ index = ix 1 ∨ index = ix 2 ∨ index = ix 3 := by
  have bound := lookup_valid tree.nodes index node present
  change index.toNat < 4 at bound
  have cases : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨ index.toNat = 3 := by omega
  rcases cases with same | same | same | same
  · exact .inl (index_injective index (ix 0) same)
  · exact .inr (.inl (index_injective index (ix 1) same))
  · exact .inr (.inr (.inl (index_injective index (ix 2) same)))
  · exact .inr (.inr (.inr (index_injective index (ix 3) same)))

private def depth : ParentDepth tree.nodes where
  depth := UniIndex.toNat
  bounded := by intro index node present;exact Nat.le_of_lt (lookup_valid tree.nodes index node present)
  parent := by
    intro index node present parent edge
    rcases index_cases index node present with rfl | rfl | rfl | rfl
    · change some original = some node at present
      cases present
      cases edge
    · change some a = some node at present
      cases present
      cases edge
    · change some d = some node at present
      cases present
      have same : parent = ix 1 := Option.some.inj edge.symm
      subst parent
      exact ⟨a,rfl,by decide +kernel⟩
    · change some v = some node at present
      cases present
      have same : parent = ix 2 := Option.some.inj edge.symm
      subst parent
      exact ⟨d,rfl,by decide +kernel⟩

private theorem cache_update : cache.updateExposure tree.nodes (ix 3) .Write .None = ⟨afterCache,.ok ()⟩ := by
  rw [GeneralBorrowExposureAncestorFold.update cache tree.nodes depth (ix 3) v rfl .Write .None]
  rfl

private theorem record_v :
    (⟨.ReservedFrz false,false,.Read⟩ : LocationState).recordNewAccess .Write .ForeignAccess =
      .Recorded ⟨.ReservedFrz false,false,.Write⟩ := rfl
private theorem perform_v :
    (⟨.ReservedFrz false,false,.Write⟩ : LocationState).performAccess .Write .ForeignAccess false =
      .Success ⟨.Disabled,false,.Write⟩ ⟨.ReservedFrz false,.Disabled⟩ := rfl

/-- The postchildren Disabled/Cell guard now completes this latent subtree. -/
theorem actual_completed :
    (tree.performWildcardAccessAt location (ix 1) (some maximum) .Write {} true).status = .Completed := by cbv

theorem child_effects_retained :
    (tree.performWildcardAccessAt location (ix 1) (some maximum) .Write {} true).location.perms.get (ix 3) =
      some ⟨.Disabled,false,.Write⟩ := by cbv

theorem cache_effects_retained :
    (tree.performWildcardAccessAt location (ix 1) (some maximum) .Write {} true).location.exposedCache = afterCache := by cbv

end DuplicatePrefix.S05DisabledLatentWildcardFailure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "S05DisabledLatentWildcardFailure" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved bounded component dependency {name}: {dependency}"
