import duplicate_prefix.GeneralBorrowExposureAncestorFold
import duplicate_prefix.GeneralBorrowFreshReuseProtection
import duplicate_prefix.GeneralBorrowWildcardRelatednessBounds
namespace DuplicatePrefix.GeneralBorrowExposureCardinality
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureAncestorFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Local access permission strength used by actual exposeTag/updateExposure.
Idempotent FOREIGN access (SIFA) is deliberately a separate field. -/
def effective (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode) : WildcardAccessLevel :=
  ((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess (protections.contains node.tag)

def supports (level : WildcardAccessLevel) : AccessKind → Bool
  | .Read => supportsRead level
  | .Write => supportsWrite level

def counter (cache : ExposedCache) (query : UniIndex) : AccessKind → UInt16
  | .Read => ((cache.nodes.get query).getD {}).localReads
  | .Write => ((cache.nodes.get query).getD {}).localWrites

/-- One present, exposed, supporting descendant contributes once at each
ancestor on its finite actual parent walk. -/
def contributes (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) (row : UniIndex × TreeNode) : Bool :=
  row.2.isExposed && supports (levels row.1 row.2) kind && (walk nodes (nodes.size+1) row.1).contains query

def cardinality (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) : Nat :=
  (nodes.entries.toList.filter (contributes nodes levels query kind)).length

/-- Generic finite-width cache invariant, valid for arbitrary sparse forests,
multiple roots, actual permissions and global protection tables. Formation
from history and preservation are separate theorems, not assumed successes. -/
def Coherent (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) : Prop :=
  ∀ query kind,counter cache query kind = UInt16.ofNat (cardinality nodes levels query kind)

def LocationCoherent (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  Coherent location.exposedCache tree.nodes (effective location protections)

theorem entries_bound (nodes : UniValMap TreeNode) : nodes.entries.toList.length ≤ nodes.size := by
  rw [GeneralBorrowFreshEntries.entries_formula]
  have bounded := List.length_filterMap_le (GeneralBorrowFreshEntries.slot nodes.data) (List.range' 0 nodes.data.size)
  simpa only [List.length_range',UniValMap.size] using bounded

theorem cardinality_bound (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) : cardinality nodes levels query kind ≤ nodes.size :=
  Nat.le_trans (List.length_filter_le _ _) (entries_bound nodes)

/-- The finite-width invariant gives exact Nat counts below the explicit
allocation-node budget, with no Rust correspondence requirement. -/
theorem nat_exact (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (short : nodes.size < 65536) (query : UniIndex) (kind : AccessKind) :
    (counter cache query kind).toNat = cardinality nodes levels query kind := by
  rw [coherent query kind,UInt16.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (cardinality_bound nodes levels query kind) short)

/-- Per-tree root dominance needs this ancestor condition; another root's
unrelated descendants are not silently charged to the selected root. -/
def Covers (nodes : UniValMap TreeNode) (root query : UniIndex) : Prop :=
  ∀ row ∈ nodes.entries.toList,query ∈ walk nodes (nodes.size+1) row.1 → root ∈ walk nodes (nodes.size+1) row.1

private theorem filter_mono {α : Type} (items : List α) (first second : α → Bool)
    (included : ∀ item ∈ items,first item = true → second item = true) :
    (items.filter first).length ≤ (items.filter second).length := by
  induction items with
  | nil => exact Nat.le_refl 0
  | cons item rest ih =>
    have later := ih (fun other member => included other (by simp [member]))
    have current := included item (by simp)
    cases left : first item <;> cases right : second item
    all_goals simp only [List.filter_cons,left,right,Bool.false_eq_true,ite_false,ite_true,List.length_cons]
    all_goals first | omega | exact False.elim (by have := current left;simp [right] at this)

theorem cardinality_dominates (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (root query : UniIndex) (kind : AccessKind) (covers : Covers nodes root query) :
    cardinality nodes levels query kind ≤ cardinality nodes levels root kind := by
  apply filter_mono
  intro row member qualified
  simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at qualified ⊢
  exact ⟨qualified.1,covers row member qualified.2⟩

theorem dominates (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (short : nodes.size < 65536) (root query : UniIndex) (covers : Covers nodes root query) (kind : AccessKind) :
    (counter cache query kind).toNat ≤ (counter cache root kind).toNat := by
  rw [nat_exact cache nodes levels coherent short query kind,nat_exact cache nodes levels coherent short root kind]
  exact cardinality_dominates nodes levels root query kind covers

/-- Every actually exposed supporting node has a positive self witness, under
the same finite-width budget. Presence and support are raw semantic metadata. -/
theorem exposed_self (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (short : nodes.size < 65536) (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (exposed : node.isExposed = true) (kind : AccessKind) (supported : supports (levels index node) kind = true) :
    0 < (counter cache index kind).toNat := by
  rw [nat_exact cache nodes levels coherent short index kind]
  have member : (index,node) ∈ nodes.entries.toList.filter (contributes nodes levels index kind) := by
    refine List.mem_filter.mpr ⟨(GeneralBorrowFreshReuseProtection.entries_get nodes index node).mpr present,?_⟩
    simp only [contributes,exposed,supported,Bool.true_and]
    apply List.contains_iff_mem.mpr
    simp only [walk]
    exact List.mem_cons_self
  apply List.length_pos_iff.mpr
  intro absent
  rw [absent] at member
  cases member
end DuplicatePrefix.GeneralBorrowExposureCardinality
