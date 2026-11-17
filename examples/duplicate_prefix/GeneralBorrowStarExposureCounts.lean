import duplicate_prefix.GeneralBorrowExposureHistoryBounds
import duplicate_prefix.GeneralBorrowWildcardRelatednessBounds

namespace DuplicatePrefix.GeneralBorrowStarExposureCounts
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposeReadFold DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Exact cardinality accounting for exposed Frozen leaves of an unexposed
parentless root. Counts are Nat specifications of the actual UInt16 fields. -/
structure Counts (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex) : Prop where
  rootAbsent : root ∉ leaves
  rootReads : reads cache root = leaves.length
  otherReads : ∀ query, query ≠ root → reads cache query = leaves.count query
  allWrites : ∀ query, writes cache query = 0

theorem empty (root : UniIndex) : Counts {} root [] := by
  refine ⟨by simp,?_,?_,?_⟩
  · simp [reads,UniValMap.get]
  · intro query different;simp [reads,UniValMap.get]
  · intro query;simp [writes,UniValMap.get]

/-- One REAL leaf/root cache delta has exact Nat cardinalities while there is
space in the fixed UInt16 fields. No Rust arithmetic correspondence is used. -/
theorem step (cache : ExposedCache) (root leaf : UniIndex) (leaves : List UniIndex)
    (good : Counts cache root leaves) (different : root ≠ leaf) (room : leaves.length+1 < 65536) :
    Counts (bumpRead (bumpRead cache leaf) root) root (leaf::leaves) := by
  have notRoot : leaf ≠ root := Ne.symm different
  have leafBound : leaves.count leaf ≤ leaves.length := List.count_le_length
  have leafRoom : reads cache leaf+1 < 65536 := by rw [good.otherReads leaf notRoot];omega
  have beforeRoot : reads (bumpRead cache leaf) root = leaves.length := by
    rw [bump_other cache leaf root different,good.rootReads]
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.mem_cons,not_or]
    exact ⟨different,good.rootAbsent⟩
  · rw [bump_same _ root (by rw [beforeRoot];exact room),beforeRoot]
    simp only [List.length_cons]
  · intro query notRootQuery
    rw [bump_other (bumpRead cache leaf) root query notRootQuery]
    by_cases same : query = leaf
    · subst query
      rw [bump_same cache leaf leafRoom,good.otherReads leaf notRoot,List.count_cons_self]
    · rw [bump_other cache leaf query same,good.otherReads query notRootQuery,List.count_cons_of_ne (Ne.symm same)]
  · intro query
    rw [bump_writes,bump_writes,good.allWrites query]

/-- The actual pure description of a successful exposure fold has these exact
counts; the actual exposeTag equality is supplied by run_eq, not assumed here. -/
theorem pure_counts (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (already : List UniIndex)
    (initial : Counts location.exposedCache root already)
    (different : ∀ request ∈ requests, root ≠ request.leaf)
    (room : already.length+requests.length < 65536) :
    Counts (pureRun capacity root requests tree location).2.exposedCache root
      ((requests.map Request.leaf).reverse ++ already) := by
  induction requests generalizing tree location already with
  | nil => simpa only [pureRun,List.map_nil,List.reverse_nil,List.nil_append] using initial
  | cons request rest ih =>
    have changed := step location.exposedCache root request.leaf already initial (different request (by simp)) (by simp only [List.length_cons] at room;omega)
    have later := ih (nextTree tree location capacity root request) (nextLocation location root request) (request.leaf::already)
      changed (fun other member => different other (by simp [member])) (by simp only [List.length_cons] at room ⊢;omega)
    simpa only [pureRun,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using later

/-- Root cardinality bounds every actual node counter for either access kind. -/
theorem dominates (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex)
    (good : Counts cache root leaves) : GeneralBorrowWildcardRelatednessBounds.Dominates cache root := by
  intro query kind
  cases kind with
  | Read =>
    change reads cache query ≤ reads cache root
    rw [good.rootReads]
    by_cases same : query = root
    · subst query;rw [good.rootReads];omega
    · rw [good.otherReads query same];exact List.count_le_length
  | Write =>
    change writes cache query ≤ writes cache root
    rw [good.allWrites query,good.allWrites root];omega

/-- A distinct actually exposed leaf has its own positive Read witness. Frozen
leaves have no Write witness, matching their source permission strength. -/
theorem self (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex)
    (good : Counts cache root leaves) (unique : leaves.Nodup) (query : UniIndex) (member : query ∈ leaves) :
    reads cache query = 1 ∧ writes cache query = 0 := by
  have different : query ≠ root := by intro same;subst query;exact good.rootAbsent member
  exact ⟨(good.otherReads query different).trans (unique.count_of_mem member),good.allWrites query⟩

/-- Counts are uniformly bounded by actual exposure cardinality; this is a
consequence of exact accounting, not an initial cache-budget premise. -/
theorem within (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex)
    (good : Counts cache root leaves) : Within cache leaves.length := by
  intro query
  refine ⟨?_,?_⟩
  · by_cases same : query = root
    · subst query;rw [good.rootReads];omega
    · rw [good.otherReads query same];exact List.count_le_length
  · rw [good.allWrites query];omega

/-- Locations track the exact cache returned by the fold, also for its empty prefix. -/
theorem pure_locations (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex)
    (locations : tree.locations = RangeMapNonempty.homogeneous capacity location) :
    (pureRun capacity root requests tree location).1.locations =
      RangeMapNonempty.homogeneous capacity (pureRun capacity root requests tree location).2 := by
  induction requests generalizing tree location with
  | nil => exact locations
  | cons request rest ih => exact ih _ _ rfl

/-- Exact accounting follows an actual successful exposure sequence. Ready
contains raw node/permission metadata; operation success is a conclusion. -/
theorem run_counts (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode) (protections : ProtectedTags)
    (locations : tree.locations = RangeMapNonempty.homogeneous capacity location)
    (ready : ∀ request ∈ requests, Ready tree location root rootNode request)
    (unique : (requests.map Request.leaf).Nodup)
    (emptyCache : location.exposedCache = {}) (room : requests.length < 65536) :
    (run protections requests tree).outcome = .ok () ∧
    ∃ finalLocation, (run protections requests tree).tree.locations =
      RangeMapNonempty.homogeneous capacity finalLocation ∧
      Counts finalLocation.exposedCache root (requests.map Request.leaf).reverse ∧
      GeneralBorrowWildcardRelatednessBounds.Dominates finalLocation.exposedCache root ∧
      (∀ leaf ∈ requests.map Request.leaf, reads finalLocation.exposedCache leaf = 1 ∧
        writes finalLocation.exposedCache leaf = 0) := by
  have actual := run_eq requests tree location capacity root rootNode protections locations ready unique
  have counted := pure_counts requests tree location capacity root []
    (by rw [emptyCache];exact empty root)
    (fun request member => (ready request member).different) (by simpa using room)
  simp only [List.append_nil] at counted
  rw [actual]
  refine ⟨rfl,(pureRun capacity root requests tree location).2,
    pure_locations requests tree location capacity root locations,counted,
    dominates _ _ _ counted,?_⟩
  intro leaf member
  exact self _ _ _ counted (List.pairwise_reverse.mpr (unique.imp (fun different => Ne.symm different))) leaf (List.mem_reverse.mpr member)

end DuplicatePrefix.GeneralBorrowStarExposureCounts
