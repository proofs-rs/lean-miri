import duplicate_prefix.GeneralBorrowExposeReadFold
namespace DuplicatePrefix.GeneralBorrowExposureHistoryBounds
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def reads (cache : ExposedCache) (index : UniIndex) : Nat :=
  ((cache.nodes.get index).getD {}).localReads.toNat

def writes (cache : ExposedCache) (index : UniIndex) : Nat :=
  ((cache.nodes.get index).getD {}).localWrites.toNat

/-- Numeric initial/cache invariant; node vacancy alone is not this property. -/
def Within (cache : ExposedCache) (budget : Nat) : Prop :=
  ∀ index, reads cache index ≤ budget ∧ writes cache index ≤ budget

theorem empty_within : Within {} 0 := by
  intro index
  simp [reads,writes,UniValMap.get]

theorem bump_same (cache : ExposedCache) (index : UniIndex)
    (room : reads cache index + 1 < 65536) :
    reads (bumpRead cache index) index = reads cache index + 1 := by
  simp only [reads,bumpRead,GeneralBorrowFreshLocation.get_same,Option.getD_some]
  rw [UInt16.toNat_add]
  change (reads cache index+1)%65536 = reads cache index+1
  exact Nat.mod_eq_of_lt room

theorem bump_other (cache : ExposedCache) (index query : UniIndex) (different : query ≠ index) :
    reads (bumpRead cache index) query = reads cache query := by
  simp only [reads,bumpRead,GeneralBorrowFreshLocation.get_other _ _ _ _ different]

theorem bump_writes (cache : ExposedCache) (index query : UniIndex) :
    writes (bumpRead cache index) query = writes cache query := by
  by_cases same : query = index
  · subst query
    simp only [writes,bumpRead,GeneralBorrowFreshLocation.get_same,Option.getD_some]
  · simp only [writes,bumpRead,GeneralBorrowFreshLocation.get_other _ _ _ _ same]

/-- A valid leaf/root exposure visits two DISTINCT indices, so every cache
counter increases by at most one, not two, for this real exposure operation. -/
theorem next_within (location : LocationTree) (root : UniIndex) (request : Request) (budget : Nat)
    (bounded : Within location.exposedCache budget) (different : root ≠ request.leaf)
    (room : budget+1 < 65536) :
    Within (nextLocation location root request).exposedCache (budget+1) := by
  intro query
  have old := bounded query
  have increment : ∀ index, reads location.exposedCache index+1 < 65536 := by
    intro index
    have := (bounded index).1
    omega
  constructor
  · change reads (bumpRead (bumpRead location.exposedCache request.leaf) root) query ≤ budget+1
    by_cases atRoot : query = root
    · subst query
      have before := bump_other location.exposedCache request.leaf root different
      rw [bump_same _ root (by rw [before];exact increment root),before]
      omega
    · rw [bump_other _ root query atRoot]
      by_cases atLeaf : query = request.leaf
      · subst query
        rw [bump_same _ request.leaf (increment request.leaf)]
        omega
      · rw [bump_other _ request.leaf query atLeaf]
        omega
  · change writes (bumpRead (bumpRead location.exposedCache request.leaf) root) query ≤ budget+1
    rw [bump_writes,bump_writes]
    omega

/-- Bound every stored/default cache counter after the source-exact exposure
fold. No final cache, operation-success or poststate is a premise. -/
theorem pure_within (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (budget : Nat)
    (bounded : Within location.exposedCache budget)
    (different : ∀ request ∈ requests, root ≠ request.leaf)
    (room : budget+requests.length < 65536) :
    Within (pureRun capacity root requests tree location).2.exposedCache (budget+requests.length) := by
  induction requests generalizing tree location budget with
  | nil => exact bounded
  | cons request rest ih =>
    have next := next_within location root request budget bounded (different request (by simp)) (by simp only [List.length_cons] at room;omega)
    have tail := ih (nextTree tree location capacity root request) (nextLocation location root request) (budget+1)
      next (fun other member => different other (by simp [member])) (by simp only [List.length_cons] at room;omega)
    simpa only [pureRun,List.length_cons,Nat.add_assoc,Nat.add_comm 1 rest.length] using tail

/-- Real successful exposures retain the numeric budget. Ready/Nodup describe
initial nodes; successful execution of the fold is derived by run_eq. -/
theorem run_within (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode) (protections : ProtectedTags) (budget : Nat)
    (locations : tree.locations = DuplicatePrefix.RangeMapNonempty.homogeneous capacity location)
    (ready : ∀ request ∈ requests, Ready tree location root rootNode request)
    (distinct : (requests.map Request.leaf).Nodup)
    (bounded : Within location.exposedCache budget)
    (room : budget+requests.length < 65536) :
    (run protections requests tree).outcome = .ok () ∧
    ∃ finalLocation, (run protections requests tree).tree.locations =
      DuplicatePrefix.RangeMapNonempty.homogeneous capacity finalLocation ∧
      Within finalLocation.exposedCache (budget+requests.length) := by
  rw [run_eq requests tree location capacity root rootNode protections locations ready distinct]
  have bound := pure_within requests tree location capacity root budget bounded
    (fun request member => (ready request member).different) room
  have shape : (pureRun capacity root requests tree location).1.locations =
      DuplicatePrefix.RangeMapNonempty.homogeneous capacity (pureRun capacity root requests tree location).2 := by
    clear bound bounded room ready distinct rootNode protections budget
    induction requests generalizing tree location with
    | nil => exact locations
    | cons request rest ih => exact ih _ _ rfl
  exact ⟨rfl,_,shape,bound⟩
end DuplicatePrefix.GeneralBorrowExposureHistoryBounds
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowExposureHistoryBounds.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved exposure-history dependency {dependency}"
