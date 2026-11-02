import duplicate_prefix.GeneralBorrowExposedConditionalReadExactAccess
import duplicate_prefix.GeneralBorrowExposedConditionalWriteAccess
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowExposedConditionalRangeData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The active-kind cache-sensitive raw permission/protector/accessed profile. -/
def Profile (tree : BorrowTree) (protections : ProtectedTags) : AccessKind → LocationTree → Prop
  | .Read => fun location => GeneralBorrowExposedConditionalReadState.Readable tree location protections
  | .Write => fun location => GeneralBorrowExposedConditionalWriteState.Profile tree location protections

/-- Slice-local raw topology, counters, numeric budget and permission data.
The supporting exposed descendant must lie in physical root position zero.
SIFA recording obligations are derived by the real source previsit predicate. -/
def Ready (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (location : LocationTree) : Prop :=
  Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) ∧
  match kind with
  | .Read => Nonempty (GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree location primary protections) ∧
      ∀ root ∈ extras, Nonempty (GeneralBorrowExposedConditionalReadState.Data tree location root protections)
  | .Write => Nonempty (GeneralBorrowExposedConditionalWritePrimaryWitness.Data tree location primary protections) ∧
      ∀ root ∈ extras, Nonempty (GeneralBorrowExposedConditionalWriteState.Data tree location root protections)

/-- Active-kind counters remain exact. Read also retains the entire cache;
Write may apply genuine Read-counter deltas. -/
def Frame (kind : AccessKind) (before after : LocationTree) : Prop :=
  (∀ query, GeneralBorrowExposureCardinality.counter after.exposedCache query kind =
    GeneralBorrowExposureCardinality.counter before.exposedCache query kind) ∧
  (kind = .Read → after.exposedCache = before.exposedCache)

theorem frame_refl (kind : AccessKind) (location : LocationTree) : Frame kind location location :=
  ⟨fun _ => rfl,fun _ => rfl⟩

theorem ready_profile (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (location : LocationTree) (ready : Ready tree protections primary extras kind location) :
    Profile tree protections kind location := by
  cases kind with
  | Read => obtain ⟨_,⟨data⟩,_⟩ := ready;exact data.base.readable
  | Write => obtain ⟨_,⟨data⟩,_⟩ := ready;exact data.base.profile

/-- The actual whole-forest location callback derives all outcomes from raw
Ready data, with no operation-success or classification input. -/
theorem location (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange) (before : LocationTree)
    (roots : tree.roots = (primary::extras).toArray) (ready : Ready tree protections primary extras kind before) :
    let accessed := source_tree_access_at tree before none kind protections mode range
    source_access_status accessed = none ∧ Profile tree protections kind (source_access_location accessed) ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location accessed) protections ∧
      Frame kind before (source_access_location accessed) := by
  classical
  cases kind with
  | Read =>
    obtain ⟨⟨forest⟩,⟨primaryData⟩,extraData⟩ := ready
    obtain ⟨after,actual,status,frame,profile,coherent,cache⟩ := GeneralBorrowExposedConditionalReadExactAccess.access tree before protections
      primary extras mode range roots forest primaryData (fun root member => Classical.choice (extraData root member))
    dsimp only
    rw [actual]
    exact ⟨status,profile,coherent,frame,fun _ => cache⟩
  | Write =>
    obtain ⟨⟨forest⟩,⟨primaryData⟩,extraData⟩ := ready
    obtain ⟨after,actual,status,frame,profile,coherent⟩ := GeneralBorrowExposedConditionalWriteAccess.access tree before protections
      primary extras mode range roots forest primaryData (fun root member => Classical.choice (extraData root member))
    dsimp only
    rw [actual]
    exact ⟨status,profile,coherent,frame,by intro impossible;cases impossible⟩
end DuplicatePrefix.GeneralBorrowExposedConditionalRangeData
