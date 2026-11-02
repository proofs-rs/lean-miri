import duplicate_prefix.GeneralBorrowGcReportedCachePreservation
import duplicate_prefix.GeneralBorrowGcSifaConsistency

namespace DuplicatePrefix.GeneralBorrowGcReportedHistory
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Recurring physical and graph data for actual reported-provenance collection.
The root array may be empty or repeated and the partition is arbitrary. -/
structure State (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop where
  forest : Nonempty (Forest (source_normal_projection tree location protections).topology)
  depth : Nonempty (ParentDepth tree.nodes)
  children : GeneralBorrowGraph.ChildNodes tree
  fits : tree.nodes.size ≤ 4294967296
  roots : ∀ root ∈ tree.roots.toList, ∃ node, tree.nodes.get root = some node ∧ node.parent = none
  well : tree.locations.WellFormed
  cache : Every (fun row => LocationCoherent tree row protections) tree.locations
  physicalProfile : Every (fun row => GeneralBorrowLocationSifaConsistency.Profile tree row protections) tree.locations

/-- Every step recomputes the actual provenance report on its current tree. -/
def next (tree : BorrowTree) (extra : Array BorTag) : BorrowTree :=
  (tree.removeUnreachableTags (tree.provenanceTags ++ extra)).tree

/-- The exact ordered roots are preserved by the source GC, even on error states. -/
theorem roots (tree : BorrowTree) (extra : Array BorTag) :
    (next tree extra).roots = tree.roots :=
  (GeneralBorrowGcResourceFrame.preserves (n := 0) (fun step => Fin.elim0 step) tree
    (tree.provenanceTags ++ extra) (by intro step; exact Fin.elim0 step)).roots

/-- Initial graph/cache/profile data derive actual success and all data needed
for the next collection. Neither success nor exposed liveness is a premise. -/
theorem advance (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (initial : State tree location protections) (extra : Array BorTag) :
    (tree.removeUnreachableTags (tree.provenanceTags ++ extra)).outcome = .ok () ∧
    State (next tree extra) location protections ∧
    (next tree extra).nodes.size = tree.nodes.size ∧
    (next tree extra).locations.size = tree.locations.size ∧
    (next tree extra).roots = tree.roots := by
  obtain ⟨forest⟩ := initial.forest
  obtain ⟨depth⟩ := initial.depth
  have complete := GeneralBorrowGcForestComplete.complete tree location protections forest depth
    initial.children initial.fits initial.roots initial.well (tree.provenanceTags ++ extra)
  have cache := GeneralBorrowGcReportedCachePreservation.collect tree location protections forest depth
    initial.children initial.fits initial.roots initial.well extra initial.cache
  have profile := GeneralBorrowGcSifaConsistency.collect tree protections (tree.provenanceTags ++ extra) initial.physicalProfile
  have rootEq := roots tree extra
  refine ⟨complete.1,?_,complete.2.2.2.1,complete.2.2.1,rootEq⟩
  constructor
  · exact complete.2.2.2.2.2.1 location protections
  · exact complete.2.2.2.2.1
  · exact complete.2.2.2.2.2.2.1
  · change (tree.removeUnreachableTags (tree.provenanceTags ++ extra)).tree.nodes.size ≤ _
    rw [complete.2.2.2.1]; exact initial.fits
  · rw [rootEq]
    exact complete.2.2.2.2.2.2.2.2.2
  · exact complete.2.1
  · exact cache.2
  · exact profile

def execute (tree : BorrowTree) : List (Array BorTag) → BorrowTree
  | [] => tree
  | extra :: rest => execute (next tree extra) rest

def AllCompleted (tree : BorrowTree) : List (Array BorTag) → Prop
  | [] => True
  | extra :: rest =>
    (tree.removeUnreachableTags (tree.provenanceTags ++ extra)).outcome = .ok () ∧
    AllCompleted (next tree extra) rest

/-- Any finite list of extra-tag arrays drives real, successful GC steps from
initial data alone. Every current provenance report is computed anew, and the
final recurring state includes cache coherence and the full physical profile. -/
theorem run (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (initial : State tree location protections) (extras : List (Array BorTag)) :
    AllCompleted tree extras ∧ State (execute tree extras) location protections ∧
    (execute tree extras).nodes.size = tree.nodes.size ∧
    (execute tree extras).locations.size = tree.locations.size ∧
    (execute tree extras).roots = tree.roots := by
  induction extras generalizing tree with
  | nil => exact ⟨True.intro,initial,rfl,rfl,rfl⟩
  | cons extra rest ih =>
    have first := advance tree location protections initial extra
    have tail := ih (next tree extra) first.2.1
    exact ⟨⟨first.1,tail.1⟩,tail.2.1,tail.2.2.1.trans first.2.2.1,
      tail.2.2.2.1.trans first.2.2.2.1,tail.2.2.2.2.trans first.2.2.2.2⟩

end DuplicatePrefix.GeneralBorrowGcReportedHistory
