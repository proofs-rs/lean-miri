import duplicate_prefix.GeneralBorrowFullSharedRead
namespace DuplicatePrefix.GeneralBorrowSharedUnexposed
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Unexposed (tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodeAt index = some node → node.isExposed = false

/-- Actual fresh shared attachment preserves the all-unexposed property. -/
theorem stage_unexposed (input : Input) (initial : Unexposed input.tree) :
    Unexposed (stage input) := by
  intro query node present
  let attached := GeneralBorrowFreshGraph.attached input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
  have lookup : attached.nodeAt query = some node := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,attached,BorrowTree.nodeAt] using present
  by_cases parent : query = input.parent
  · subst query
    rw [GeneralBorrowFreshGraph.parent_lookup _ _ _ _ _ (at_end input) input.parentPresent] at lookup
    cases lookup
    change input.parentNode.isExposed = false
    exact initial _ _ input.parentPresent
  · by_cases fresh : query = index input
    · subst query
      rw [GeneralBorrowFreshGraph.new_lookup _ _ _ _ _ (at_end input) input.parentPresent] at lookup
      cases lookup
      rfl
    · rw [GeneralBorrowFreshGraph.other_lookup _ _ _ _ _ _ (at_end input) input.parentPresent parent fresh] at lookup
      exact initial _ _ lookup

/-- The real ancestor SIFA update preserves flags, so this property concerns
all old and newly attached nodes, not only the newly created leaf. -/
theorem append_unexposed (input : Input) (initial : Unexposed input.tree) :
    Unexposed (result input) := by
  intro query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (stage input) (result input)
    (exposure input) query
  rw [show (result input).nodes.get query = some node from present] at flags
  cases old : (stage input).nodeAt query with
  | none => rw [show (stage input).nodes.get query = none from old] at flags; contradiction
  | some before =>
    have oldFlag := stage_unexposed input initial query before old
    simpa only [show (stage input).nodes.get query = some before from old,Option.map_some,Option.some.injEq,oldFlag] using flags
/-- The next constructor's actual normal-Read cache is unchanged when every
node is unexposed, without assuming that normal access succeeds. -/
theorem read_cache (input : Input) (location : LocationTree) (protections : ProtectedTags)
    (initial : Unexposed input.tree) :
    (GeneralBorrowFullSharedRead.readLocation input location protections).exposedCache = location.exposedCache :=
  GeneralBorrowReadCacheFrame.normal_cache input.tree location input.parent .Read protections .VisitChildrenOfAccessed initial

/-- Preparing the constructor from the real read location leaves all node flags
unchanged. Read completion is derived separately by read_closed. -/
theorem prepared (input : Input) (location : LocationTree) (protections : ProtectedTags)
    (offset : input.offset = 0) (initial : Unexposed input.tree) :
    Unexposed (GeneralBorrowFullSharedRead.afterReadInput input location protections offset).tree := initial

/-- The actual constructor from the prepared Read metadata preserves the
all-unexposed property for subsequent operations. -/
theorem read_append (input : Input) (location : LocationTree) (protections : ProtectedTags)
    (offset : input.offset = 0) (initial : Unexposed input.tree) :
    Unexposed (result (GeneralBorrowFullSharedRead.afterReadInput input location protections offset)) :=
  append_unexposed _ (prepared input location protections offset initial)

end DuplicatePrefix.GeneralBorrowSharedUnexposed
