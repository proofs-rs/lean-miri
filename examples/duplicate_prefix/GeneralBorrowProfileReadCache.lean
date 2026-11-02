import duplicate_prefix.GeneralBorrowFullSharedStep
import duplicate_prefix.GeneralBorrowReadNoopCache
namespace DuplicatePrefix.GeneralBorrowProfileReadCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowFullSharedRead
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A real full-slice parent Read retains its actual cache even when arbitrary
root/leaf exposure flags are set: Unique local and Frozen visitors are no-ops. -/
theorem read (input : Input) (location : LocationTree) (good : State input location) :
    (GeneralBorrowFullSharedRead.read input {}).status = .Completed ∧
    (readLocation input location {}).exposedCache = location.exposedCache := by
  obtain ⟨forest⟩ := good.forest
  have facts := read_closed input location good.offset good.locations good.roots good.parentless forest good.profile
  refine ⟨facts.1,?_⟩
  apply GeneralBorrowReadNoopCache.selected_unique input.tree location input.parent {}
    .VisitChildrenOfAccessed GeneralBorrowWildcardLeaf.unique forest
    (GeneralBorrowSharedGeneratorProfile.read_owned input location good.parentless good.profile)
    good.profile.rootStored rfl
  intro event member index node converted present different exposed
  exact ⟨GeneralBorrowFreshAnchor.sharedState,good.profile.shared index node present different,rfl⟩
end DuplicatePrefix.GeneralBorrowProfileReadCache
