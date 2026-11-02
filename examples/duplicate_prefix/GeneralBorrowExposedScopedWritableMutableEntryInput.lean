import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultConstructor
import duplicate_prefix.GeneralBorrowExposedScopedWritableProtectedMutableProtect
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryInput
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def mutableInput (input : GeneralBorrowFreshMetadataChildDefault.Input) : GeneralBorrowFreshMetadataChildMutable.Input :=
  ⟨input.tree,input.depth,input.children,input.covered,input.parentTag,input.newTag,input.parent,input.parentNode,
    input.parentTagPresent,input.parentPresent,input.fresh,input.noFree,input.aligned,input.fits,input.offset,input.len,
    input.nonzero,input.well,input.bounds⟩

def mutableResources (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail) :
    GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources (mutableInput input) protections selected head tail :=
  ⟨raw.forest,raw.component,raw.selectedNode,raw.selectedPresent,raw.roots,raw.rootPath,raw.hidden,raw.separate,
    raw.tags,raw.leaves,raw.writableLeaves,raw.first,raw.rest,raw.coherent,raw.owned,raw.room⟩

/-- Actual tag freshness and source node/tag lookup derive fresh Strong
registration for the whole mixed writable-leaf constructor resources. -/
theorem register (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input protections selected head tail)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    ∃ held : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input
      (protections.insert input.newTag .StrongProtector) selected head tail,
      held.component.support=raw.component.support := by
  apply GeneralBorrowExposedScopedWritableProtectedMutableProtect.protect input protections input.newTag selected head tail raw
  intro index node present same
  have mapped:=nodeTags index node present
  have absent : input.tree.tagMapping.get input.newTag=none := by
    simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  rw [same,absent] at mapped
  cases mapped
end DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryInput
