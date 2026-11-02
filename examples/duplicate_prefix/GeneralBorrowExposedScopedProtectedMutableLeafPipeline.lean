import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableLeafConstructor
import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafRun
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableLeafPipeline
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def mutableInput (input : GeneralBorrowFreshMetadataChildDefault.Input) : GeneralBorrowFreshMetadataChildMutable.Input :=
  ⟨input.tree,input.depth,input.children,input.covered,input.parentTag,input.newTag,input.parent,input.parentNode,
    input.parentTagPresent,input.parentPresent,input.fresh,input.noFree,input.aligned,input.fits,input.offset,input.len,
    input.nonzero,input.well,input.bounds⟩

def mutableResources (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail) :
    GeneralBorrowExposedScopedProtectedMutableLeafConstructor.Resources (mutableInput input) protections selected head tail :=
  ⟨raw.forest,raw.component,raw.selectedNode,raw.selectedPresent,raw.roots,raw.rootPath,raw.hidden,raw.separate,
    raw.tags,raw.leaves,raw.unique,raw.first,raw.rest,raw.coherent,raw.owned,raw.room⟩

/-- The actual registered parent Read and protected mutable constructor form
full fresh-child Write inputs. Only initial exposed-leaf resources are used. -/
theorem run (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail)
    (atBase : input.offset = 0) (full : input.len = input.tree.locations.size.bytes) (mode : ChildrenVisitMode) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child.tree (GeneralBorrowFreshMetadataChildDefault.index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedKnownRootRangeData.Data child.tree location protections
          (GeneralBorrowFreshMetadataChildDefault.index input) selected head tail .Write))
          input.offset (input.offset+input.len) child.tree.locations := by
  obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full mode
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedProtectedMutableLeafConstructor.construct (mutableInput next)
    protections selected head tail (mutableResources next protections selected head tail nextRaw)
  have childEq : GeneralBorrowFreshMetadataChildMutable.result (mutableInput next) =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,mutableInput,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  have indexSame : GeneralBorrowFreshMetadataChildMutable.index (mutableInput next) = GeneralBorrowFreshMetadataChildDefault.index input := indexEq
  rw [childEq,indexSame] at context owned
  simp only [mutableInput,offsetEq,lenEq] at owned success
  refine ⟨readDone,?_,context,owned⟩
  simpa only [treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using success
end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableLeafPipeline
