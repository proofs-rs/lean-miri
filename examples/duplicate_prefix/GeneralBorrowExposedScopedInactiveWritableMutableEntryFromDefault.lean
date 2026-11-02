import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryFromDefault
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]

/-- The ordinary input packet supplies the protected FnEntry input metadata
and initial resources verbatim; no operation outcome or stronger profile is
introduced by selecting the actual protected constructor policy. -/
def mutableInput (input : GeneralBorrowFreshMetadataChildDefault.Input) : GeneralBorrowFreshMetadataChildMutable.Input :=
  ⟨input.tree,input.depth,input.children,input.covered,input.parentTag,input.newTag,input.parent,input.parentNode,
    input.parentTagPresent,input.parentPresent,input.fresh,input.noFree,input.aligned,input.fits,input.offset,input.len,
    input.nonzero,input.well,input.bounds⟩

def mutableResources {profileMode : ProfileMode} (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableDefaultConstructor.ResourcesFor input protections selected head tail profileMode) :
    GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor
      (mutableInput input) protections selected head tail profileMode :=
  ⟨raw.forest,raw.component,raw.selectedNode,raw.selectedPresent,raw.roots,raw.rootPath,raw.exposures,raw.separate,
    raw.tags,raw.leaves,raw.writableLeaves,raw.first,raw.rest,raw.coherent,raw.owned,raw.room⟩

def convert {profileMode : ProfileMode} (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw.DataFor tree protections parentTag newTag offset len selected head tail profileMode) :
    GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw.DataFor tree protections parentTag newTag offset len selected head tail profileMode := {
  input:=mutableInput data.input
  treeEq:=data.treeEq
  parentTagEq:=data.parentTagEq
  newTagEq:=data.newTagEq
  offsetEq:=data.offsetEq
  lenEq:=data.lenEq
  resources:=mutableResources data.input protections selected head tail data.resources
  nodeTags:=data.nodeTags }

theorem index {profileMode : ProfileMode} (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw.DataFor tree protections parentTag newTag offset len selected head tail profileMode) :
    GeneralBorrowFreshMetadataChildMutable.index (convert tree protections parentTag newTag offset len selected head tail data).input=
      GeneralBorrowFreshMetadataChildDefault.index data.input := rfl
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryFromDefault
