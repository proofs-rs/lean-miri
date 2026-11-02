import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultConstructor
import duplicate_prefix.GeneralBorrowExposedScopedWritableProtectedMutableConstructor
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableConstructorReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual ordinary mutable construction also supplies the real Write and
Read/Write-closed inputs, without strengthening mixed old leaves to Unique. -/
theorem ordinary (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail) :
    let child:=GeneralBorrowFreshMetadataChildDefault.result input
    let anchor:=GeneralBorrowFreshMetadataChildDefault.index input
    let support:=fun position=>raw.component.support position ∨position=anchor.toNat
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside)
      (.ReservedFrz false) false).outcome=.ok () ∧
    ∃ _context : GeneralBorrowExposedKnownRootRangeData.Context child anchor selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>
        Nonempty (GeneralBorrowExposedScopedWritableReadData.Data child location protections anchor selected head tail support (fun _=>true)) ∧
        Nonempty (GeneralBorrowExposedKnownRootRangeData.Data child location protections anchor selected head tail .Write) ∧
        Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data child location protections anchor selected head tail))
        input.offset (input.offset+input.len) child.locations := by
  obtain ⟨success,context,owned⟩:=GeneralBorrowExposedScopedWritableDefaultConstructor.construct input protections selected head tail raw
  refine ⟨success,context,?_⟩
  intro position valid positive lower upper
  obtain ⟨data⟩:=owned position valid positive lower upper
  exact ⟨⟨data⟩,⟨GeneralBorrowExposedScopedWritableReadData.write _ _ _ _ _ _ _ _ context data⟩,
    ⟨GeneralBorrowExposedScopedWritableReadData.strong _ _ _ _ _ _ _ _ context data⟩⟩

/-- Actual protected mutable construction also supplies the real Write and
Read/Write-closed inputs, without strengthening mixed old leaves to Unique. -/
theorem protected_mutable (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input protections selected head tail) :
    let child:=GeneralBorrowFreshMetadataChildMutable.result input
    let anchor:=GeneralBorrowFreshMetadataChildMutable.index input
    let support:=fun position=>raw.component.support position ∨position=anchor.toNat
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside)
      (.ReservedFrz false) true).outcome=.ok () ∧
    ∃ _context : GeneralBorrowExposedKnownRootRangeData.Context child anchor selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>
        Nonempty (GeneralBorrowExposedScopedWritableReadData.Data child location protections anchor selected head tail support (fun _=>true)) ∧
        Nonempty (GeneralBorrowExposedKnownRootRangeData.Data child location protections anchor selected head tail .Write) ∧
        Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data child location protections anchor selected head tail))
        input.offset (input.offset+input.len) child.locations := by
  obtain ⟨success,context,owned⟩:=GeneralBorrowExposedScopedWritableProtectedMutableConstructor.construct input protections selected head tail raw
  refine ⟨success,context,?_⟩
  intro position valid positive lower upper
  obtain ⟨data⟩:=owned position valid positive lower upper
  exact ⟨⟨data⟩,⟨GeneralBorrowExposedScopedWritableReadData.write _ _ _ _ _ _ _ _ context data⟩,
    ⟨GeneralBorrowExposedScopedWritableReadData.strong _ _ _ _ _ _ _ _ context data⟩⟩

end DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableConstructorReady
