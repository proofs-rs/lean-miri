import duplicate_prefix.GlobalDataOnlyActualConfig
import duplicate_prefix.StaticGlobalActualConfig
import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.DuplicatePrefixSliceStorage

namespace DuplicatePrefix.PositiveGlobalMaterialization
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual image conversion preserves every positive u8 window's mask/bounds,
backing size and mutability. It does not manufacture provenance-map WF or borrow
ownership from allocation attributes. Relocation support remains explicit in
the materialization theorem below. -/
theorem positive_attributes (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (root : BorTag) (offset len : UInt64)
    (attributes : GlobalAllocationAttributes.Attributes source converted)
    (window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len)
    (storage : source.len = source.byteSize.bytes.toNat) (mutable : source.mutability = .Mut) :
    let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
    DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len ∧
      allocation.len = allocation.byteSize.bytes.toNat ∧ allocation.mutability = .Mut := by
  change DuplicatePrefixSliceStorage.Positive converted.initializationMask converted.byteSize.bytes offset len ∧
    converted.len = converted.byteSize.bytes.toNat ∧ converted.mutability = .Mut
  rw [attributes.mask, attributes.size, attributes.storage, attributes.mutability]
  exact ⟨window, storage, mutable⟩

/-- Positive-length MEMORY and supported non-TLS/non-extern STATIC images are
not required to be live initially. The actual fixed ensureTreeExtra operation
materializes their original exported bytes, creates the real root tree and
extras, and supplies the exact live lookup plus positive writable-u8 storage.
Every success and live row is derived; no operation-success premise occurs.

This is state-changing normalization at the actual ensure endpoint. It does
NOT construct a live-only Input on the original absent-allocation prestate,
insert an extra operation into the call, prove later FnEntry/call equivalence,
or establish coverage of unsupported/TLS/extern/fragmented images. Supported
relocation/image metadata and source storage validity are explicit premises. -/
theorem ensure_positive (options : EvalConfigurationCore.Options) (choice : Unit)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.machine.dataRace = none)
    (noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any
      (fun row => row.1 == id)) = false)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor
      (DuplicatePrefixCallSpecification.imageContext options before.machine tracker) before.machine.memory id source)
    (offset len : UInt64)
    (window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len)
    (storage : source.len = source.byteSize.bytes.toNat) (mutable : source.mutability = .Mut) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
      let after := GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
        before.machine id .global allocation
      (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before =
        .ok () {before with machine := after} ∧
      after.memory.live.find? (fun row => row.1 == id) = some (id, ⟨.machine .global, allocation⟩) ∧
      DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len ∧
      allocation.len = allocation.byteSize.bytes.toNat ∧ allocation.mutability = .Mut := by
  have materialized : ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before =
        .ok () {before with machine := (GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
          before.machine id .global (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))} := by
    rcases descriptor with memoryDescriptor | ⟨definition, initializer, staticDescriptor⟩
    · exact GlobalDataOnlyActualConfig.ensure_success options choice remaining span before tracker id root source
        supported enabled rootCached race noExtras absent memoryDescriptor
    · exact StaticGlobalActualConfig.ensure_success options choice remaining span before tracker id root source definition
        initializer supported enabled rootCached race noExtras absent staticDescriptor
  obtain ⟨converted, attributes, actual⟩ := materialized
  refine ⟨converted, attributes, actual, ?_, ?_⟩
  · exact MemoryCopyBridge.live_lookup_replaced before.machine.memory id _
  · exact positive_attributes source converted root offset len attributes window storage mutable

end DuplicatePrefix.PositiveGlobalMaterialization
