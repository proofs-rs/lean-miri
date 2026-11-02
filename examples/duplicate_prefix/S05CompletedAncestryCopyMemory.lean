import duplicate_prefix.GenericCopyMemoryCore
import duplicate_prefix.S05CompletedAncestryCopyBorrow

/-! The existing generic machine copy consumes borrowing derived from initial
raw buffer authority. Read/Write success equations are internal proof results,
not caller obligations. Physical storage and fixed-configuration premises are
unchanged from the original machine-copy theorem. -/
namespace DuplicatePrefix.S05CompletedAncestryCopyMemory
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter Miri.Concurrency Miri.Input
open DuplicatePrefix.CanonicalCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem interval {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (completion : CandidateStableCallOwnership.Completion)
    (complete : CandidateStableCallOwnership.Completes allocation.extra completion)
    (formed : GeneralBorrowStructuralHistoryState.GraphState allocation.extra)
    (depth : GeneralBorrowExposure.ParentDepth allocation.extra.nodes)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder allocation.extra)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : allocation.extra.roots[selectedPosition]? = some selected)
    (selectedPresent : allocation.extra.nodes.get selected = some selectedNode)
    (sourcePresent : allocation.extra.nodes.get source = some sourceNode) (sourceTagged : sourceNode.tag = tag)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path allocation.extra selected source)
    (sliceLen : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible allocation.extra location ∧
      ∀ index node, allocation.extra.nodes.get index = some node →
        (CandidateStableCallOwnership.Below completion index source → OrdinaryBorrowAuthority.LocalWrite
          ((location.perms.get index).getD node.defaultLocationState) (tracker.global.protectedTags.contains node.tag)) ∧
        (¬CandidateStableCallOwnership.Below completion index source → OrdinaryBorrowAuthority.ForeignWrite
          ((location.perms.get index).getD node.defaultLocationState) (tracker.global.protectedTags.contains node.tag)))
      offset (offset+sliceLen) allocation.extra.locations)
    (well : allocation.extra.locations.WellFormed)
    (runtime : GeneralRangeMapState.Every (fun location =>
      GeneralBorrowExposureCardinality.LocationCoherent allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile allocation.extra location tracker.global.protectedTags) allocation.extra.locations)
    (borrowBounds : offset.toNat+sliceLen.toNat ≤ allocation.extra.locations.size.bytes.toNat)
    (twice : n.toNat+n.toNat ≤ sliceLen.toNat) (short : allocation.extra.nodes.size < 65536) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := replaceAllocation readState id kind writeAlloc
    ∃ result,
      GlobalMemoryCopyMachine.genericCopy context.access PointerMachine.User.addresses
        context.pointers.arithmetic (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset)))
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + (offset + n)))) (Size.ofBytes n) 1 true state =
        .ok () (replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have borrowed := S05CompletedAncestryCopyBorrow.accesses allocation.extra completion tracker.global.protectedTags
    complete formed depth order selectedPosition selected source selectedNode sourceNode selectedSlot selectedPresent
    sourcePresent sourcePath offset sliceLen n owned well runtime borrowBounds twice short
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [sourceTagged] using borrowed.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [sourceTagged] using borrowed.2.1
  exact GenericCopyMemoryCore.interval context state tracker id tag base offset n kind allocation width positive bounded
    storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached readValid writeValid

end DuplicatePrefix.S05CompletedAncestryCopyMemory

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryCopyMemory." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved copy-machine dependency {dependency}"
