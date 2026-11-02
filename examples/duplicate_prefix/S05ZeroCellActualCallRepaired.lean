import duplicate_prefix.S05ZeroCellActualCallAsMutReturn
import duplicate_prefix.GenericCopyMemoryCore
import Init.Internal.Order.While

/-! Revised-state copy regression, not a new whole-call Result theorem.
That old-only error module is retired on this explicitly repaired revision.
The actual generated AsMut Return tree is retained as the input below; no old
literal tree, stronger valid-input domain or whole-call completion is asserted. -/
namespace DuplicatePrefix.S05ZeroCellActualCallRepaired.PureTree
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def tree : BorrowTree := S05ZeroCellActualCallAsMutReturn.PureTree.released.tree
def tag : BorTag := S05ZeroCellActualCallAsMutReturn.PureTree.helperTracker.global.nextPointerTag
def held : ProtectedTags := (S05ZeroCellActualCallAsMutReturn.PureTree.heldGlobal.endCall
  (({} : FrameState).addProtector S05ZeroCellJointPacket.sourceId tag)).protectedTags
def read := tree.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes 1) .Read held .VisitChildrenOfAccessed
def write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes 1) (Size.ofBytes 1) .Write held .VisitChildrenOfAccessed

theorem read_completed : read.status = .Completed := by cbv
theorem write_completed : write.status = .Completed := by cbv
/-- The repair preserves the generated pointer graph and its tag identities. -/
theorem graph_preserved : write.tree.nodes = tree.nodes ∧ write.tree.tagMapping = tree.tagMapping := by cbv

end DuplicatePrefix.S05ZeroCellActualCallRepaired.PureTree

namespace DuplicatePrefix.S05ZeroCellActualCallRepaired
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Input
open CanonicalCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def copyEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {S05ZeroCellActualCallLenReturn.source with allocation := S05ZeroCellActualCallLenReturn.source.allocation.setExtra PureTree.tree}
def copyTracker : MachineHooks.BorrowState :=
  ⟨S05ZeroCellActualCallAsMutReturn.PureTree.heldGlobal.endCall
    (({} : FrameState).addProtector S05ZeroCellJointPacket.sourceId PureTree.tag),.Default⟩

/-- Actual byte copy succeeds from this generated AsMut-return tree and keeps
both access effects. Preconditions are resource bindings, not success premises. -/
theorem actual_state_copy_completed {Os R P H D O Aff B Host : Type}
    (ctx : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (width : ctx.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some copyTracker)
    (extras : (ctx.extras.get state.machine.user).allocations.find? (fun row => row.1 == S05ZeroCellJointPacket.sourceId) =
      some (S05ZeroCellJointPacket.sourceId, ⟨none,#[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == S05ZeroCellJointPacket.sourceId) = some (S05ZeroCellJointPacket.sourceId,copyEntry))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == S05ZeroCellJointPacket.sourceId) =
      some ⟨S05ZeroCellJointPacket.sourceId,4096⟩) :
    ∃ after result,
      GlobalMemoryCopyMachine.genericCopy ctx.access PointerMachine.User.addresses ctx.pointers.arithmetic
        (Pointer.new (some (.concrete S05ZeroCellJointPacket.sourceId PureTree.tag)) (Size.ofBytes 4096))
        (Pointer.new (some (.concrete S05ZeroCellJointPacket.sourceId PureTree.tag)) (Size.ofBytes 4097))
        (Size.ofBytes 1) 1 true state = .ok () after ∧
      after.machine.memory.live.find? (fun row => row.1 == S05ZeroCellJointPacket.sourceId) =
        some (S05ZeroCellJointPacket.sourceId,⟨copyEntry.kind,result⟩) ∧
      result.extra = PureTree.write.tree ∧ result.byteSize = Size.ofBytes 2 ∧ result.len = 2 := by
  obtain ⟨result,run,bytes,len,extra,_⟩ := GenericCopyMemoryCore.interval ctx state copyTracker
    S05ZeroCellJointPacket.sourceId PureTree.tag 4096 0 1 copyEntry.kind copyEntry.allocation
    width (by decide) (by change 0+1+1 ≤ 2; decide) (by rfl)
    (by cbv) (by rfl) (by cbv)
    (by
      change ProvenanceCopy.WellFormed (ProvenanceMap.new : ProvenanceMap Provenance) 2
      constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers])
    (by change 2+64 < 18446744073709551616; decide)
    (by rfl) noClocks noBackend tracked extras live cached PureTree.read_completed PureTree.write_completed
  refine ⟨_,result,run,replace_lookup _ _ _ _,extra,bytes,len⟩

end DuplicatePrefix.S05ZeroCellActualCallRepaired
