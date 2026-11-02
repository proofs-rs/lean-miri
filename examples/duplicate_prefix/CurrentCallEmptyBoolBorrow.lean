import duplicate_prefix.CurrentCallResourceFnEntry

/-! The immediate Bool operation after an actual empty argument copy. The
current one-byte resource supplies bounds internally; no source resource or
successful access/constructor result is a premise. -/
namespace DuplicatePrefix.CurrentCallEmptyBoolBorrow
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Reuse the same actual post-copy Bool window. All capacities are current
representation budgets; the actual associated Read and protected constructor
are derived by the existing FnEntry operation theorem. -/
theorem invoke {post tracker data owner id offset}
    (B : UniformWindow post tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (short : B.allocation.extra.nodes.size < 65536)
    (nodeRoom : B.allocation.extra.nodes.size+1 ≤ 4294967295) :
    ∃ output child,
      CandidateCurrentFnEntryRaw.operation B.allocation.extra tracker.global frame id B.pointer.value.provenance
        (UInt64.ofNat offset) 1 = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered tracker.global frame id room).1 ∧
      output.frame = (GeneralBorrowFnEntryRegistration.registered tracker.global frame id room).2 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      output.child.tree.indexOfTag output.tag = some child ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness B output child (UInt64.ofNat offset) 1) := by
  have bound := (B.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have cap := B.issued.capability
  have extent := cap.extent
  have treeExtent := cap.treeExtent
  have capacity := UInt64.toNat_lt B.allocation.byteSize.bytes
  have offsetFits : offset < 2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat = offset := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have bounds : (UInt64.ofNat offset).toNat+(1 : UInt64).toNat ≤ B.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,treeExtent,←extent]
    change offset+1 ≤ B.allocation.len
    omega
  exact CurrentCallResourceFnEntry.correlated_borrow_selected B runtime frame room (by rfl) distinct short nodeRoom
    (UInt64.ofNat offset) 1 startEq rfl (by decide) bounds

end DuplicatePrefix.CurrentCallEmptyBoolBorrow
