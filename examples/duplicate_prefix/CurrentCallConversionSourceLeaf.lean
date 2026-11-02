import duplicate_prefix.CurrentCallConversionSourceCheckpoint
import duplicate_prefix.S03ReturnChildMetadata

/-! The actual fresh source constructor supplies a leaf. This is derived
metadata for entry transport, rather than an extra common-checkpoint field. -/
namespace DuplicatePrefix.CurrentCallConversionSourceLeaf
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallLazySourceResources GeneralBorrowFullSharedSeed GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem stage_leaf (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (capacity offset len : UInt64) (room : global.nextPointerTag.value < 18446744073709551615)
    (stage : Stage global frame id root capacity offset len room)
    (positive : 0 < len.toNat) (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (rootBelow : root.value.toNat < global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ global.protectedTags.entries, row.1.value.toNat < global.nextPointerTag.value.toNat) :
    stage.node.children = #[] := by
  have nonzeroCapacity : capacity ≠ 0 := by
    intro zero
    rw [zero] at bounds
    simp only [UInt64.toNat_zero] at bounds
    omega
  have nonzero : len ≠ 0 := by
    intro zero
    rw [zero] at positive
    contradiction
  let tree := BorrowTree.new root (Size.ofBytes capacity)
  have shape := GeneralBorrowFullSharedSeed.tree_eq capacity nonzeroCapacity root
  change tree = _ at shape
  have runtime := PositiveGlobalFnEntryInput.new_runtime root capacity nonzeroCapacity global rootBelow protectorBelow
  obtain ⟨C, complete⟩ := (positive_global_rule ".CurrentCallLazySourceResources.root_completion")
    root capacity nonzeroCapacity global runtime
  have order := (positive_global_rule ".CurrentCallLazySourceResources.root_order") root capacity nonzeroCapacity
  have rootAt : tree.nodes.get allocationRoot = some (GeneralBorrowFullSharedSeed.node root) := BorrowTree.new_root_node _ _
  have path : Path tree allocationRoot allocationRoot := .refl _ _ rootAt
  have short : tree.nodes.size < 65536 := by rw [shape]; change (1 : Nat) < 65536; decide
  have nodeRoom : tree.nodes.size + 1 ≤ 4294967295 := by rw [shape]; change (2 : Nat) ≤ 4294967295; decide
  have bound : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat := by rw [shape]; exact bounds
  have oldOwned := (positive_global_rule ".CurrentCallLazySourceResources.seed_owned")
    root capacity offset len nonzeroCapacity global.protectedTags C
  obtain ⟨_, readRuntime, _, _, readNodes, _, readTags, readCapacity⟩ :=
    S05ConcreteFnEntryRaw.prepare_read tree global frame id C runtime complete order
      0 allocationRoot allocationRoot (GeneralBorrowFullSharedSeed.node root) (GeneralBorrowFullSharedSeed.node root)
      rfl rootAt rootAt path room offset len bound oldOwned short .VisitChildrenOfAccessed
  let accessed := (CurrentCallTypedFnEntry.literal tree global frame id room (.concrete id root) offset len).access.tree
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed (GeneralBorrowFnEntryRegistration.registered global frame id room).1 at readRuntime
  change accessed.nodes = tree.nodes at readNodes
  change accessed.tagMapping = tree.tagMapping at readTags
  change accessed.locations.size = tree.locations.size at readCapacity
  have parentAt : accessed.nodeAt allocationRoot = some (GeneralBorrowFullSharedSeed.node root) := by
    change accessed.nodes.get _ = _
    rw [readNodes]
    exact rootAt
  have tagged := readRuntime.formed.allocator.nodeTags allocationRoot _ parentAt
  obtain ⟨_, _, _, _, _, fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame id room runtime
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tagMapping global.nextPointerTag := by rw [readTags]; exact fresh
  have afterRoom : accessed.nodes.size + 1 ≤ 4294967295 := by rw [readNodes]; exact nodeRoom
  have afterBound : offset.toNat + len.toNat ≤ accessed.locations.size.bytes.toNat := by rw [readCapacity]; exact bound
  obtain ⟨child, node, lookup, present, _, _, leaf, _, _⟩ :=
    S03ReturnChildMetadata.construct accessed _ readRuntime root global.nextPointerTag allocationRoot
      (GeneralBorrowFullSharedSeed.node root) tagged parentAt afterFresh afterRoom offset len nonzero afterBound
  have normalized := CurrentCallTypedFnEntry.literal_operation tree global frame id room (.concrete id root) offset len
  change GeneralBorrowForestFnEntry.operation tree global frame id root offset len .VisitChildrenOfAccessed = .ok _ at normalized
  have outputEq : stage.output = CurrentCallTypedFnEntry.literal tree global frame id room (.concrete id root) offset len :=
    Except.ok.inj (stage.operation.symm.trans normalized)
  have treeEq : (accessed.newChild (Size.ofBytes offset) (.concrete root) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree =
      stage.output.child.tree := by rw [outputEq]; rfl
  rw [treeEq] at lookup present
  have childEq : child = stage.child := Option.some.inj (lookup.symm.trans (stage.tag ▸ stage.lookup))
  subst child
  have nodeEq : node = stage.node := Option.some.inj (present.symm.trans stage.nodeAt)
  rw [← nodeEq]
  exact leaf

end DuplicatePrefix.CurrentCallConversionSourceLeaf

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionSourceLeaf.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved fresh source leaf dependency {name}: {dependency}"
