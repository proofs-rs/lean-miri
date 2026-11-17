import duplicate_prefix.PositiveGlobalMaterialization
import duplicate_prefix.GeneralBorrowRawFnEntry
import duplicate_prefix.GeneralBorrowExposureAllocation

namespace DuplicatePrefix.PositiveGlobalFnEntryInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowProjection GeneralBorrowFullSharedSeed
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual freshly materialized global root supplies positive normal ownership
at every interior byte window. There are no foreign roots or exposed callbacks;
the existing protector table is arbitrary, including protection of this root. -/
theorem new_positive (tag : BorTag) (capacity offset len : UInt64)
    (protections : ProtectedTags) (positive : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    DuplicatePrefixBorrowAuthorization.Positive (BorrowTree.new tag (Size.ofBytes capacity))
      protections (some root) (some root) (some tag) offset len := by
  have nonzero : capacity ≠ 0 := by intro zero; rw [zero] at bounds; simp only [UInt64.toNat_zero] at bounds; omega
  have model := tree_eq capacity nonzero tag
  change tree capacity nonzero tag = _ at model
  let component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection (tree capacity nonzero tag) default protections).topology root.toNat := {
    support := fun _ => True
    anchor := trivial
    parents := by intro current supported parent edge; trivial
    children := by intro current supported child member; trivial }
  have row : DuplicatePrefixBorrowAuthorization.Row (tree capacity nonzero tag) location protections
      (some root) (some root) (some tag) := by
    refine {wildcard := ?_,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := ?_}
    · intro impossible; cases impossible
    · intro anchor same
      have equal : anchor = root := Option.some.inj same.symm
      subst anchor
      rw [model]
      with_unfolding_all rfl
    · intro selected same
      have equal : selected = root := Option.some.inj same.symm
      subst selected
      exact ⟨node tag, by rw [model]; rfl⟩
    · rw [model]
      rfl
    · intro anchor same
      have equal : anchor = root := Option.some.inj same.symm
      subst anchor
      refine ⟨⟨component, ?_⟩⟩
      intro kind index supported bounded
      have zero : index = 0 := by rw [model] at bounded; change index < 1 at bounded; omega
      subst index
      refine ⟨GeneralBorrowWildcardLeaf.unique, ?_, ?_⟩
      · rw [projection_state _ _ _ 0 root (node tag) (by rfl) rfl (by rw [model]; rfl)]
        rfl
      · have localRelation : GeneralBorrowAnchor.relation
            (source_normal_projection (tree capacity nonzero tag) location protections) root.toNat 0 = .LocalAccess := by
          rw [model]
          with_unfolding_all rfl
        rw [localRelation]
        cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,
          GeneralBorrowProtectedReadCompatible.Compatible, GeneralBorrowExposedConditionalWritePermissions.Compatible,
          GeneralBorrowWildcardLeaf.unique, LocationState.possible, Permission.isUnique]
    · intro position valid different
      have zero : position = 0 := by rw [model] at valid; change position < 1 at valid; omega
      subst position
      have first : (tree capacity nonzero tag).roots[0] = root := by simp only [model]; rfl
      exact False.elim (different (congrArg some first).symm)
  refine {positive := positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}
  · change offset.toNat + len.toNat ≤ (tree capacity nonzero tag).locations.size.bytes.toNat
    rw [model]
    exact bounds
  · intro anchor same
    have equal : anchor = root := Option.some.inj same.symm
    subst anchor
    exact ⟨node tag, by change (tree capacity nonzero tag).nodeAt root = _; rw [model]; rfl⟩
  · intro impossible; cases impossible
  · change GeneralRangeMapOrigins.OwnedOn (fun loc => Nonempty
      (DuplicatePrefixBorrowAuthorization.Row (tree capacity nonzero tag) loc protections
        (some root) (some root) (some tag))) offset (offset+len) (tree capacity nonzero tag).locations
    intro position valid nonempty start stop
    have zero : position = 0 := by rw [model] at valid; change position < 1 at valid; omega
    subst position
    have actualLocation : (tree capacity nonzero tag).locations.entries[0].data = location := by
      simp only [model]
      rfl
    rw [actualLocation]
    exact ⟨row⟩

/-- Runtime consistency of the actual new root is derived from allocation
formation. Only raw global tag/protector high-water and capacity facts remain;
no post-materialization runtime or ownership certificate is assumed. -/
theorem new_runtime (tag : BorTag) (capacity : UInt64) (nonzero : capacity ≠ 0)
    (global : GlobalState) (rootBelow : tag.value.toNat < global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ global.protectedTags.entries,
      row.1.value.toNat < global.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts (BorrowTree.new tag (Size.ofBytes capacity)) global := by
  have model := tree_eq capacity nonzero tag
  refine {
    formed := GeneralBorrowStructuralHistorySifaState.initial tag _ global.protectedTags
    coherent := GeneralBorrowExposureAllocation.coherent capacity tag global.protectedTags
    possible := ?_
    below := ⟨?_, protectorBelow⟩ }
  · intro position valid query value present
    change position < (tree capacity nonzero tag).locations.entries.size at valid
    have zero : position = 0 := by rw [model] at valid; change position < 1 at valid; omega
    subst position
    have bound := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes query value present
    change query.toNat < (tree capacity nonzero tag).nodes.data.size at bound
    rw [model] at bound
    have same : query = root := GeneralBorrowNodeUpdate.index_injective query root (by change query.toNat = 0; change query.toNat < 1 at bound; omega)
    subst query
    have rootPresent : (BorrowTree.new tag (Size.ofBytes capacity)).nodeAt root = some (node tag) := by
      change (tree capacity nonzero tag).nodeAt root = _
      rw [model]
      rfl
    have equal : value = node tag := Option.some.inj (present.symm.trans rootPresent)
    subst value
    have actualLocation : (tree capacity nonzero tag).locations.entries[0].data = location := by
      simp only [model]
      rfl
    change (((tree capacity nonzero tag).locations.entries[0].data.perms.get root).getD (node tag).defaultLocationState).possible = true
    rw [actualLocation]
    rfl
  · intro row member
    change row ∈ (tree capacity nonzero tag).tagMapping.mapping at member
    rw [model] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact rootBelow

/-- The genuine new allocation tree supplies the raw FnEntry constructor input.
The conditional tag-order condition is vacuous because the selected root is
its first and only root; no global parent-tag law is imposed. -/
def new_input (tag : BorTag) (capacity offset len : UInt64) (global : GlobalState)
    (positive : 0 < len.toNat) (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615) :
    GeneralBorrowRawFnEntry.Input (BorrowTree.new tag (Size.ofBytes capacity)) global := {
  parentTag := tag
  parent := root
  selected := root
  maximum := some tag
  offset := offset
  len := len
  tagged := by simp [BorrowTree.indexOfTag, BorrowTree.new, UniKeyMap.get]; rfl
  positive := new_positive tag capacity offset len global.protectedTags positive bounds
  distinct := by change [root].Nodup; simp
  order := by intro valid different; exact False.elim (different rfl)
  short := by change (1 : Nat) < 65536; decide
  nodeRoom := by change (1 : Nat) + 1 ≤ 4294967295; decide
  tagRoom := tagRoom }

/-- Normalize a supported positive MEMORY/STATIC window at the actual ensure
endpoint, construct its raw FnEntry input from the real new root, and execute
the exact source protected-reborrow component. All initial and final borrow
capabilities and runtime facts are derived. Root/protector high-water and fresh
tag capacity are explicit raw global resources, not successful-operation facts.

The operation here is GeneralBorrowForestFnEntry.operation on the materialized
tree. Its later integration with typed pointer resolution and the enclosing
MIR argument/call remains separate; this does not insert a new pre-call ensure
or assert a live-only Input on the original prestate. -/
theorem ensure_fn_entry (options : EvalConfigurationCore.Options) (choice : Unit)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : CanonicalConfigFacts.RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (rootTag : BorTag) (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some rootTag)
    (race : before.machine.dataRace = none)
    (noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any
      (fun row => row.1 == id)) = false)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor
      (DuplicatePrefixCallSpecification.imageContext options before.machine tracker) before.machine.memory id source)
    (offset len : UInt64)
    (window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len)
    (storage : source.len = source.byteSize.bytes.toNat) (mutable : source.mutability = .Mut)
    (rootBelow : rootTag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (frame : FrameState) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let initialTree := BorrowTree.new rootTag source.byteSize
      let allocation := converted.mapExtra (fun _ => initialTree)
      let after := GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
        before.machine id .global allocation
      (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before =
        .ok () {before with machine := after} ∧
      after.memory.live.find? (fun row => row.1 == id) = some (id, ⟨.machine .global, allocation⟩) ∧
      DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len ∧
      allocation.len = allocation.byteSize.bytes.toNat ∧ allocation.mutability = .Mut ∧
      Nonempty (GeneralBorrowRawFnEntry.Input initialTree tracker.global) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts initialTree tracker.global ∧
      ∃ output, GeneralBorrowForestFnEntry.operation initialTree tracker.global frame id rootTag offset len
          .VisitChildrenOfAccessed = .ok output ∧
        DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
        ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
          Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
            (some child) (some root) (some rootTag) offset len) := by
  obtain ⟨converted, attributes, materialized, live, positiveWindow, physicalStorage, mutability⟩ :=
    PositiveGlobalMaterialization.ensure_positive options choice remaining span before tracker id rootTag source
      supported enabled rootCached race noExtras absent descriptor offset len window storage mutable
  have nonzero : source.byteSize.bytes ≠ 0 := by
    intro zero
    have positive := window.positive
    have bounds := window.bounds
    rw [zero] at bounds
    simp only [UInt64.toNat_zero] at bounds
    omega
  have runtime := new_runtime rootTag source.byteSize.bytes nonzero tracker.global rootBelow protectorBelow
  let raw := new_input rootTag source.byteSize.bytes offset len tracker.global window.positive window.bounds tagRoom
  obtain ⟨output, actualEntry, tag, global, owned, readDone, childDone, finalRuntime, capacity, growth,
      child, lookup, roots, finalPositive, activity⟩ :=
    GeneralBorrowRawFnEntry.invoke_positive (BorrowTree.new rootTag source.byteSize) tracker.global frame id runtime raw
  exact ⟨converted, attributes, materialized, live, positiveWindow, physicalStorage, mutability,
    ⟨raw⟩, runtime, output, actualEntry, finalRuntime, child, lookup, finalPositive⟩

end DuplicatePrefix.PositiveGlobalFnEntryInput
