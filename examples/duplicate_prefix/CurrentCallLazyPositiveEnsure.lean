import duplicate_prefix.PositiveGlobalTypedReborrow
import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.S03MaterializableRootRuntime
namespace DuplicatePrefix.CurrentCallLazyPositiveEnsure
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CanonicalConfigFacts GeneralBorrowFullSharedSeed GeneralRangeMapState GeneralRangeMapOrigins OrdinaryBorrowAuthority
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

private theorem seed_owned (tag : BorTag) (capacity offset len : UInt64) (nonzero : capacity≠0)
    (held : ProtectedTags) (completion : Completion) :
    OwnedOn (Authority (BorrowTree.new tag (Size.ofBytes capacity)) completion held allocationRoot)
      offset (offset+len) (BorrowTree.new tag (Size.ofBytes capacity)).locations := by
  have shape := tree_eq capacity nonzero tag
  change BorrowTree.new tag (Size.ofBytes capacity)=_ at shape
  intro position valid positive start stop index node present
  have positionZero : position=0 := by rw [shape] at valid;change position<1 at valid;omega
  subst position
  have bounded := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes index node present
  rw [shape] at bounded
  have indexZero : index=allocationRoot := GeneralBorrowNodeUpdate.index_injective index allocationRoot (by change index.toNat=0;change index.toNat<1 at bounded;omega)
  subst index
  have actual : node=GeneralBorrowFullSharedSeed.node tag := by rw [shape] at present;exact (Option.some.inj present).symm
  subst node
  refine ⟨?_,fun outside=>False.elim (outside (.refl allocationRoot))⟩
  intro below
  simp only [shape]
  change LocalWrite GeneralBorrowWildcardLeaf.unique (held.contains tag)
  simp [LocalWrite,GeneralBorrowWildcardLeaf.unique,LocationState.possible,Permission.isUnique]

private theorem seed_embeds (allocation : Allocation Provenance BorrowTree) (capacity : UInt64)
    (rootTag : BorTag) (nonzero : capacity≠0) (shape : allocation.extra=BorrowTree.new rootTag (Size.ofBytes capacity))
    (held : ProtectedTags) (completion : Completion) (byte : Nat) :
    Embeds allocation held completion allocationRoot byte .exclusive := by
  have model := tree_eq capacity nonzero rootTag
  change BorrowTree.new rootTag (Size.ofBytes capacity)=_ at model
  intro segment member start stop index node present
  rw [shape,model] at member present
  have segmentEq : segment=⟨⟨0,capacity⟩,GeneralBorrowFullSharedSeed.location⟩ := by
    simpa only [RangeMapNonempty.homogeneous,List.mem_singleton] using member
  subst segment
  have bounded := GeneralBorrowNodeUpdate.lookup_valid (⟨#[some (GeneralBorrowFullSharedSeed.node rootTag)]⟩ : UniValMap TreeNode) index node present
  have same : index=allocationRoot := GeneralBorrowNodeUpdate.index_injective index allocationRoot (by change index.toNat=0;change index.toNat<1 at bounded;omega)
  subst index
  have actual : node=GeneralBorrowFullSharedSeed.node rootTag := (Option.some.inj present).symm
  subst node
  refine ⟨?_,fun _=>Below.refl allocationRoot⟩
  intro _
  change .exclusive∈tokens (denote GeneralBorrowWildcardLeaf.unique (held.contains rootTag))
  simp [tokens,denote,GeneralBorrowWildcardLeaf.unique]

/-- The real inner ensure action supplies actual root resources on its exact
post-state. Descriptor storage entitlement and cache/image representation stay
explicit; this neither prewarms the original caller nor creates an initial live loan. -/
theorem ensure (options : EvalConfigurationCore.Options) (choice : Unit) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (rootTag : BorTag) (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker=some tracker) (rootCached : tracker.global.rootTag? id=some rootTag)
    (race : before.machine.dataRace=none)
    (noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id))=false)
    (absent : before.machine.memory.live.find? (fun row=>row.1==id)=none)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor (DuplicatePrefixCallSpecification.imageContext options before.machine tracker) before.machine.memory id source)
    (base offset len : UInt64)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (addressRoom : base.toNat+source.len<2^64) (nonnull : base+offset≠0)
    (window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len)
    (storage : source.len=source.byteSize.bytes.toNat) (mutable : source.mutability=.Mut)
    (rootBelow : rootTag.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (protectors : ∀ row∈tracker.global.protectedTags.entries,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat) :
    ∃ converted : Allocation Provenance Unit,GlobalAllocationAttributes.Attributes source converted ∧
    let allocation := converted.mapExtra (fun _=>BorrowTree.new rootTag source.byteSize)
    let after := GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine id .global allocation
    let pointer : PointerInstance := ⟨id,Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)),allocationRoot⟩
    (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before=.ok () {before with machine:=after} ∧
    after.memory.live.find? (fun row=>row.1==id)=some (id,⟨.machine .global,allocation⟩) ∧
    AllocationCapability after tracker id allocation ∧
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
    PointerBinds allocation pointer ∧ CandidateCallBindings.WindowBinding after pointer.value id offset.toNat len.toNat ∧
    DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len ∧ allocation.mutability=.Mut ∧
    (∀ completion,SpatialDelegation after tracker id allocation completion allocationRoot ∧
      OwnedOn (Authority allocation.extra completion tracker.global.protectedTags allocationRoot) offset (offset+len) allocation.extra.locations ∧
      ∀ byte,Embeds allocation tracker.global.protectedTags completion allocationRoot byte .exclusive) := by
  obtain ⟨converted,attributes,actual,live,positive,length,writable⟩ := PositiveGlobalMaterialization.ensure_positive options choice remaining span before tracker id rootTag source
    supported enabled rootCached race noExtras absent descriptor offset len window storage mutable
  let allocation := converted.mapExtra (fun _=>BorrowTree.new rootTag source.byteSize)
  let after := GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine id .global allocation
  have nonzero : source.byteSize.bytes≠0 := by
    intro zero
    have bounds := window.bounds
    rw [zero] at bounds
    have positive := window.positive
    simp only [UInt64.toNat_zero] at bounds
    omega
  have shape := tree_eq source.byteSize.bytes nonzero rootTag
  change BorrowTree.new rootTag (Size.ofBytes source.byteSize.bytes)=_ at shape
  have treeSize : allocation.extra.locations.size=allocation.byteSize := by
    change (BorrowTree.new rootTag source.byteSize).locations.size=converted.byteSize
    rw [attributes.size]
    exact (by rw [show source.byteSize=Size.ofBytes source.byteSize.bytes from rfl,shape];rfl)
  have cap : AllocationCapability after tracker id allocation := by
    refine ⟨?_,length,treeSize,rfl,_,BorrowTree.new_root_node _ _,rfl,rfl,rootCached⟩
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,⟨.machine .global,allocation⟩),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have runtime := S03MaterializableRootRuntime.initial rootTag source.byteSize.bytes tracker.global rootBelow protectors
  have pointerBind : PointerBinds allocation ⟨id,Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)),allocationRoot⟩ := by
    refine ⟨_,BorrowTree.new_root_node _ _,?_,rfl,rfl⟩
    exact runtime.formed.allocator.nodeTags allocationRoot _ (BorrowTree.new_root_node _ _)
  have offsetBound : offset.toNat≤source.len := by
    have bounds := window.bounds
    rw [storage]
    omega
  have sumFits : base.toNat+offset.toNat<2^64 := by omega
  have binding : CandidateCallBindings.WindowBinding after (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) id offset.toNat len.toNat := by
    refine ⟨⟨.machine .global,allocation⟩,base,live,cached,length,?_,?_,?_,nonnull,rfl⟩
    · change base.toNat+converted.len<2^64
      rw [attributes.storage]
      exact addressRoom
    · change offset.toNat+len.toNat≤converted.len
      rw [attributes.storage,storage]
      exact window.bounds
    · change (base+offset).toNat=base.toNat+offset.toNat
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]
  refine ⟨converted,attributes,actual,live,cap,runtime,pointerBind,binding,positive,writable,?_⟩
  intro completion
  exact ⟨.allocated cap,seed_owned rootTag source.byteSize.bytes offset len nonzero tracker.global.protectedTags completion,
    fun byte=>seed_embeds allocation source.byteSize.bytes rootTag nonzero rfl tracker.global.protectedTags completion byte⟩

end
end DuplicatePrefix.CurrentCallLazyPositiveEnsure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLazyPositiveEnsure" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved lazy positive ensure dependency {dependency}"
