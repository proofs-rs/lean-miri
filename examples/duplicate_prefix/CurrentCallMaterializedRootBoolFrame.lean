import duplicate_prefix.CurrentCallEmptyMaterializedSourceFacts
import duplicate_prefix.CurrentCallMaterializedZeroParents
import duplicate_prefix.CurrentCallLiveBoolTransport
import duplicate_prefix.CurrentCallCheckpointMutableBoolFrame
import duplicate_prefix.PositiveGlobalFnEntryInput
import duplicate_prefix.PositiveGlobalTypedReborrow
import duplicate_prefix.S05CompletedRootOrigins
import duplicate_prefix.CurrentCallSpatialCover
import duplicate_prefix.CurrentCallSupportChain
import duplicate_prefix.CurrentCallResourceCopyInstall

namespace DuplicatePrefix.CurrentCallMaterializedRootBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open OrdinaryBorrowAuthority GeneralBorrowView GeneralRangeMapOrigins
open S05CompletedAncestryReadMutable
open GeneralBorrowFullSharedSeed GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05ConcreteProtectedChildCompletion
open CandidateCurrentGrantResources CurrentCallSpatialCover

open Lean Elab Term in
elab "materialized_bool_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked materialized Bool helper {suffix.getString}"
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem root_cases (tag : BorTag) (capacity : UInt64) (nonzero : capacity≠0) (index : UniIndex) (value : TreeNode)
    (present : (BorrowTree.new tag (Size.ofBytes capacity)).nodes.get index=some value) :
    index=allocationRoot ∧value=GeneralBorrowFullSharedSeed.node tag := by
  have shape:=tree_eq capacity nonzero tag
  change BorrowTree.new tag (Size.ofBytes capacity)=_ at shape
  have bounded:=GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes index value present
  rw [shape] at bounded
  have same : index=allocationRoot:=GeneralBorrowNodeUpdate.index_injective index allocationRoot (by change index.toNat=0;change index.toNat<1 at bounded;omega)
  subst index
  have nodeEq : value=GeneralBorrowFullSharedSeed.node tag := by rw [shape] at present;exact (Option.some.inj present).symm
  exact ⟨rfl,nodeEq⟩

private theorem root_order (tag : BorTag) (capacity : UInt64) (nonzero : capacity≠0) :
    ParentTagOrder (BorrowTree.new tag (Size.ofBytes capacity)) := by
  intro child childNode childAt parent parentNode edge parentAt
  obtain ⟨rfl,rfl⟩:=root_cases tag capacity nonzero child childNode childAt
  cases edge

private theorem root_completion (tag : BorTag) (capacity : UInt64) (nonzero : capacity≠0)
    (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (BorrowTree.new tag (Size.ofBytes capacity)) global) :
    ∃ C,Completes (BorrowTree.new tag (Size.ofBytes capacity)) C := by
  apply S05CompletedRootOrigins.exists_completion _ runtime.formed.toGraphState (by change [allocationRoot].Nodup;simp) (root_order tag capacity nonzero)
  intro position root slot different
  have valid:=(Array.getElem?_eq_some_iff.mp slot).1
  change position<1 at valid
  exact False.elim (different (by omega))

private theorem seed_owned (tag : BorTag) (capacity offset len : UInt64) (nonzero : capacity≠0)
    (held : ProtectedTags) (completion : Completion) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority (BorrowTree.new tag (Size.ofBytes capacity)) completion held allocationRoot)
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


private theorem seed_any (tag : BorTag) (capacity lower upper : UInt64) (nonzero : capacity≠0)
    (held : ProtectedTags) (completion : Completion) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority (BorrowTree.new tag (Size.ofBytes capacity)) completion held allocationRoot)
      lower upper (BorrowTree.new tag (Size.ofBytes capacity)).locations := by
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



private theorem parents_of_complete (tree : BorrowTree) (C : Completion)
    (complete : Completes tree C) (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (order : ParentTagOrder tree) (roots : tree.roots=#[allocationRoot]) : ParentInterpretation tree C := by
  have primary : tree.roots[0]?=some allocationRoot:=by rw [roots];rfl
  have first:=complete.2.2.2.2.2.1 0 allocationRoot primary
  have primaryNone : C.parents[allocationRoot.toNat]?=some none:=by simpa using first
  refine ⟨runtime.formed.toGraphState,order,complete.1,?_,?_,primaryNone,?_⟩
  · intro index node present parent edge
    exact (complete.2.2.2.2.1 index node present).2.2.1 parent edge
  · intro child parent edge
    exact ⟨(complete.2.2.2.2.2.2 child parent edge).1,(complete.2.2.2.2.2.2 child parent edge).2.1⟩
  · intro position root slot origin edge
    have valid:=(Array.getElem?_eq_some_iff.mp slot).1
    rw [roots] at valid
    have zero : position=0:=by change position<1 at valid;omega
    subst position
    have same : root=allocationRoot:=Option.some.inj (slot.symm.trans primary)
    subst root
    rw [primaryNone] at edge
    cases edge


/-- An optional completion cannot put another node above its primary root. -/
theorem below_primary (C : Completion) (noneAt : C.parents[allocationRoot.toNat]?=some none)
    (index : UniIndex) (below : Below C index allocationRoot) : index=allocationRoot := by
  cases below with
  | refl => rfl
  | step edge _ => rw [noneAt] at edge; cases edge

private theorem zero_location (root tag : BorTag) (C : Completion) (flags : ProtectedTags)
    (noneAt : C.parents[allocationRoot.toNat]?=some none) (locations : DedupRangeMap LocationTree) :
    Authority (BorrowRangeAccess.canonicalChildTree root tag locations)
      C flags allocationRoot BorrowRangeAccess.rootLocation := by
  intro index node present
  have bounded:=GeneralBorrowNodeUpdate.lookup_valid _ index node present
  change index.toNat<2 at bounded
  have split : index=allocationRoot ∨ index=(⟨1⟩ : UniIndex) := by
    by_cases zero : index.toNat=0
    · exact Or.inl (GeneralBorrowNodeUpdate.index_injective index allocationRoot zero)
    · exact Or.inr (GeneralBorrowNodeUpdate.index_injective index ⟨1⟩ (by change index.toNat=1;omega))
  rcases split with rfl | rfl
  · have actual : node={tag:=root,parent:=none,children:=#[⟨1⟩],defaultInitialPermission:=.Disabled,defaultInitialSifa:=.None} :=
      (Option.some.inj present).symm
    subst node
    refine ⟨?_,fun outside=>False.elim (outside (.refl _))⟩
    intro _
    change LocalWrite ⟨.Unique,true,.None⟩ (flags.contains root)
    simp [LocalWrite,LocationState.possible,Permission.isUnique]
  · have actual : node={tag:=tag,parent:=some ⟨0⟩,children:=#[],defaultInitialPermission:=.ReservedFrz false,defaultInitialSifa:=.None} :=
      (Option.some.inj present).symm
    subst node
    constructor
    · intro below
      have impossible:=below_primary C noneAt ⟨1⟩ below
      have bad:=congrArg UniIndex.toNat impossible
      change 1=0 at bad
      omega
    · intro _
      change ForeignWrite ⟨.ReservedFrz false,false,.None⟩ (flags.contains tag)
      simp [ForeignWrite,LocationState.possible,Permission.isUnique]

/-- The actual concrete empty q constructor leaves root0 writable on every
Bool byte, even while q is protected. No source window or source authority is
needed; q is dormant ReservedFrz(false), rather than Disabled. -/
theorem concrete_zero_owned (root tag : BorTag) (size : Size) (C : Completion) (flags : ProtectedTags)
    (noneAt : C.parents[allocationRoot.toNat]?=some none) (lower upper : UInt64) :
    OwnedOn (Authority (TypedRetagConcreteEmpty.lazyTree root tag size.bytes) C flags allocationRoot)
      lower upper (TypedRetagConcreteEmpty.lazyTree root tag size.bytes).locations := by
  intro position valid positive start stop
  have one : position=0 := by
    dsimp only [TypedRetagConcreteEmpty.lazyTree,BorrowRangeAccess.canonicalChildTree,DedupRangeMap.new] at valid
    split at valid <;> simp_all only [Array.size_empty,Array.size_singleton] <;> omega
  subst position
  have nonzero : (size.bytes==0)=false := by
    dsimp only [TypedRetagConcreteEmpty.lazyTree,BorrowRangeAccess.canonicalChildTree,DedupRangeMap.new] at valid
    split at valid
    · simp only [Array.size_empty] at valid;omega
    · rename_i h;exact Bool.eq_false_iff.mpr (by simpa only [Size.ofBytes] using h)
  simpa [TypedRetagConcreteEmpty.lazyTree,DedupRangeMap.new,Size.ofBytes,nonzero]
    using zero_location root tag C flags noneAt (DedupRangeMap.new (Size.ofBytes size.bytes) BorrowRangeAccess.rootLocation)

private theorem wildcard_location (root tag : BorTag) (size : Size) (C : Completion) (flags : ProtectedTags)
    (noneAt : C.parents[allocationRoot.toNat]?=some none) :
    Authority (CurrentCallEmptyMaterializedWildcard.finalTree root tag size)
      C flags allocationRoot BorrowRangeAccess.rootLocation := by
  intro index node present
  have bounded:=GeneralBorrowNodeUpdate.lookup_valid _ index node present
  change index.toNat<2 at bounded
  have split : index=allocationRoot ∨ index=(⟨1⟩ : UniIndex) := by
    by_cases zero : index.toNat=0
    · exact Or.inl (GeneralBorrowNodeUpdate.index_injective index allocationRoot zero)
    · exact Or.inr (GeneralBorrowNodeUpdate.index_injective index ⟨1⟩ (by change index.toNat=1;omega))
  rcases split with rfl | rfl
  · have actual : node={tag:=root,parent:=none,children:=#[],defaultInitialPermission:=.Disabled,defaultInitialSifa:=.None} :=
      (Option.some.inj present).symm
    subst node
    refine ⟨?_,fun outside=>False.elim (outside (.refl _))⟩
    intro _
    change LocalWrite ⟨.Unique,true,.None⟩ (flags.contains root)
    simp [LocalWrite,LocationState.possible,Permission.isUnique]
  · have actual : node=WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None :=
      (Option.some.inj present).symm
    subst node
    constructor
    · intro below
      have impossible:=below_primary C noneAt ⟨1⟩ below
      have bad:=congrArg UniIndex.toNat impossible
      change 1=0 at bad
      omega
    · intro _
      change ForeignWrite ⟨.ReservedFrz false,false,.None⟩ (flags.contains tag)
      simp [ForeignWrite,LocationState.possible,Permission.isUnique]

/-- The wildcard zero constructor creates a genuine second root. Its dormant
reservation also preserves the first root's Bool bytes, with no source bounds. -/
theorem wildcard_zero_owned (root tag : BorTag) (size : Size) (C : Completion) (flags : ProtectedTags)
    (noneAt : C.parents[allocationRoot.toNat]?=some none) (lower upper : UInt64) :
    OwnedOn (Authority (CurrentCallEmptyMaterializedWildcard.finalTree root tag size) C flags allocationRoot)
      lower upper (CurrentCallEmptyMaterializedWildcard.finalTree root tag size).locations := by
  intro position valid positive start stop
  change position<(DedupRangeMap.new size BorrowRangeAccess.rootLocation).entries.size at valid
  have one : position=0 := by
    dsimp only [DedupRangeMap.new] at valid
    split at valid <;> simp_all only [Array.size_empty,Array.size_singleton] <;> omega
  subst position
  have nonzero : (size.bytes==0)=false := by
    dsimp only [DedupRangeMap.new] at valid
    split at valid
    · simp only [Array.size_empty] at valid;omega
    · rename_i h;exact Bool.eq_false_iff.mpr h
  change Authority (CurrentCallEmptyMaterializedWildcard.finalTree root tag size) C flags allocationRoot
    (DedupRangeMap.new size BorrowRangeAccess.rootLocation).entries[0].data
  simpa [DedupRangeMap.new,nonzero] using wildcard_location root tag size C flags noneAt


/-- The positive concrete q tree preserves the original-root Bool bank solely
on its disjoint bytes. The root seed is derived here, not supplied as a live
pre-conversion Bool or a post-constructor authority premise. -/
theorem positive_owned (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (capacity offset len lower upper : UInt64) (room : global.nextPointerTag.value<18446744073709551615)
    (positive : 0<len.toNat) (bounds : offset.toNat+len.toNat≤capacity.toNat)
    (rootBelow : root.value.toNat<global.nextPointerTag.value.toNat)
    (protectors : ∀row∈global.protectedTags.entries,row.1.value.toNat<global.nextPointerTag.value.toNat)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→
      point.toNat<offset.toNat∨(offset+len).toNat≤point.toNat) :
    let G:=(GeneralBorrowFnEntryRegistration.registered global frame id room).1
    let tree:=PositiveGlobalTypedReborrow.finalTree root global.nextPointerTag (Size.ofBytes capacity) G.protectedTags offset len
    ∃C,ParentInterpretation tree C ∧OwnedOn (Authority tree C G.protectedTags allocationRoot) lower upper tree.locations := by
  have nonzeroCapacity : capacity≠0 := by intro zero;rw [zero] at bounds;simp only [UInt64.toNat_zero] at bounds;omega
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;contradiction
  let tree:=BorrowTree.new root (Size.ofBytes capacity)
  have runtime:=PositiveGlobalFnEntryInput.new_runtime root capacity nonzeroCapacity global rootBelow protectors
  obtain ⟨C,complete⟩:=root_completion root capacity nonzeroCapacity global runtime
  have order:=root_order root capacity nonzeroCapacity
  have rootAt : tree.nodes.get allocationRoot=some (GeneralBorrowFullSharedSeed.node root):=BorrowTree.new_root_node _ _
  have bound : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat := by
    have shape:=GeneralBorrowFullSharedSeed.tree_eq capacity nonzeroCapacity root
    change tree=_ at shape
    rw [shape]
    exact bounds
  have path : Path tree allocationRoot allocationRoot:=.refl _ _ rootAt
  have short : tree.nodes.size<65536 := by change (1 : Nat)<65536;decide
  have oldOwned:=seed_owned root capacity offset len nonzeroCapacity global.protectedTags C
  obtain ⟨readDone,readRuntime,readComplete,_,readNodes,readRoots,readTags,readCapacity⟩:=
    S05ConcreteFnEntryRaw.prepare_read tree global frame id C runtime complete order 0 allocationRoot allocationRoot
      (GeneralBorrowFullSharedSeed.node root) (GeneralBorrowFullSharedSeed.node root) rfl rootAt rootAt path room offset len bound oldOwned short .VisitChildrenOfAccessed
  let G:=(GeneralBorrowFnEntryRegistration.registered global frame id room).1
  let accessed:=tree.performBorrowAccessRange (.concrete root) (Size.ofBytes offset) (Size.ofBytes len) .Read G.protectedTags .VisitChildrenOfAccessed
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree G at readRuntime
  change Completes accessed.tree C at readComplete
  change accessed.tree.nodes=tree.nodes at readNodes
  change accessed.tree.roots=tree.roots at readRoots
  change accessed.tree.tagMapping=tree.tagMapping at readTags
  change accessed.tree.locations.size=tree.locations.size at readCapacity
  have readOrder : ParentTagOrder accessed.tree := by
    intro child childNode childAt parent parentNode edge parentAt
    rw [readNodes] at childAt parentAt
    exact order child childNode childAt parent parentNode edge parentAt
  have roots : accessed.tree.roots=#[allocationRoot] := readRoots
  have parents:=parents_of_complete accessed.tree C readComplete G readRuntime readOrder roots
  have seed:=seed_any root capacity lower upper nonzeroCapacity G.protectedTags C
  have retained:=GeneralBorrowRangeOutsideOwned.owned (Authority tree C G.protectedTags allocationRoot)
    tree (.concrete root) (Size.ofBytes offset) (Size.ofBytes len) .Read G.protectedTags .VisitChildrenOfAccessed runtime.formed.well bound lower upper apart seed
  have readOwned : OwnedOn (Authority accessed.tree C G.protectedTags allocationRoot) lower upper accessed.tree.locations := by
    intro position valid pos start stop index node present
    rw [readNodes] at present
    exact retained position valid pos start stop index node present
  have atRoot : accessed.tree.nodeAt allocationRoot=some (GeneralBorrowFullSharedSeed.node root) := by
    change accessed.tree.nodes.get _=_;rw [readNodes];exact rootAt
  have tagged:=readRuntime.formed.allocator.nodeTags _ _ atRoot
  obtain ⟨_,held,_,_,_,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame id room runtime
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [readTags];exact fresh
  have tagBound : global.nextPointerTag.value.toNat<G.nextPointerTag.value.toNat := by
    have next:=GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have afterRoom : accessed.tree.nodes.size+1≤4294967295 := by rw [readNodes];change (2 : Nat)≤4294967295;decide
  have afterBounds : offset.toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bound
  have isHeld : G.protectedTags.contains global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨_,_,_,_,child,lookup,leaf,nextParents,nextOwned,_⟩:=CurrentCallCheckpointMutableBoolFrame.strong_constructor
    accessed.tree G C readRuntime parents root global.nextPointerTag allocationRoot allocationRoot
    (GeneralBorrowFullSharedSeed.node root) (GeneralBorrowFullSharedSeed.node root) tagged atRoot atRoot afterFresh afterRoom tagBound isHeld
    offset len lower upper nonzero afterBounds apart ⟨_,atRoot⟩ (by change root.value≤global.nextPointerTag.value;exact Nat.le_of_lt rootBelow) readOwned
  exact ⟨_,nextParents,nextOwned⟩


/-- Technical root-grant indices preserve the original return-family value. -/
def identities (family : Family) (C : Completion) : Identities :=
  ⟨⟨#[(family.allocation,⟨C,#[]⟩)],#[family.at allocationRoot],#[⟨0,none,0⟩],fun _ _=>none⟩,
    #[⟨0,family.value⟩],#[]⟩

/-- Install the DERIVED root Bool bank in the actual materialized q allocation.
The physical window is the original destination, independent of q's pointer.
Presence and the selected root cache are current-world facts, not an ensure
replay or a fabricated initial live Bool window. -/
theorem window {before place} (tracker : MachineHooks.BorrowState)
    (family : Family) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (id : physical.id=family.allocation) (_pointer : physical.pointer=family.value)
    (root : BorTag) (concrete : family.value.provenance=.concrete family.allocation root)
    (C : Completion) (parents : ParentInterpretation physical.entry.allocation.extra C)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra tracker.global)
    (extent : physical.entry.allocation.len=physical.entry.allocation.byteSize.bytes.toNat)
    (capacity : physical.entry.allocation.extra.locations.size=physical.entry.allocation.byteSize)
    (rootSlot : physical.entry.allocation.extra.roots[0]?=some allocationRoot)
    (rootNode : TreeNode) (rootAt : physical.entry.allocation.extra.nodes.get allocationRoot=some rootNode)
    (rootTag : rootNode.tag=root) (rootNone : rootNode.parent=none)
    (rootDefault : rootNode.defaultInitialPermission=.Disabled)
    (cachedRoot : tracker.global.rootTag? family.allocation=some root)
    (owned : OwnedOn (Authority physical.entry.allocation.extra C tracker.global.protectedTags allocationRoot)
      physical.offset (physical.offset+1) physical.entry.allocation.extra.locations) :
    ∃B : UniformWindow before tracker (identities family C) 0 family.allocation physical.offset.toNat 1 .ret,
      B.pointer=family.at allocationRoot ∧B.allocation=physical.entry.allocation ∧B.precise.completion=C := by
  have present : Present (ActualWorld before) family.allocation physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    refine List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live),?_⟩
    simp only [id]
  have cap : AllocationCapability before tracker family.allocation physical.entry.allocation :=
    ⟨present,extent,capacity,rootSlot,rootNode,rootAt,rootNone,rootDefault,by rw [rootTag];exact cachedRoot⟩
  have bind : PointerBinds physical.entry.allocation (family.at allocationRoot) := by
    refine ⟨rootNode,rootAt,runtime.formed.allocator.nodeTags _ _ rootAt,?_⟩
    simp only [Family.at,concrete]
    exact ⟨trivial,rootTag.symm⟩
  have fits : physical.offset.toNat+1<2^64 := by
    have bound:=physical.bounds
    exact Nat.lt_of_le_of_lt bound physical.capacity.toNat_lt
  have endEq : (physical.offset+1).toNat=physical.offset.toNat+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
  let B : UniformWindow before tracker (identities family C) 0 family.allocation physical.offset.toNat 1 .ret := {
    loan:=⟨0,none,0⟩,pointer:=family.at allocationRoot,allocation:=physical.entry.allocation,precise:=⟨C,#[]⟩,
    loanAt:=rfl,pointerAt:=rfl,pointerId:=rfl,present:=present,preciseAt:=by simp [identities],
    binding:=bind,issued:=.allocated cap,parents:=parents,window:=by
      intro byte inside
      refine ⟨?_,?_⟩
      · have bound:=physical.bounds
        have size:=physical.bytes
        have lower:=inside.2.1
        have upper:=inside.2.2
        omega
      · intro segment member lower upper index node found
        obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
        subst segment
        have rights:=owned position valid (by omega) (by have h:=inside.2;omega) (by have h:=inside.2;omega) index node found
        have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node found)
          ((runtime.formed.profile position valid).present index node found)
        exact ⟨fun below=>(materialized_bool_rule "CurrentCallResourceCopyInstall.local_token") _ _ realized (rights.1 below),
          fun clash=>Classical.byContradiction (fun outside=>(materialized_bool_rule "CurrentCallResourceCopyInstall.foreign_no_clash") _ _ realized (rights.2 outside) clash)⟩}
  exact ⟨B,rfl,rfl,rfl⟩


/-- Bool-role storage facts about the SAME converted payload. Initialization
mask validity is required, but no initialized Bool value is required. These
facts do not constrain the zero source's footprint or mutability. -/
structure PhysicalData (family : Family) (root : BorTag) (converted : Allocation Provenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance) : Prop where
  extent : converted.len=converted.byteSize.bytes.toNat
  mutable : converted.mutability=.Mut
  maskValid : InitMaskCopy.WellFormed converted.initializationMask
  maskLength : converted.initializationMask.len=converted.byteSize
  provenance : ProvenanceCopy.WellFormed converted.provenanceMap converted.len
  bounds : offset.toNat+1≤converted.byteSize.bytes.toNat
  addressRoom : base.toNat+converted.len<2^64
  nonnull : base+offset≠0
  value : family.value=Pointer.new (.concrete family.allocation root) (Size.ofBytes (base+offset))
  physicalPointer : place.mplace.ptr=family.value.withOptionalProvenance
  layout : place.layout=RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned=none

/-- Recover the original physical Bool destination and its binding from the
actual post-source heap/cache/registry. q's temporary pointer is never used as
the return place, and ensure is not invoked a second time. -/
theorem physical (post : Before) (family : Family) (root : BorTag)
    (converted : Allocation Provenance Unit) (base offset : UInt64) (place : MPlaceTy Provenance)
    (facts : PhysicalData family root converted base offset place) (tree : BorrowTree)
    (kind : MemoryKind MiriMemoryKind)
    (live : post.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨kind,converted.mapExtra (fun _=>tree)⟩))
    (cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩)
    (extra : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨none,#[]⟩)) :
    ∃P : CandidateCurrentBoolUninitWrite.PhysicalWindow post place,
      P.id=family.allocation ∧P.pointer=family.value ∧P.offset=offset ∧P.entry.allocation=converted.mapExtra (fun _=>tree) ∧
      CandidateCallBindings.WindowBinding post P.pointer P.id offset.toNat 1 ∧
      CurrentCallBoolProtection.WindowReady post P.id offset.toNat 1 := by
  let allocation:=converted.mapExtra (fun _=>tree)
  let P : CandidateCurrentBoolUninitWrite.PhysicalWindow post place := {
    pointer:=family.value,physicalPointer:=facts.physicalPointer,layout:=facts.layout,aligned:=facts.aligned,
    id:=family.allocation,entry:=⟨kind,allocation⟩,base:=base,offset:=offset,capacity:=converted.byteSize.bytes,
    live:=live,cachedBase:=cached,pointerAddress:=by rw [facts.value];rfl,
    bounds:=facts.bounds,size:=rfl,bytes:=facts.extent,mutable:=facts.mutable,
    maskValid:=facts.maskValid,maskLength:=facts.maskLength,provenanceMap:=facts.provenance}
  have sumFits : base.toNat+offset.toNat<2^64 := by
    have bound:=facts.bounds
    have extent:=facts.extent
    have room:=facts.addressRoom
    omega
  have binding : CandidateCallBindings.WindowBinding post family.value family.allocation offset.toNat 1 := by
    refine ⟨⟨kind,allocation⟩,base,live,cached,facts.extent,facts.addressRoom,?_,?_,?_,?_⟩
    · change offset.toNat+1≤converted.len
      rw [facts.extent]
      exact facts.bounds
    · rw [facts.value]
      change (base+offset).toNat=base.toNat+offset.toNat
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]
    · rw [facts.value]
      exact facts.nonnull
    · rw [facts.value]
      rfl
  exact ⟨P,rfl,rfl,rfl,rfl,binding,⟨#[],extra,by simp⟩⟩


/-- The one post-source packet consumed by the existing LIVE Bool backend. -/
structure Packet (post : Before) (tracker : MachineHooks.BorrowState) (family : Family)
    (converted : Allocation Provenance Unit) (tree : BorrowTree) (offset : UInt64) (place : MPlaceTy Provenance) where
  completion : Completion
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow post place
  physicalId : physical.id=family.allocation
  physicalPointer : physical.pointer=family.value
  physicalOffset : physical.offset=offset
  physicalAllocation : physical.entry.allocation=converted.mapExtra (fun _=>tree)
  window : UniformWindow post tracker (identities family completion) 0 family.allocation offset.toNat 1 .ret
  pointer : window.pointer=family.at allocationRoot
  allocation : window.allocation=converted.mapExtra (fun _=>tree)
  precise : window.precise.completion=completion
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global
  distinct : tree.roots.toList.Nodup
  short : tree.nodes.size<65536
  binding : CandidateCallBindings.WindowBinding post physical.pointer physical.id offset.toNat 1
  ready : CurrentCallBoolProtection.WindowReady post physical.id offset.toNat 1

private theorem install (post : Before) (tracker : MachineHooks.BorrowState) (family : Family) (root : BorTag)
    (converted : Allocation Provenance Unit) (base offset : UInt64) (place : MPlaceTy Provenance)
    (facts : PhysicalData family root converted base offset place) (tree : BorrowTree) (kind : MemoryKind MiriMemoryKind)
    (live : post.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨kind,converted.mapExtra (fun _=>tree)⟩))
    (cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩)
    (extra : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨none,#[]⟩))
    (C : Completion) (parents : ParentInterpretation tree C)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size<65536)
    (capacity : tree.locations.size=converted.byteSize)
    (rootSlot : tree.roots[0]?=some allocationRoot)
    (rootNode : TreeNode) (rootAt : tree.nodes.get allocationRoot=some rootNode)
    (rootTag : rootNode.tag=root) (rootNone : rootNode.parent=none) (rootDefault : rootNode.defaultInitialPermission=.Disabled)
    (cachedRoot : tracker.global.rootTag? family.allocation=some root)
    (owned : OwnedOn (Authority tree C tracker.global.protectedTags allocationRoot) offset (offset+1) tree.locations) :
    Nonempty (Packet post tracker family converted tree offset place) := by
  obtain ⟨P,pId,pPointer,pOffset,pAllocation,binding,ready⟩:=physical post family root converted base offset place facts tree kind live cached extra
  have parentsP : ParentInterpretation P.entry.allocation.extra C := by rw [pAllocation];exact parents
  have runtimeP : DuplicatePrefixBorrowContract.RuntimeFacts P.entry.allocation.extra tracker.global := by rw [pAllocation];exact runtime
  have extentP : P.entry.allocation.len=P.entry.allocation.byteSize.bytes.toNat := by rw [pAllocation];exact facts.extent
  have capacityP : P.entry.allocation.extra.locations.size=P.entry.allocation.byteSize := by rw [pAllocation];exact capacity
  have rootSlotP : P.entry.allocation.extra.roots[0]?=some allocationRoot := by rw [pAllocation];exact rootSlot
  have rootAtP : P.entry.allocation.extra.nodes.get allocationRoot=some rootNode := by rw [pAllocation];exact rootAt
  have ownedP : OwnedOn (Authority P.entry.allocation.extra C tracker.global.protectedTags allocationRoot)
      P.offset (P.offset+1) P.entry.allocation.extra.locations := by rw [pAllocation,pOffset];exact owned
  have choice:=window tracker family P pId pPointer root (by rw [facts.value];rfl) C parentsP runtimeP extentP capacityP
    rootSlotP rootNode rootAtP rootTag rootNone rootDefault cachedRoot ownedP
  rw [pOffset] at choice
  obtain ⟨B,pointer,allocation,precise⟩:=choice
  exact ⟨⟨C,P,pId,pPointer,pOffset,pAllocation,B,pointer,allocation.trans pAllocation,precise,runtime,distinct,short,binding,ready⟩⟩


/-- Positive SAME-ID endpoint. The source operation supplies its actual
current tree/runtime/root metadata; Bool authority is derived from the fresh
root and byte disjointness, then installed in that SAME post-source world. -/
theorem positive (post : Before) (next : MachineHooks.BorrowState) (family : Family) (root : BorTag)
    (converted : Allocation Provenance Unit) (base boolOffset : UInt64) (place : MPlaceTy Provenance)
    (facts : PhysicalData family root converted base boolOffset place)
    (global : GlobalState) (frame : FrameState) (sourceOffset len : UInt64)
    (room : global.nextPointerTag.value<18446744073709551615)
    (nonzero : 0<len.toNat) (bounds : sourceOffset.toNat+len.toNat≤converted.byteSize.bytes.toNat)
    (rootBelow : root.value.toNat<global.nextPointerTag.value.toNat)
    (protectors : ∀row∈global.protectedTags.entries,row.1.value.toNat<global.nextPointerTag.value.toNat)
    (apart : ∀point : UInt64,boolOffset.toNat≤point.toNat→point.toNat<(boolOffset+1).toNat→
      point.toNat<sourceOffset.toNat∨(sourceOffset+len).toNat≤point.toNat)
    (flags : next.global.protectedTags=(GeneralBorrowFnEntryRegistration.registered global frame family.allocation room).1.protectedTags)
    (kind : MemoryKind MiriMemoryKind)
    (cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩)
    (extra : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨none,#[]⟩))
    (cachedRoot : next.global.rootTag? family.allocation=some root) :
    let tree:=PositiveGlobalTypedReborrow.finalTree root global.nextPointerTag converted.byteSize
      (GeneralBorrowFnEntryRegistration.registered global frame family.allocation room).1.protectedTags sourceOffset len
    post.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨kind,converted.mapExtra (fun _=>tree)⟩)→
    DuplicatePrefixBorrowContract.RuntimeFacts tree next.global→
    tree.roots.toList.Nodup→tree.nodes.size≤2→
    tree.locations.size=converted.byteSize→tree.roots[0]?=some allocationRoot→
    (∃node,tree.nodes.get allocationRoot=some node ∧node.tag=root ∧node.parent=none ∧node.defaultInitialPermission=.Disabled)→
    Nonempty (Packet post next family converted tree boolOffset place) := by
  intro tree live runtime distinct growth capacity rootSlot rootMetadata
  obtain ⟨C,parents,owned⟩:=positive_owned global frame family.allocation root converted.byteSize.bytes sourceOffset len boolOffset (boolOffset+1)
    room nonzero bounds rootBelow protectors apart
  change ParentInterpretation tree C at parents
  change OwnedOn (Authority tree C (GeneralBorrowFnEntryRegistration.registered global frame family.allocation room).1.protectedTags allocationRoot)
    boolOffset (boolOffset+1) tree.locations at owned
  have currentOwned : OwnedOn (Authority tree C next.global.protectedTags allocationRoot) boolOffset (boolOffset+1) tree.locations := by
    rw [flags]
    exact owned
  obtain ⟨node,atRoot,tag,parent,disabled⟩:=rootMetadata
  exact install post next family root converted base boolOffset place facts tree kind live cached extra C parents runtime distinct (by omega) capacity rootSlot
    node atRoot tag parent disabled cachedRoot currentOwned


private theorem new_capacity (size : Size) (location : LocationTree) : (DedupRangeMap.new size location).size=size := by
  cases size with
  | mk bytes=>
    by_cases zero : bytes=0
    · subst bytes;rfl
    · simp [DedupRangeMap.new,DedupRangeMap.size,Size.ofBytes,zero]

/-- Concrete zero-source SAME-ID endpoint, with arbitrary source offset. All
source runtime and optional-parent facts are derived from the actual literal
constructor and allocator facts; Bool storage comes solely from its own role. -/
theorem concrete_zero (post : Before) (next : MachineHooks.BorrowState) (family : Family) (root tag : BorTag)
    (converted : Allocation Provenance Unit) (base boolOffset sourceOffset : UInt64) (place : MPlaceTy Provenance)
    (facts : PhysicalData family root converted base boolOffset place)
    (older : root.value<tag.value) (rootBelow : root.value.toNat<next.global.nextPointerTag.value.toNat)
    (protectors : ∀row∈next.global.protectedTags.entries,row.1.value.toNat<next.global.nextPointerTag.value.toNat)
    (tagBelow : tag.value.toNat<next.global.nextPointerTag.value.toNat) (held : next.global.protectedTags.contains tag=true)
    (kind : MemoryKind MiriMemoryKind)
    (live : post.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,
      ⟨kind,converted.mapExtra (fun _=>TypedRetagConcreteEmpty.lazyTree root tag converted.byteSize.bytes)⟩))
    (cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩)
    (extra : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨none,#[]⟩))
    (cachedRoot : next.global.rootTag? family.allocation=some root) :
    Nonempty (Packet post next family converted (TypedRetagConcreteEmpty.lazyTree root tag converted.byteSize.bytes) boolOffset place) := by
  have distinct : root≠tag := by intro same;rw [same] at older;exact Nat.lt_irrefl _ older
  have runtime:=CurrentCallEmptyMaterializedSourceFacts.concrete_runtime root tag converted.byteSize next.global rootBelow protectors distinct tagBelow held sourceOffset
  obtain ⟨C,parents⟩:=CurrentCallMaterializedZeroParents.concrete root tag converted.byteSize next.global runtime older
  have owned:=concrete_zero_owned root tag converted.byteSize C next.global.protectedTags parents.primaryNone boolOffset (boolOffset+1)
  have capacity : (TypedRetagConcreteEmpty.lazyTree root tag converted.byteSize.bytes).locations.size=converted.byteSize := by
    exact new_capacity converted.byteSize BorrowRangeAccess.rootLocation
  exact install post next family root converted base boolOffset place facts _ kind live cached extra C parents runtime (by change ([allocationRoot] : List UniIndex).Nodup;simp) (by change (2 : Nat)<65536;decide) capacity rfl
    _ rfl rfl rfl rfl cachedRoot owned

/-- Wildcard zero-source SAME-ID endpoint. q remains a genuine parentless
second root, and its source offset need not lie within the allocation. -/
theorem wildcard_zero (post : Before) (next : MachineHooks.BorrowState) (family : Family) (root tag : BorTag)
    (converted : Allocation Provenance Unit) (base boolOffset sourceOffset : UInt64) (place : MPlaceTy Provenance)
    (facts : PhysicalData family root converted base boolOffset place)
    (older : root.value<tag.value) (rootBelow : root.value.toNat<next.global.nextPointerTag.value.toNat)
    (protectors : ∀row∈next.global.protectedTags.entries,row.1.value.toNat<next.global.nextPointerTag.value.toNat)
    (tagBelow : tag.value.toNat<next.global.nextPointerTag.value.toNat) (held : next.global.protectedTags.contains tag=true)
    (kind : MemoryKind MiriMemoryKind)
    (live : post.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,
      ⟨kind,converted.mapExtra (fun _=>CurrentCallEmptyMaterializedWildcard.finalTree root tag converted.byteSize)⟩))
    (cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩)
    (extra : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨none,#[]⟩))
    (cachedRoot : next.global.rootTag? family.allocation=some root) :
    Nonempty (Packet post next family converted (CurrentCallEmptyMaterializedWildcard.finalTree root tag converted.byteSize) boolOffset place) := by
  have distinct : root≠tag := by intro same;rw [same] at older;exact Nat.lt_irrefl _ older
  have runtime:=CurrentCallEmptyMaterializedSourceFacts.wildcard_runtime root tag converted.byteSize next.global rootBelow protectors distinct tagBelow held sourceOffset
  obtain ⟨C,parents⟩:=CurrentCallMaterializedZeroParents.wildcard root tag converted.byteSize next.global runtime older
  have owned:=wildcard_zero_owned root tag converted.byteSize C next.global.protectedTags parents.primaryNone boolOffset (boolOffset+1)
  have capacity : (CurrentCallEmptyMaterializedWildcard.finalTree root tag converted.byteSize).locations.size=converted.byteSize :=
    new_capacity converted.byteSize BorrowRangeAccess.rootLocation
  exact install post next family root converted base boolOffset place facts _ kind live cached extra C parents runtime (by change ([allocationRoot,⟨1⟩] : List UniIndex).Nodup;decide) (by change (2 : Nat)<65536;decide) capacity rfl
    _ rfl rfl rfl rfl cachedRoot owned

end
end DuplicatePrefix.CurrentCallMaterializedRootBoolFrame

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallMaterializedRootBoolFrame.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved materialized root Bool dependency {name}: {dependency}"
