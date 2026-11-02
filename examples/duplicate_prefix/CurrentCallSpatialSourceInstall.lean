import duplicate_prefix.CurrentCallSpatialTypedSourceCopy
import duplicate_prefix.CurrentCallBorrowIssuance
import duplicate_prefix.CurrentCallSpatialSourceCover

/-! Source-only spatial resources on the actual installed allocation. No
initial world is reused as the world of the changed borrow tree. -/
namespace DuplicatePrefix.CurrentCallSpatialSourceInstall
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath S05ConcreteProtectedChildCompletion
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallTypedSourceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section

/-- Issuance needs the actual installed world and actual constructor metadata,
not ownership of the full operation window under one parent interpretation. -/
private theorem issue {before tracker id allocation C grant}
    (old : SpatialDelegation before tracker id allocation C grant)
    (model : ParentInterpretation allocation.extra C)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global)
    (value : Provenance) (post : Before) (next : MachineHooks.BorrowState)
    (afterTree : BorrowTree) (child : UniIndex) (node : TreeNode)
    (present : Present (ActualWorld post) id (allocation.setExtra afterTree))
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id)
    (capacity : afterTree.locations.size=allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),allocation.extra.roots[position]?=some root→afterTree.roots[position]?=some root)
    (metadata : ∀ index oldNode,allocation.extra.nodes.get index=some oldNode→
      ∃changed,afterTree.nodes.get index=some changed ∧changed.tag=oldNode.tag ∧changed.parent=oldNode.parent ∧changed.isExposed=oldNode.isExposed ∧changed.defaultInitialPermission=oldNode.defaultInitialPermission)
    (nodeAt : afterTree.nodes.get child=some node) (tag : node.tag=tracker.global.nextPointerTag)
    (constructor : match value with | .concrete _ _=>node.parent=some grant | .wildcard=>node.parent=none)
    (parents : ParentInterpretation afterTree (extend C child grant)) :
    SpatialDelegation post next id (allocation.setExtra afterTree) (extend C child grant) child := by
  have vacant : allocation.extra.nodes.get child=none := by
    cases oldAt : allocation.extra.nodes.get child with
    | none=>rfl
    | some previous=>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := metadata child previous oldAt
      have same : changed=node := Option.some.inj (changedAt.symm.trans nodeAt)
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh allocation.extra tracker.global runtime child previous oldAt
      rw [←changedTag,same,tag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have parentIssued := CurrentCallResourceInstallation.spatial old model post next afterTree present rootTag capacity roots metadata child grant vacant
  cases value with
  | concrete id tag=>
    obtain ⟨parent,parentAt⟩ := (parents.edgeLive child grant (child_edge C child grant)).2
    exact SpatialDelegation.concrete parentIssued (.step (.refl grant parent parentAt) node nodeAt constructor)
  | wildcard=>
    obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path afterTree parents.graph child node nodeAt
    have sameRoot : root=child := by
      cases path with
      | refl=>rfl
      | @step predecessor target earlier found foundAt edge=>
        have same : found=node := Option.some.inj (foundAt.symm.trans nodeAt)
        rw [same,constructor] at edge
        cases edge
    subst root
    obtain ⟨earlier,originRoot,newRoot,originNode,before,originSlot,newRootAt,originAt,exposed,older,originPath⟩ :=
      parents.virtual position child rootSlot grant (child_edge C child grant)
    have same : newRoot=node := Option.some.inj (newRootAt.symm.trans nodeAt)
    exact .wildcard originNode newRoot earlier position originRoot parentIssued originAt exposed newRootAt
      (by rw [same];exact constructor) older before originSlot rootSlot originPath (child_edge C child grant)

private theorem shape {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (i : Fin role.backing.cells.size)
    (overlap : ∃byte,Window role.backing.id offset length byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (child : UniIndex) (node : TreeNode)
    (lookup : (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.indexOfTag tracker.global.nextPointerTag=some child)
    (nodeAt : (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.nodes.get child=some node) :
    match role.family.value.provenance with
    | .concrete _ _=>node.parent=some (role.roles i overlap).grant
    | .wildcard=>node.parent=none := by
  obtain ⟨contract,afterRuntime,_⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  obtain ⟨_,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global frame role.backing.id room runtime
  obtain ⟨parent,parentAt,_,binding⟩ := (role.roles i overlap).binding
  have afterAt : (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.get (role.roles i overlap).grant=some parent := by rw [contract.nodes];exact parentAt
  have freshAfter : GeneralBorrowTagMap.Fresh (CurrentCallSpatialEntryRead.read role frame room start amount).tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have afterRoom : (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.size+1≤4294967295 := by change (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.data.size+1≤_;rw [contract.nodes];exact nodeRoom
  have afterBounds : start.toNat+amount.toNat≤(CurrentCallSpatialEntryRead.read role frame room start amount).tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<(CurrentCallSpatialEntryRead.registeredTracker role frame room).global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : (CurrentCallSpatialEntryRead.registeredTracker role frame room).global.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    change ((GeneralBorrowFnEntryRegistration.registered tracker.global frame role.backing.id room).1.protectedTags.get tracker.global.nextPointerTag).isSome=true
    rw [held]
    rfl
  cases value : role.family.value.provenance with
  | concrete id tag=>
    change (match role.family.value.provenance with | .concrete id tag=>id=role.family.allocation ∧tag=parent.tag | .wildcard=>parent.isExposed=true) at binding
    rw [value] at binding
    have tagged := afterRuntime.formed.allocator.nodeTags _ _ afterAt
    obtain ⟨_,_,_,_,q,qLookup,leaf,_⟩ := CurrentCallParentInsertion.concrete_frame _ _ afterRuntime parent.tag tracker.global.nextPointerTag (role.roles i overlap).grant parent tagged afterAt freshAfter afterRoom tagBound tagHeld start amount nonzero afterBounds
    have qLookup' : (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.indexOfTag tracker.global.nextPointerTag=some q := by
      simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialRows.provenance,value,binding.2] using qLookup
    have same : q=child := Option.some.inj (qLookup'.symm.trans lookup)
    subst q
    obtain ⟨actual,actualAt,parentEq⟩ := leaf.childLive
    have actualAt' : (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.nodes.get child=some actual := by
      simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialRows.provenance,value,binding.2] using actualAt
    have equal : node=actual := Option.some.inj (nodeAt.symm.trans actualAt')
    exact equal ▸ parentEq
  | wildcard=>
    obtain ⟨_,_,_,_,q,qLookup,_,rootFrame,_⟩ := CurrentCallParentInsertion.wildcard_frame _ _ afterRuntime tracker.global.nextPointerTag freshAfter afterRoom tagBound tagHeld (role.roles i overlap).grant parent afterAt start amount nonzero afterBounds
    have qLookup' : (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.indexOfTag tracker.global.nextPointerTag=some q := by
      simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialRows.provenance,value] using qLookup
    have same : q=child := Option.some.inj (qLookup'.symm.trans lookup)
    subst q
    obtain ⟨actual,actualAt,_,parentEq⟩ := rootFrame.childLive
    have actualAt' : (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.nodes.get child=some actual := by
      simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialRows.provenance,value] using actualAt
    have equal : node=actual := Option.some.inj (nodeAt.symm.trans actualAt')
    exact equal ▸ parentEq

open Lean Elab Tactic in
elab "spatial_install_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected one checked resource theorem for {suffix.getString}"

def childFamily {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (tag : BorTag) : Family :=
  ⟨role.family.slot,role.backing.id,CurrentCallTypedFnEntry.changedPointer role.family.value role.backing.id tag⟩

/-- Derived source-only installation evidence, indexed by the unchanged old
cell positions. It is an output of the operation, not a caller admission. -/
def CellResources {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (post : Before) (next : MachineHooks.BorrowState)
    (tree : BorrowTree) (tag : BorTag) (child : UniIndex) : Prop :=
  ∀(i : Fin role.backing.cells.size)
    (overlap : ∃byte,Window role.backing.id offset length byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte),
    ParentInterpretation tree (extend role.backing.cells[i].completion child (role.roles i overlap).grant) ∧
    PointerBinds (role.backing.allocation.setExtra tree) ((childFamily role tag).at child) ∧
    SpatialDelegation post next role.backing.id (role.backing.allocation.setExtra tree)
      (extend role.backing.cells[i].completion child (role.roles i overlap).grant) child ∧
    ∀byte,Window role.backing.id offset length byte→Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte→
      byte.2<role.backing.allocation.len ∧Embeds (role.backing.allocation.setExtra tree) next.global.protectedTags
        (extend role.backing.cells[i].completion child (role.roles i overlap).grant) child byte.2 .exclusive

/-- Per-cell source resources are installed on the actual post allocation.
The current presence/cache projections are supplied by the actual typed-copy
result; no new tree is pretended to be present in the old world. -/
theorem resources {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (post : Before) (next : MachineHooks.BorrowState)
    (present : Present (ActualWorld post) role.backing.id
      (role.backing.allocation.setExtra (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree))
    (rootTag : next.global.rootTag? role.backing.id=tracker.global.rootTag? role.backing.id)
    (flags : next.global.protectedTags=(CurrentCallSpatialEntryRead.output role frame room start amount).global.protectedTags) :
    let output := CurrentCallSpatialEntryRead.output role frame room start amount
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      CellResources role post next output.child.tree output.tag child := by
  let output := CurrentCallSpatialEntryRead.output role frame room start amount
  obtain ⟨_,_,_,afterRuntime,capacity,_,child,lookup,roots,metadata,node,nodeAt,nodeTag⟩ :=
    CurrentCallSpatialEntryConstructor.invoke role exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  obtain ⟨other,otherLookup,cellOwned⟩ := CurrentCallSpatialEntryConstructor.cells role exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  have same : other=child := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  refine ⟨child,lookup,?_⟩
  intro i overlap
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt role.backing.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat=offset+length := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap,startEq,amountEq]
  have atByte : ∀byte,Window role.backing.id offset length byte→Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte→
      ParentInterpretation output.child.tree (extend role.backing.cells[i].completion child (role.roles i overlap).grant) ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree (extend role.backing.cells[i].completion child (role.roles i overlap).grant) output.global.protectedTags child)
        (UInt64.ofNat byte.2) (UInt64.ofNat (byte.2+1)) output.child.tree.locations := by
    intro byte request cell
    have fit : byte.2+1<2^64 := by have := request.2.2;omega
    have lowerEq : (UInt64.ofNat byte.2).toNat=byte.2 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : byte.2<2^64)]
    have upperEq : (UInt64.ofNat (byte.2+1)).toNat=byte.2+1 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fit]
    exact cellOwned i overlap _ _ (by rw [lowerEq];exact request.2.1) (by rw [upperEq];have := request.2.2;omega)
      (by rw [lowerEq];exact cell.2.1) (by rw [upperEq];have := cell.2.2;omega)
  have witness := overlap
  obtain ⟨byte,request,cell⟩ := witness
  have parents := (atByte byte request cell).1
  have constructor := shape role exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds i overlap child node lookup nodeAt
  have issued := issue (role.roles i overlap).issued role.backing.cells[i].parents runtime role.family.value.provenance post next output.child.tree child node present rootTag capacity roots metadata nodeAt nodeTag constructor parents
  refine ⟨parents,?_,issued,?_⟩
  · refine ⟨node,nodeAt,?_,?_⟩
    · simpa only [Allocation.setExtra,Allocation.mapExtra,childFamily,Family.at,BorrowTree.indexOfTag,nodeTag] using lookup
    · change role.backing.id=role.backing.id ∧output.tag=node.tag
      exact ⟨rfl,nodeTag.symm⟩
  · intro byte request cell
    refine ⟨((role.roles i overlap).available byte request cell).1,?_⟩
    have owned := (atByte byte request cell).2
    dsimp only [output] at owned
    intro segment member lower upper index actual actualAt
    simp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper actualAt ⊢
    obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have fit : byte.2+1<2^64 := by have := request.2.2;omega
    have lowerEq : (UInt64.ofNat byte.2).toNat=byte.2 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : byte.2<2^64)]
    have upperEq : (UInt64.ofNat (byte.2+1)).toNat=byte.2+1 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fit]
    have rights := owned position valid (by omega) (by rw [upperEq];omega) (by rw [lowerEq];omega) index actual actualAt
    have realized := CandidateCurrentGrantRuntime.realized _ _ (afterRuntime.possible position valid index actual actualAt)
      ((afterRuntime.formed.profile position valid).present index actual actualAt)
    rw [flags]
    constructor
    · intro below
      exact (spatial_install_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact (spatial_install_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash

/-- This is exactly the machine named by the scoped typed-copy equation. -/
def copiedMachine {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (frame : FrameState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) : Before :=
  let output := CurrentCallSpatialEntryRead.output role frame room start amount
  {CurrentCallTypedSourceCopy.validated before tracker room role.backing.id entry output.child.tree with
    borrowTracker:=some ⟨output.global,tracker.retagMode⟩}

theorem copied_present {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (frame : FrameState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocation : entry.allocation=role.backing.allocation) :
    Present (ActualWorld (copiedMachine role frame room start amount entry)) role.backing.id
      (role.backing.allocation.setExtra (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree) := by
  have live : (copiedMachine role frame room start amount entry).memory.live.find? (fun row=>row.1==role.backing.id)=
      some (role.backing.id,{entry with allocation:=entry.allocation.setExtra (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree}) :=
    MemoryCopyBridge.live_lookup_replaced before.memory role.backing.id _
  simp only [Present,ActualWorld,Array.toList_map]
  refine List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),?_⟩
  simp only [allocation]

/-- Actual scoped-copy installation discharges current presence and cache
transport internally. No future-state or operation-status premise is added. -/
theorem copied_resources {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (allocation : entry.allocation=role.backing.allocation) :
    let output := CurrentCallSpatialEntryRead.output role frame room start amount
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      CellResources role (copiedMachine role frame room start amount entry) ⟨output.global,tracker.retagMode⟩ output.child.tree output.tag child := by
  apply resources role exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
    (copiedMachine role frame room start amount entry) ⟨_,tracker.retagMode⟩ (copied_present role frame room start amount entry allocation)
  · rfl
  · rfl

/-- Restricting to intersecting original cells is affine source extraction.
Every retained cell keeps its old geometry and its deterministically extended
parent map. This does not claim preservation of an ambient or paired cover. -/
def updates {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (exclusive : demandOf mode=.exclusive)
    {post : Before} {next : MachineHooks.BorrowState} {tree : BorrowTree} {tag : BorTag} {child : UniIndex}
    (resources : CellResources role post next tree tag child)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    CurrentCallSpatialSourceCover.Update role post next (role.backing.allocation.setExtra tree) (childFamily role tag) child i overlap where
  cell := ⟨role.backing.cells[i].offset,role.backing.cells[i].length,extend role.backing.cells[i].completion child (role.roles i overlap).grant,(resources i overlap).1⟩
  offsetEq := rfl
  lengthEq := rfl
  binding := (resources i overlap).2.1
  issued := (resources i overlap).2.2.1
  available := by
    intro byte request cell
    simpa only [exclusive,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using (resources i overlap).2.2.2 byte request cell

def sourceCover {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (exclusive : demandOf mode=.exclusive)
    {post : Before} {next : MachineHooks.BorrowState} {tree : BorrowTree} {tag : BorTag} {child : UniIndex}
    (live : Present (ActualWorld post) role.backing.id (role.backing.allocation.setExtra tree))
    (resources : CellResources role post next tree tag child) :
    RoleCover post next (CurrentCallSpatialSourceCover.context role live (updates role exclusive resources)) mode offset length :=
  CurrentCallSpatialSourceCover.assemble role live (updates role exclusive resources) rfl

/-- The actual scoped copy immediately produces installed source-cell resources. -/
theorem typed (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (cover : CurrentCallSpatialCover.Context before)
    (offset : Nat) (len : UInt64) (role : RoleCover before tracker cover .mut offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (enabled : before.borrowTracker=some tracker)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before role.family.value role.backing.id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none) :
    let output := CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
    ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,entry.allocation=role.backing.allocation ∧
      ∃doneFrame : CompilerFrameContext.ActualFrame,
        MachineHooks.withRetagMode .FnEntry
          ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
            ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
            (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
          (Storage.withCurrent frames frame before) =
          .ok () (Storage.withCurrent frames doneFrame (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) ∧
        ∃child,output.child.tree.indexOfTag output.tag=some child ∧
          CellResources role (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)
            ⟨output.global,tracker.retagMode⟩ output.child.tree output.tag child := by
  obtain ⟨entry,child,sourceLive,allocation,actual,tag,global,outputFrame,lookup,readDone,childDone,afterRuntime,capacity,growth,oldRoots,oldFields,node,typed,copied,cellModels⟩ :=
    CurrentCallSpatialTypedSourceCopy.invoke options limits remaining span ctx before tracker cover offset len role runtime worldIds distinct short nodeRoom frames frame borrowFrame enabled frameBorrow binding positive signedFits room race nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  have copyStep := copied.2.2.1
  refine ⟨entry,allocation,_,copyStep,?_⟩
  obtain ⟨physicalEntry,base,physicalLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have same : physicalEntry=entry := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans sourceLive))).2
  subst physicalEntry
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have request : Window role.backing.id offset len.toNat (role.backing.id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  have overlap : ∃byte,Window role.backing.id offset len.toNat byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte := ⟨_,request,cell⟩
  have capability := (role.roles i overlap).issued.capability
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,capability.treeExtent,←capability.extent,←allocation]
    exact sourceBounds
  exact copied_resources role rfl runtime distinct short nodeRoom borrowFrame room _ len startEq rfl
    (by intro zero;rw [zero] at positive;cases positive) bounds entry allocation

/-- Actual scoped copy with its source-only installed cover. Original cell
indices/geometries are restricted affinely, never merged into one origin. -/
theorem typed_cover (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (cover : CurrentCallSpatialCover.Context before)
    (offset : Nat) (len : UInt64) (role : RoleCover before tracker cover .mut offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (enabled : before.borrowTracker=some tracker)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before role.family.value role.backing.id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none) :
    let output := CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
    ∃(entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (doneFrame : CompilerFrameContext.ActualFrame) (child : UniIndex)
      (installed : CellResources role (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)
        ⟨output.global,tracker.retagMode⟩ output.child.tree output.tag child),
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
          (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent frames frame before) =
        .ok () (Storage.withCurrent frames doneFrame (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      ∃(current : Present (ActualWorld (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) role.backing.id
          (role.backing.allocation.setExtra output.child.tree))
        (view : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩
          (CurrentCallSpatialSourceCover.context role current (updates role rfl installed)) .mut offset len.toNat),
        view.family=childFamily role output.tag ∧view.backing=CurrentCallSpatialSourceCover.backing role current (updates role rfl installed) := by
  obtain ⟨entry,allocation,doneFrame,copyStep,child,lookup,installed⟩ := typed options limits remaining span ctx before tracker cover offset len role runtime worldIds distinct short nodeRoom frames frame borrowFrame enabled frameBorrow binding positive signedFits room race nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  have current := copied_present role borrowFrame room (UInt64.ofNat offset) len entry allocation
  exact ⟨entry,doneFrame,child,installed,copyStep,lookup,current,sourceCover role rfl current installed,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallSpatialSourceInstall

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialSourceInstall.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual spatial source install dependency {dependency}"
