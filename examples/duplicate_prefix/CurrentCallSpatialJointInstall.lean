import duplicate_prefix.CurrentCallSpatialReturnFrame
import duplicate_prefix.CurrentCallSpatialSourceState

/-! Joint current cover geometry after one spatial source copy. Every original
cell and other allocation is retained. Only the selected source allocation's
parent maps are deterministically extended; no outside-source ownership is
claimed for the fresh child. -/
namespace DuplicatePrefix.CurrentCallSpatialJointInstall
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialReturnFrame
open GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins GeneralBorrowFnEntryRegistration S05ConcreteProtectedChildCompletion
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallTypedSourceCopy CurrentCallSpatialSourceInstall
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section

variable {before tracker ctx mode offset length} (source : RoleCover before tracker ctx mode offset length)

def originIndex (positive : 0<length) (i : Fin source.backing.cells.size) : Fin source.backing.cells.size := by
  classical
  exact if CurrentCallSpatialSourceCover.Active source i then i else fallbackIndex source positive

theorem originOverlap (positive : 0<length) (i : Fin source.backing.cells.size) :
    CurrentCallSpatialSourceCover.Active source (originIndex source positive i) := by
  classical
  unfold originIndex
  split
  · assumption
  · exact fallbackOverlap source positive

theorem origin_active (positive : 0<length) (i : Fin source.backing.cells.size)
    (active : CurrentCallSpatialSourceCover.Active source i) : originIndex source positive i=i := by
  classical
  simp only [originIndex,ite_eq_left active]

def extended (positive : 0<length) (child : UniIndex) (i : Fin source.backing.cells.size) : Completion :=
  extend source.backing.cells[i].completion child (source.roles (originIndex source positive i) (originOverlap source positive i)).grant

theorem parents (positive : 0<length) (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (distinct : source.backing.allocation.extra.roots.toList.Nodup) (short : source.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat) :
    let output := CurrentCallSpatialEntryRead.output source frame room start amount
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      ∀i,ParentInterpretation output.child.tree (extended source positive child i) := by
  obtain ⟨_,_,_,_,_,_,child,lookup,_,_,_⟩ := CurrentCallSpatialEntryConstructor.invoke source exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  obtain ⟨contract,afterRuntime,oldParents⟩ := CurrentCallSpatialEntryRead.invoke source exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  obtain ⟨_,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare source.backing.allocation.extra tracker.global frame source.backing.id room runtime
  let accessed := CurrentCallSpatialEntryRead.read source frame room start amount
  let registration := registered tracker.global frame source.backing.id room
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1≤4294967295 := by change accessed.tree.nodes.data.size+1≤_;rw [contract.nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt source.backing.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat=start.toNat+amount.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  obtain ⟨primary,primaryAt,_,_,_⟩ := (source.roles (fallbackIndex source positive) (fallbackOverlap source positive)).issued.capability.rootNode
  refine ⟨child,lookup,?_⟩
  intro i
  let selected := originIndex source positive i
  let overlap := originOverlap source positive i
  obtain ⟨node,nodeAt,_,binding⟩ := (source.roles selected overlap).binding
  have afterAt : accessed.tree.nodes.get (source.roles selected overlap).grant=some node := by rw [contract.nodes];exact nodeAt
  have bindingOnly : match source.family.value.provenance with | .concrete _ tag=>tag=node.tag | .wildcard=>node.isExposed=true := by
    cases value : source.family.value.provenance with
    | concrete id tag=>exact (show id=source.family.allocation ∧tag=node.tag from by simpa only [Family.at,value] using binding).2
    | wildcard=>simpa only [Family.at,value] using binding
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh source.backing.allocation.extra tracker.global runtime (source.roles selected overlap).grant node nodeAt
  obtain ⟨ownChild,ownLookup,model,_⟩ := CurrentCallSpatialEntryConstructor.parent_subwindow accessed.tree registration.1 source.backing.cells[i].completion afterRuntime (oldParents i)
    source.family.value.provenance (source.roles selected overlap).grant node afterAt bindingOnly tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld older
    ⟨primary,by rw [contract.nodes];exact primaryAt⟩ start amount start start nonzero childBounds (Nat.le_refl _) (by omega)
    (by intro cursor valid impossible;omega)
  have same : ownChild=child := Option.some.inj (ownLookup.symm.trans lookup)
  subst ownChild
  exact model

private theorem ofFn_fin {α : Type} {n : Nat} (f : Fin n→α) (i : Fin (Array.ofFn f).size) :
    (Array.ofFn f)[i]=f ⟨i.val,by simpa only [Array.size_ofFn] using i.isLt⟩ := by
  change (Array.ofFn f)[i.val]=_
  rw [Array.getElem_ofFn]

variable (positive : 0<length) (frame : FrameState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (start amount : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=source.backing.allocation)
    (child : UniIndex)
    (models : ∀i,ParentInterpretation (CurrentCallSpatialEntryRead.output source frame room start amount).child.tree (extended source positive child i))

def sourceBacking : AllocationCover (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry) where
  id := source.backing.id
  allocation := source.backing.allocation.setExtra (CurrentCallSpatialEntryRead.output source frame room start amount).child.tree
  live := CurrentCallSpatialSourceInstall.copied_present source frame room start amount entry entryEq
  cells := Array.ofFn (fun i : Fin source.backing.cells.size=>
    ⟨source.backing.cells[i].offset,source.backing.cells[i].length,extended source positive child i,models i⟩)
  disjoint := by
    intro i j different byte first second
    let oi : Fin source.backing.cells.size := ⟨i.val,by simpa only [Array.size_ofFn] using i.isLt⟩
    let oj : Fin source.backing.cells.size := ⟨j.val,by simpa only [Array.size_ofFn] using j.isLt⟩
    apply source.backing.disjoint oi oj (by intro same;apply different;have values : i.val=j.val := congrArg (fun k : Fin source.backing.cells.size=>k.val) same;exact Fin.ext values) byte
    · simpa only [ofFn_fin,oi] using first
    · simpa only [ofFn_fin,oj] using second

def otherBacking (backing : AllocationCover before) (different : backing.id≠source.backing.id) :
    AllocationCover (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry) :=
  ⟨backing.id,backing.allocation,other_present source frame room start amount entry backing.id backing.allocation backing.live different,backing.cells,backing.disjoint⟩

def update (backing : AllocationCover before) : AllocationCover (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry) := by
  classical
  exact if h : backing.id=source.backing.id then sourceBacking source positive frame room start amount entry entryEq child models
    else otherBacking source frame room start amount entry backing h

theorem update_id (backing : AllocationCover before) :
    (update source positive frame room start amount entry entryEq child models backing).id=backing.id := by
  classical
  unfold update
  split
  · exact Eq.symm (by assumption)
  · rfl

def context : Context (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry) where
  allocations := ctx.allocations.map (update source positive frame room start amount entry entryEq child models)
  unique := by
    have ids : (ctx.allocations.map (update source positive frame room start amount entry entryEq child models)).toList.map AllocationCover.id=
        ctx.allocations.toList.map AllocationCover.id := by
      simp only [Array.toList_map,List.map_map]
      apply List.map_congr_left
      intro backing member
      exact update_id source positive frame room start amount entry entryEq child models backing
    rw [ids]
    exact ctx.unique

theorem source_member : sourceBacking source positive frame room start amount entry entryEq child models ∈
    (context source positive frame room start amount entry entryEq child models).allocations.toList := by
  classical
  simp only [context,Array.toList_map]
  exact List.mem_map.mpr ⟨source.backing,source.backingAt,by simp [update]⟩

theorem other_member (backing : AllocationCover before) (member : backing∈ctx.allocations.toList)
    (different : backing.id≠source.backing.id) : otherBacking source frame room start amount entry backing different ∈
    (context source positive frame room start amount entry entryEq child models).allocations.toList := by
  classical
  simp only [context,Array.toList_map]
  exact List.mem_map.mpr ⟨backing,member,by simp only [update,dite_eq_right different]⟩

/-- All original cell positions remain, including those with no source byte. -/
theorem cell_completion (i : Fin source.backing.cells.size) :
    (sourceBacking source positive frame room start amount entry entryEq child models).cells[i.val]'(by simp only [sourceBacking,Array.size_ofFn];exact i.isLt) =
    ⟨source.backing.cells[i].offset,source.backing.cells[i].length,extended source positive child i,models i⟩ := by
  simp only [sourceBacking,Array.getElem_ofFn]

private theorem grants_equal (i j : Fin source.backing.cells.size)
    (hi : CurrentCallSpatialSourceCover.Active source i) (hj : CurrentCallSpatialSourceCover.Active source j) (same : i=j) :
    (source.roles i hi).grant=(source.roles j hj).grant := by
  cases same
  rfl

/-- Source-active cells agree with the previously installed source-only view. -/
theorem active_completion (i : Fin source.backing.cells.size) (active : CurrentCallSpatialSourceCover.Active source i) :
    extended source positive child i=extend source.backing.cells[i].completion child (source.roles i active).grant := by
  exact congrArg (fun grant=>extend source.backing.cells[i].completion child grant)
    (grants_equal source _ i (originOverlap source positive i) active (origin_active source positive i active))

/-- The Bool selector is exactly the joint cover's selector at its original
common-context index, including the single fixed fallback outside the source. -/
theorem return_origin {returnOffset} (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) :
    originIndex source positive (commonIndex source ret same)=selectedIndex source ret same positive := by
  rfl

private theorem original_return_completion {returnOffset} (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) :
    source.backing.cells[commonIndex source ret same].completion=(returnWindow ret).precise.completion := by
  have backing := ctx.same_backing ret.backingAt source.backingAt same
  have arrays : (source.backing.cells.map (fun cell=>cell.completion))=(ret.backing.cells.map (fun cell=>cell.completion)) :=
    congrArg (fun backing : AllocationCover before=>backing.cells.map (fun cell=>cell.completion)) backing.symm
  have lookups := congrArg (fun array : Array Completion=>array[(returnIndex ret).val]?) arrays
  have sourceBound : (returnIndex ret).val<source.backing.cells.size := (commonIndex source ret same).isLt
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem sourceBound,Array.getElem?_eq_getElem (returnIndex ret).isLt,Option.map_some,Option.some.injEq] at lookups
  exact lookups

theorem return_completion {returnOffset} (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) :
    extended source positive child (commonIndex source ret same)=
      extend (returnWindow ret).precise.completion child
        (source.roles (selectedIndex source ret same positive) (selectedOverlap source ret same positive)).grant := by
  have grants := grants_equal source _ _ (originOverlap source positive (commonIndex source ret same))
    (selectedOverlap source ret same positive) (return_origin source positive ret same)
  change extend source.backing.cells[commonIndex source ret same].completion child _=_
  rw [original_return_completion source ret same]
  exact congrArg (fun grant=>extend (returnWindow ret).precise.completion child grant) grants

/-- Actual source resources inhabit the SAME joint context, not a separately
spliced source-only context. All inactive cells remain structurally present. -/
def sourceRole (exclusive : demandOf mode=.exclusive)
    (installed : CurrentCallSpatialSourceInstall.CellResources source
      (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
      ⟨(CurrentCallSpatialEntryRead.output source frame room start amount).global,tracker.retagMode⟩
      (CurrentCallSpatialEntryRead.output source frame room start amount).child.tree
      (CurrentCallSpatialEntryRead.output source frame room start amount).tag child) :
    RoleCover (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
      ⟨(CurrentCallSpatialEntryRead.output source frame room start amount).global,tracker.retagMode⟩
      (context source positive frame room start amount entry entryEq child models) mode offset length where
  family := CurrentCallSpatialSourceInstall.childFamily source (CurrentCallSpatialEntryRead.output source frame room start amount).tag
  backing := sourceBacking source positive frame room start amount entry entryEq child models
  backingAt := source_member source positive frame room start amount entry entryEq child models
  id := rfl
  covered := by
    intro byte hit
    obtain ⟨i,inside⟩ := source.covered byte hit
    refine ⟨⟨i.val,by simp only [sourceBacking,Array.size_ofFn];exact i.isLt⟩,?_⟩
    simpa only [sourceBacking,Fin.getElem_fin,Array.getElem_ofFn] using inside
  roles := by
    intro i overlap
    let original : Fin source.backing.cells.size := ⟨i.val,by simpa only [sourceBacking,Array.size_ofFn] using i.isLt⟩
    have active : CurrentCallSpatialSourceCover.Active source original := by
      simpa only [sourceBacking,ofFn_fin,CurrentCallSpatialSourceCover.Active,original] using overlap
    have data := installed original active
    have completion := active_completion source positive child original active
    rw [←completion] at data
    have result : CellRole (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
        ⟨(CurrentCallSpatialEntryRead.output source frame room start amount).global,tracker.retagMode⟩
        (sourceBacking source positive frame room start amount entry entryEq child models)
        ⟨source.backing.cells[original].offset,source.backing.cells[original].length,extended source positive child original,models original⟩
        (CurrentCallSpatialSourceInstall.childFamily source (CurrentCallSpatialEntryRead.output source frame room start amount).tag) mode offset length := by
      refine ⟨child,data.2.1,data.2.2.1,?_⟩
      intro byte request cell
      simpa only [sourceBacking,Allocation.setExtra,Allocation.mapExtra,Allocation.len,exclusive] using data.2.2.2 byte request cell
    simpa only [sourceBacking,ofFn_fin,original] using result

private theorem pointer_same (pointer : PointerInstance) (id : AllocId) (same : pointer.allocation=id) :
    ({allocation:=id,value:=pointer.value,grant:=pointer.grant} : PointerInstance)=pointer := by
  cases pointer
  cases same
  rfl

/-- A scalar window's current certificate reconstructs its role on the one
joint backing. Disjoint cells make the Bool cell unique. -/
private def scalarRole {post : Before} {next : MachineHooks.BorrowState} {joint : Context post}
    (backing : AllocationCover post) (backingAt : backing∈joint.allocations.toList)
    (slot off : Nat) {data owner}
    (W : UniformWindow post next data owner backing.id off 1 .ret)
    (allocationEq : W.allocation=backing.allocation)
    (j : Fin backing.cells.size)
    (inside : Window backing.id backing.cells[j].offset backing.cells[j].length (backing.id,off))
    (completionEq : backing.cells[j].completion=W.precise.completion) :
    RoleCover post next joint .ret off 1 where
  family := ⟨slot,backing.id,W.pointer.value⟩
  backing := backing
  backingAt := backingAt
  id := rfl
  covered := by
    intro byte hit
    refine ⟨j,?_⟩
    obtain ⟨id,lower,upper⟩ := hit
    have byteEq : byte.2=off := by omega
    exact ⟨id,by rw [byteEq];exact inside.2.1,by rw [byteEq];exact inside.2.2⟩
  roles := by
    intro i overlap
    have equal : i=j := by
      obtain ⟨byte,request,cell⟩ := overlap
      have atJ : Window backing.id backing.cells[j].offset backing.cells[j].length byte := by
        have byteEq : byte.2=off := by have := request.2;omega
        exact ⟨request.1,by rw [byteEq];exact inside.2.1,by rw [byteEq];exact inside.2.2⟩
      by_cases same : i=j
      · exact same
      · exact False.elim (backing.disjoint i j same byte cell atJ)
    subst i
    have pointerEq : ({allocation:=backing.id,value:=W.pointer.value,grant:=W.pointer.grant} : PointerInstance)=W.pointer :=
      pointer_same W.pointer backing.id W.pointerId
    refine ⟨W.pointer.grant,?_,?_,?_⟩
    · simpa only [Family.at,pointerEq,←allocationEq] using W.binding
    · simpa only [←allocationEq,completionEq] using W.issued
    · intro byte request cell
      simpa only [←allocationEq,completionEq] using W.window byte request

private theorem canonical_fields {post next id off}
    (pointer : PointerInstance) (C : Completion)
    (W : UniformWindow post next (windowData id pointer C) 0 id off 1 .ret) :
    W.pointer=pointer ∧ W.precise.completion=C := by
  have loan : W.loan=⟨0,none,0⟩ := by
    have found := W.loanAt
    change some (⟨0,none,0⟩ : Loan)=some W.loan at found
    exact Option.some.inj found.symm
  have pointerEq : W.pointer=pointer := by
    have found := W.pointerAt
    rw [loan] at found
    change some pointer=some W.pointer at found
    exact Option.some.inj found.symm
  have precise : W.precise=(⟨C,#[]⟩ : PreciseAllocation) := by
    have found := W.preciseAt
    change (id,W.precise)∈[(id,(⟨C,#[]⟩ : PreciseAllocation))] at found
    exact (Prod.mk.inj (List.mem_singleton.mp found)).2
  exact ⟨pointerEq,congrArg PreciseAllocation.completion precise⟩

private theorem family_same (family : Family) (id : AllocId) (same : family.allocation=id) :
    (⟨family.slot,id,family.value⟩ : Family)=family := by
  cases family
  cases same
  rfl

private theorem common_inside {returnOffset} (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) :
    Window source.backing.id source.backing.cells[commonIndex source ret same].offset
      source.backing.cells[commonIndex source ret same].length (source.backing.id,returnOffset) := by
  have backing := ctx.same_backing ret.backingAt source.backingAt same
  have arrays := congrArg (fun backing : AllocationCover before=>backing.cells.map (fun cell=>(cell.offset,cell.length))) backing.symm
  have lookups := congrArg (fun array : Array (Nat×Nat)=>array[(returnIndex ret).val]?) arrays
  have bound : (returnIndex ret).val<source.backing.cells.size := (commonIndex source ret same).isLt
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem bound,Array.getElem?_eq_getElem (returnIndex ret).isLt,Option.map_some,Option.some.injEq,Prod.mk.injEq] at lookups
  have inside := Classical.choose_spec (ret.covered (ret.backing.id,returnOffset) ⟨rfl,Nat.le_refl _,by omega⟩)
  refine ⟨rfl,?_,?_⟩
  · change source.backing.cells[(returnIndex ret).val].offset≤returnOffset
    rw [lookups.1]
    exact inside.2.1
  · change returnOffset<source.backing.cells[(returnIndex ret).val].offset+source.backing.cells[(returnIndex ret).val].length
    rw [lookups.1,lookups.2]
    exact inside.2.2

private theorem post_ids {post : Before} {next : MachineHooks.BorrowState}
    (state : DuplicatePrefixRuntimeInput.State post next) : ((ActualWorld post).toList.map Prod.fst).Nodup := by
  simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds

/-- Both roles coexist on the SAME joint context after the real source copy.
The post-state argument is an internal output of SpatialSourceState.invoke;
the public typed join below derives it from the original representation. -/
theorem same_views {before tracker ctx offset length returnOffset}
    (source : RoleCover before tracker ctx .mut offset length) (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id)
    (separate : ∀byte,Window source.backing.id offset length byte→Window source.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (distinct : source.backing.allocation.extra.roots.toList.Nodup) (short : source.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat) (positive : 0<length)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=source.backing.allocation)
    (state : DuplicatePrefixRuntimeInput.State (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
      ⟨(CurrentCallSpatialEntryRead.output source frame room start amount).global,tracker.retagMode⟩) :
    let output := CurrentCallSpatialEntryRead.output source frame room start amount
    let post := CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry
    ∃(child : UniIndex) (models : ∀i,ParentInterpretation output.child.tree (extended source positive child i)),
      output.child.tree.indexOfTag output.tag=some child ∧
      ∃(src : RoleCover post ⟨output.global,tracker.retagMode⟩ (context source positive frame room start amount entry entryEq child models) .mut offset length)
        (dst : RoleCover post ⟨output.global,tracker.retagMode⟩ (context source positive frame room start amount entry entryEq child models) .ret returnOffset 1),
        src.family=CurrentCallSpatialSourceInstall.childFamily source output.tag ∧dst.family=ret.family := by
  obtain ⟨child,lookup,models⟩ := parents source positive rfl runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  obtain ⟨sourceChild,sourceLookup,installed⟩ := CurrentCallSpatialSourceInstall.copied_resources source rfl runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds entry entryEq
  have sameSource : sourceChild=child := Option.some.inj (sourceLookup.symm.trans lookup)
  subst sourceChild
  obtain ⟨retChild,retLookup,⟨W⟩⟩ := CurrentCallSpatialReturnFrame.same source ret same separate runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds positive entry entryEq
  have sameRet : retChild=child := Option.some.inj (retLookup.symm.trans lookup)
  subst retChild
  let backing := sourceBacking source positive frame room start amount entry entryEq child models
  let j : Fin backing.cells.size := ⟨(commonIndex source ret same).val,by simp only [backing,sourceBacking,Array.size_ofFn];exact (commonIndex source ret same).isLt⟩
  have inside : Window backing.id backing.cells[j].offset backing.cells[j].length (backing.id,returnOffset) := by
    simpa only [backing,sourceBacking,ofFn_fin,j] using common_inside source ret same
  have fields := canonical_fields _ _ W
  have allocationEq : W.allocation=backing.allocation := CandidateCurrentUniformOwnerWindow.same_id _ (post_ids state)
    source.backing.id W.allocation backing.allocation W.present backing.live
  have completionEq : backing.cells[j].completion=W.precise.completion := by
    simpa only [backing,sourceBacking,ofFn_fin,j] using (return_completion source positive child ret same).trans fields.2.symm
  let dst := scalarRole (length := 0) backing (source_member source positive frame room start amount entry entryEq child models) ret.family.slot returnOffset W allocationEq j inside completionEq
  refine ⟨child,models,lookup,sourceRole source positive frame room start amount entry entryEq child models rfl installed,dst,rfl,?_⟩
  change (⟨ret.family.slot,source.backing.id,W.pointer.value⟩ : Family)=ret.family
  rw [fields.1]
  exact family_same ret.family source.backing.id (ret.id.trans same)

/-- Different-allocation return roles retain their original cell maps on the
SAME joint context, while all source-allocation cells are also retained. -/
theorem different_views {before tracker ctx offset length returnOffset}
    (source : RoleCover before tracker ctx .mut offset length) (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (different : ret.backing.id≠source.backing.id)
    (retRuntime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (distinct : source.backing.allocation.extra.roots.toList.Nodup) (short : source.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat) (positive : 0<length)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=source.backing.allocation)
    (state : DuplicatePrefixRuntimeInput.State (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
      ⟨(CurrentCallSpatialEntryRead.output source frame room start amount).global,tracker.retagMode⟩) :
    let output := CurrentCallSpatialEntryRead.output source frame room start amount
    let post := CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry
    ∃(child : UniIndex) (models : ∀i,ParentInterpretation output.child.tree (extended source positive child i)),
      output.child.tree.indexOfTag output.tag=some child ∧
      ∃(src : RoleCover post ⟨output.global,tracker.retagMode⟩ (context source positive frame room start amount entry entryEq child models) .mut offset length)
        (dst : RoleCover post ⟨output.global,tracker.retagMode⟩ (context source positive frame room start amount entry entryEq child models) .ret returnOffset 1),
        src.family=CurrentCallSpatialSourceInstall.childFamily source output.tag ∧dst.family=ret.family := by
  obtain ⟨child,lookup,models⟩ := parents source positive rfl runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  obtain ⟨sourceChild,sourceLookup,installed⟩ := CurrentCallSpatialSourceInstall.copied_resources source rfl runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds entry entryEq
  have sameSource : sourceChild=child := Option.some.inj (sourceLookup.symm.trans lookup)
  subst sourceChild
  obtain ⟨W⟩ := CurrentCallSpatialReturnFrame.different source ret different retRuntime frame room start amount entry
  let backing := otherBacking source frame room start amount entry ret.backing different
  let j : Fin backing.cells.size := returnIndex ret
  have inside : Window backing.id backing.cells[j].offset backing.cells[j].length (backing.id,returnOffset) :=
    Classical.choose_spec (ret.covered (ret.backing.id,returnOffset) ⟨rfl,Nat.le_refl _,by omega⟩)
  have fields := canonical_fields (returnWindow ret).pointer (returnWindow ret).precise.completion W
  have allocationEq : W.allocation=backing.allocation := CandidateCurrentUniformOwnerWindow.same_id _ (post_ids state)
    ret.backing.id W.allocation backing.allocation W.present backing.live
  have completionEq : backing.cells[j].completion=W.precise.completion := fields.2.symm
  let dst := scalarRole (length := 0) backing (other_member source positive frame room start amount entry entryEq child models ret.backing ret.backingAt different) ret.family.slot returnOffset W allocationEq j inside completionEq
  refine ⟨child,models,lookup,sourceRole source positive frame room start amount entry entryEq child models rfl installed,dst,rfl,?_⟩
  change (⟨ret.family.slot,ret.backing.id,W.pointer.value⟩ : Family)=ret.family
  rw [fields.1]
  exact family_same ret.family ret.backing.id ret.id

private theorem runtime_present {before : Before} {tracker : MachineHooks.BorrowState}
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree) (present : Present (ActualWorld before) id allocation) :
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global := by
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨row,member,same⟩ := List.mem_map.mp present
  have selected : DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global :=
    ⟨state.formed row member,state.coherent row member,state.possible row member,highwater row member⟩
  have allocationEq := (Prod.mk.inj same).2
  rw [allocationEq] at selected
  exact selected

/-- One actual scoped source copy produces State and two roles on the SAME
joint cover. Empty/latent sources and ordinary adequacy remain separate. -/
theorem typed (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (cover : CurrentCallSpatialCover.Context before)
    (offset : Nat) (len : UInt64) (role : RoleCover before tracker cover .mut offset len.toNat)
    (returnOffset : Nat) (ret : RoleCover before tracker cover .ret returnOffset 1)
    (separate : ∀byte,Window role.backing.id offset len.toNat byte→Window ret.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState)
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
    ∃(entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (doneFrame : CompilerFrameContext.ActualFrame)
      (child : UniIndex) (models : ∀i,ParentInterpretation output.child.tree (extended role positive child i)),
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
          (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent frames frame before)=
        .ok () (Storage.withCurrent frames doneFrame (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      doneFrame.extra.borrowTracker=some output.frame ∧doneFrame.returnPlace=frame.returnPlace ∧
      DuplicatePrefixRuntimeInput.State (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩ ∧
      (∀row∈(copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry).memory.live.toList,
        GeneralBorrowForestTagHighWater.Below row.2.allocation.extra output.global.protectedTags output.global.nextPointerTag) ∧
      ∃(entryEq : entry.allocation=role.backing.allocation)
        (src : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩
          (context role positive borrowFrame room (UInt64.ofNat offset) len entry entryEq child models) .mut offset len.toNat)
        (dst : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩
          (context role positive borrowFrame room (UInt64.ofNat offset) len entry entryEq child models) .ret returnOffset 1),
        src.family=childFamily role output.tag ∧dst.family=ret.family := by
  obtain ⟨entry,doneFrame,child,installed,sourceLive,allocation,copyStep,lookup,borrowed,returnPlace,continuation,body,bodyIdentity,functionInstance,location,postState,postHighwater,_⟩ :=
    CurrentCallSpatialSourceState.invoke options limits remaining span ctx before tracker cover offset len role runtime state highwater distinct short nodeRoom frames frame borrowFrame frameBorrow binding positive signedFits room race nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  obtain ⟨physicalEntry,base,physicalLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have sameEntry : physicalEntry=entry := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans sourceLive))).2
  subst physicalEntry
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have treeLength := state.treeLength (role.backing.id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive))
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,←allocation,treeLength,←length]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;cases positive
  have joined : ∃(q : UniIndex) (models : ∀i,ParentInterpretation (CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).child.tree (extended role positive q i)),
      (CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).child.tree.indexOfTag tracker.global.nextPointerTag=some q ∧
      ∃(src : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨(CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).global,tracker.retagMode⟩
          (context role positive borrowFrame room (UInt64.ofNat offset) len entry allocation q models) .mut offset len.toNat)
        (dst : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨(CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).global,tracker.retagMode⟩
          (context role positive borrowFrame room (UInt64.ofNat offset) len entry allocation q models) .ret returnOffset 1),
        src.family=childFamily role tracker.global.nextPointerTag ∧dst.family=ret.family := by
    by_cases same : ret.backing.id=role.backing.id
    · exact same_views role ret same (by intro byte sourceHit retHit;apply separate byte sourceHit;simpa only [same] using retHit)
        runtime distinct short nodeRoom borrowFrame room (UInt64.ofNat offset) len startEq rfl nonzero bounds positive entry allocation postState
    · exact different_views role ret same (runtime_present state highwater ret.backing.id ret.backing.allocation ret.backing.live)
        runtime distinct short nodeRoom borrowFrame room (UInt64.ofNat offset) len startEq rfl nonzero bounds positive entry allocation postState
  obtain ⟨q,models,qLookup,src,dst,sourceFamily,retFamily⟩ := joined
  have same : q=child := Option.some.inj (qLookup.symm.trans lookup)
  subst q
  exact ⟨entry,doneFrame,child,models,copyStep,lookup,borrowed,returnPlace,postState,postHighwater,allocation,src,dst,sourceFamily,retFamily⟩

end
end DuplicatePrefix.CurrentCallSpatialJointInstall

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialJointInstall.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual joint spatial installation dependency {dependency}"
