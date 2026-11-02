import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.GeneralBorrowRangeOutsideOwned

/-! Original return-family resources across the actual spatial source copy.
This is a Bool-window transport, not preservation of an ambient paired cover. -/
namespace DuplicatePrefix.CurrentCallSpatialReturnFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins GeneralBorrowFnEntryRegistration
open S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section

def returnIndex {before tracker ctx offset} (role : RoleCover before tracker ctx .ret offset 1) : Fin role.backing.cells.size :=
  Classical.choose (role.covered (role.backing.id,offset) ⟨rfl,Nat.le_refl _,by omega⟩)

theorem returnOverlap {before tracker ctx offset} (role : RoleCover before tracker ctx .ret offset 1) :
    ∃byte,Window role.backing.id offset 1 byte ∧Window role.backing.id role.backing.cells[returnIndex role].offset role.backing.cells[returnIndex role].length byte :=
  ⟨(role.backing.id,offset),⟨rfl,Nat.le_refl _,by omega⟩,Classical.choose_spec (role.covered (role.backing.id,offset) ⟨rfl,Nat.le_refl _,by omega⟩)⟩

def returnWindow {before tracker ctx offset} (role : RoleCover before tracker ctx .ret offset 1) :
    UniformWindow before tracker (role.roles (returnIndex role) (returnOverlap role)).identities 0 role.backing.id offset 1 .ret :=
  singleByte role (returnIndex role) (returnOverlap role) (role.backing.id,offset) ⟨rfl,Nat.le_refl _,by omega⟩
    (Classical.choose_spec (role.covered (role.backing.id,offset) ⟨rfl,Nat.le_refl _,by omega⟩))

theorem other_present {before tracker ctx mode offset length}
    (source : RoleCover before tracker ctx mode offset length) (frame : FrameState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (old : Present (ActualWorld before) id allocation) (different : id≠source.backing.id) :
    Present (ActualWorld (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)) id allocation := by
  simp only [Present,ActualWorld,Array.toList_map] at old ⊢
  obtain ⟨row,member,same⟩ := List.mem_map.mp old
  have idEq : row.1=id := (Prod.mk.inj same).1
  refine List.mem_map.mpr ⟨row,?_,same⟩
  apply Array.mem_toList_iff.mpr
  apply Array.mem_push.mpr
  apply Or.inl
  apply Array.mem_filter.mpr
  refine ⟨Array.mem_toList_iff.mp member,?_⟩
  simpa only [idEq,bne_iff_ne] using different

/-- Different allocations retain the original Bool family and its SAME cell
map; the only global change is a fresh protector with no old Bool node. -/
theorem different {before tracker ctx mode offset length returnOffset}
    (source : RoleCover before tracker ctx mode offset length)
    (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (different : ret.backing.id≠source.backing.id)
    (retRuntime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :
    let output := CurrentCallSpatialEntryRead.output source frame room start amount
    Nonempty (UniformWindow (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
      ⟨output.global,tracker.retagMode⟩ (ret.roles (returnIndex ret) (returnOverlap ret)).identities 0 ret.backing.id returnOffset 1 .ret) := by
  let old := returnWindow ret
  let current := CurrentCallResourceFnEntry.registered_window old retRuntime frame room
  have present := other_present source frame room start amount entry ret.backing.id ret.backing.allocation ret.backing.live different
  have issued := CurrentCallResourceInstallation.spatial_frame current.issued
    (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
    ⟨(CurrentCallSpatialEntryRead.output source frame room start amount).global,tracker.retagMode⟩ ret.backing.allocation.extra present rfl rfl
    (by intros;assumption) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩) old.precise.completion (by intros;assumption)
  exact ⟨{current with present:=present,issued:=issued}⟩

open Lean Elab Tactic in
elab "return_frame_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with | [(name,_)]=>return mkConst name | _=>throwError "expected checked return-frame theorem {suffix.getString}"

private theorem parents_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree) (C : Completion)
    (parents : ParentInterpretation tree C) : ParentInterpretation {tree with locations:=locations} C := by
  refine ⟨GeneralBorrowStructuralHistoryState.graph_locations tree locations parents.graph,parents.order,parents.dimension,
    parents.physical,parents.edgeLive,parents.primaryNone,?_⟩
  intro position root slot origin edge
  obtain ⟨earlier,originRoot,rootNode,originNode,before,originSlot,rootAt,originAt,exposed,older,path⟩ := parents.virtual position root slot origin edge
  exact ⟨earlier,originRoot,rootNode,originNode,before,originSlot,rootAt,originAt,exposed,older,
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before:={tree with locations:=locations}) (after:=tree) rfl path⟩

def windowData (id : AllocId) (pointer : PointerInstance) (C : Completion) : Identities :=
  ⟨⟨#[(id,⟨C,#[]⟩)],#[pointer],#[⟨0,none,0⟩],fun _ _=>none⟩,#[⟨0,pointer.value⟩],#[]⟩

/-- Scalar return framing uses its own parent interpretation. Source ownership
under that interpretation is never required, even when the request spans cells. -/
theorem same_selected {before tracker ctx mode offset length data owner returnOffset}
    (source : RoleCover before tracker ctx mode offset length)
    (V : UniformWindow before tracker data owner source.backing.id returnOffset 1 .ret)
    (allocationEq : V.allocation=source.backing.allocation)
    (separate : ∀byte,Window source.backing.id offset length byte→Window source.backing.id returnOffset 1 byte→False)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (distinct : source.backing.allocation.extra.roots.toList.Nodup) (short : source.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat)
    (i : Fin source.backing.cells.size)
    (overlap : ∃byte,Window source.backing.id offset length byte ∧Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=source.backing.allocation) :
    let output := CurrentCallSpatialEntryRead.output source frame room start amount
    let post := CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      Nonempty (UniformWindow post ⟨output.global,tracker.retagMode⟩
        (windowData source.backing.id V.pointer (extend V.precise.completion child (source.roles i overlap).grant)) 0 source.backing.id returnOffset 1 .ret) := by
  let accessed := CurrentCallSpatialEntryRead.read source frame room start amount
  let registration := registered tracker.global frame source.backing.id room
  let output := CurrentCallSpatialEntryRead.output source frame room start amount
  obtain ⟨_,_,_,afterChild,capacity,growth,child,lookup,oldRoots,oldNodes,newNode,newAt,newTag⟩ :=
    CurrentCallSpatialEntryConstructor.invoke source exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  obtain ⟨contract,afterRuntime,_⟩ := CurrentCallSpatialEntryRead.invoke source exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  obtain ⟨_,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare source.backing.allocation.extra tracker.global frame source.backing.id room runtime
  have retRuntime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global := by rw [allocationEq];exact runtime
  let current := CurrentCallResourceFnEntry.registered_window V retRuntime frame room
  have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare V.allocation.extra tracker.global frame source.backing.id room retRuntime).2.2.2.1
  have retBound := (V.window (source.backing.id,returnOffset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have fits : returnOffset+1<2^64 := by have := UInt64.toNat_lt V.allocation.byteSize.bytes;have := V.issued.capability.extent;omega
  let lower := UInt64.ofNat returnOffset
  have lowerEq : lower.toNat=returnOffset := by simp only [lower,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : returnOffset<2^64)]
  have upperEq : (lower+1).toNat=returnOffset+1 := by rw [UInt64.toNat_add,lowerEq,show (1:UInt64).toNat=1 from rfl,Nat.mod_eq_of_lt fits]
  have initial := (return_frame_rule ".CurrentCallResourceFnEntry.window_owned") current (by rfl) registeredRuntime lower (lower+1) (by omega) (by omega)
  change OwnedOn (S05CompletedAncestryReadMutable.Authority V.allocation.extra V.precise.completion registration.1.protectedTags V.pointer.grant) lower (lower+1) V.allocation.extra.locations at initial
  rw [allocationEq] at initial
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt source.backing.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat=offset+length := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap,startEq,amountEq]
  have disjoint : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<(lower+1).toNat→point.toNat<start.toNat ∨(start+amount).toNat≤point.toNat := by
    intro point lo hi
    by_cases early : point.toNat<start.toNat
    · exact Or.inl early
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro hit
      exact separate (source.backing.id,point.toNat) ⟨rfl,by omega,by omega⟩ ⟨rfl,by omega,by omega⟩
  have outside := GeneralBorrowRangeOutsideOwned.owned _ source.backing.allocation.extra (provenance source) (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed runtime.formed.well bounds lower (lower+1) disjoint initial
  have afterBool : OwnedOn (S05CompletedAncestryReadMutable.Authority accessed.tree V.precise.completion registration.1.protectedTags V.pointer.grant) lower (lower+1) accessed.tree.locations := by
    intro cursor valid positive lo hi index node atNode
    exact outside cursor valid positive lo hi index node (by rw [←contract.nodes];exact atNode)
  have beforeParents : ParentInterpretation source.backing.allocation.extra V.precise.completion := by rw [←allocationEq];exact V.parents
  have readParents : ParentInterpretation accessed.tree V.precise.completion := by
    rw [contract.tree_eq]
    exact parents_locations _ _ _ beforeParents
  obtain ⟨origin,originAt,_,binding⟩ := (source.roles i overlap).binding
  have originAfter : accessed.tree.nodes.get (source.roles i overlap).grant=some origin := by rw [contract.nodes];exact originAt
  obtain ⟨target,targetAt,_,targetBinding⟩ := V.binding
  rw [allocationEq] at targetAt
  have targetAfter : accessed.tree.nodes.get V.pointer.grant=some target := by rw [contract.nodes];exact targetAt
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1≤4294967295 := by change accessed.tree.nodes.data.size+1≤_;rw [contract.nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh source.backing.allocation.extra tracker.global runtime (source.roles i overlap).grant origin originAt
  obtain ⟨primary,primaryAt,_,_,_⟩ := V.issued.capability.rootNode
  rw [allocationEq] at primaryAt
  have bindingOnly : match source.family.value.provenance with | .concrete _ tag=>tag=origin.tag | .wildcard=>origin.isExposed=true := by
    cases value : source.family.value.provenance with
    | concrete id tag=>exact (show id=source.family.allocation ∧tag=origin.tag from by simpa only [Family.at,value] using binding).2
    | wildcard=>simpa only [Family.at,value] using binding
  obtain ⟨parentChild,parentLookup,parents,_⟩ := CurrentCallSpatialEntryConstructor.parent_subwindow accessed.tree registration.1 V.precise.completion afterRuntime readParents
    source.family.value.provenance (source.roles i overlap).grant origin originAfter bindingOnly tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld older
    ⟨primary,by rw [contract.nodes];exact primaryAt⟩ start amount start start nonzero childBounds (Nat.le_refl _) (by omega)
    (by intro cursor valid impossible;omega)
  have same : parentChild=child := Option.some.inj (parentLookup.symm.trans lookup)
  subst parentChild
  have boolOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree (extend V.precise.completion child (source.roles i overlap).grant) output.global.protectedTags V.pointer.grant) lower (lower+1) output.child.tree.locations := by
    cases value : source.family.value.provenance with
    | concrete id tag=>
      have tagged := afterRuntime.formed.allocator.nodeTags _ _ originAfter
      obtain ⟨_,_,_,_,q,qLookup,owned⟩ := CurrentCallResourceChild.Disjoint.construct accessed.tree registration.1 V.precise.completion afterRuntime readParents origin.tag tracker.global.nextPointerTag (source.roles i overlap).grant V.pointer.grant origin target tagged originAfter targetAfter freshAfter childRoom tagBound tagHeld start amount lower (lower+1) nonzero childBounds disjoint afterBool
      have eqTag : tag=origin.tag := by simpa only [value] using bindingOnly
      have qLookup' : output.child.tree.indexOfTag output.tag=some q := by simpa only [output,CurrentCallSpatialEntryRead.output,provenance,value,eqTag] using qLookup
      have same : q=child := Option.some.inj (qLookup'.symm.trans lookup)
      subst q
      simpa only [output,CurrentCallSpatialEntryRead.output,provenance,value,eqTag] using owned
    | wildcard=>
      obtain ⟨q,qLookup,owned⟩ := CurrentCallResourceChild.WildcardDisjoint.disjoint accessed.tree registration.1 V.precise.completion afterRuntime readParents tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld (source.roles i overlap).grant origin originAfter start amount lower (lower+1) nonzero childBounds V.pointer.grant ⟨target,targetAfter⟩ disjoint afterBool
      have qLookup' : output.child.tree.indexOfTag output.tag=some q := by simpa only [output,CurrentCallSpatialEntryRead.output,provenance,value] using qLookup
      have same : q=child := Option.some.inj (qLookup'.symm.trans lookup)
      subst q
      simpa only [output,CurrentCallSpatialEntryRead.output,provenance,value] using owned
  have vacant : source.backing.allocation.extra.nodes.get child=none := by
    cases oldAt : source.backing.allocation.extra.nodes.get child with
    | none=>rfl
    | some oldNode=>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := oldNodes child oldNode oldAt
      have same : changed=newNode := Option.some.inj (changedAt.symm.trans newAt)
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime child oldNode oldAt
      rw [←changedTag,same,newTag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have present := CurrentCallSpatialSourceInstall.copied_present source frame room start amount entry entryEq
  have issued := CurrentCallResourceInstallation.spatial V.issued V.parents (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry) ⟨output.global,tracker.retagMode⟩ output.child.tree (by simpa only [allocationEq] using present) rfl
    (by simpa only [allocationEq] using capacity) (by simpa only [allocationEq] using oldRoots) (by simpa only [allocationEq] using oldNodes)
    child (source.roles i overlap).grant (by simpa only [allocationEq] using vacant)
  obtain ⟨currentTarget,currentAt,tagEq,_,exposedEq,_⟩ := oldNodes V.pointer.grant target targetAt
  have currentBinding : PointerBinds (source.backing.allocation.setExtra output.child.tree) V.pointer := by
    refine ⟨currentTarget,currentAt,afterChild.formed.allocator.nodeTags _ _ currentAt,?_⟩
    cases value : V.pointer.value.provenance with
    | concrete id tag=>simpa only [value,tagEq] using targetBinding
    | wildcard=>simpa only [value,exposedEq] using targetBinding
  refine ⟨child,lookup,⟨?_⟩⟩
  refine ⟨⟨0,none,0⟩,V.pointer,source.backing.allocation.setExtra output.child.tree,⟨extend V.precise.completion child (source.roles i overlap).grant,#[]⟩,rfl,rfl,V.pointerId,present,by simp [windowData],currentBinding,?_,parents,?_⟩
  · simpa only [allocationEq] using issued
  · intro byte inside
    refine ⟨by simpa only [Allocation.setExtra,Allocation.mapExtra,Allocation.len,←allocationEq] using (V.window byte inside).1,?_⟩
    intro segment member lo hi index node atNode
    simp only [Allocation.setExtra,Allocation.mapExtra] at member lo hi atNode ⊢
    obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have byteEq : byte.2=returnOffset := by have := inside.2;omega
    have rights := boolOwned position valid (by omega) (by omega) (by omega) index node atNode
    have realized := CandidateCurrentGrantRuntime.realized _ _ (afterChild.possible position valid index node atNode) ((afterChild.formed.profile position valid).present index node atNode)
    constructor
    · intro below
      exact (return_frame_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact (return_frame_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash

def fallbackIndex {before tracker ctx mode offset length}
    (source : RoleCover before tracker ctx mode offset length) (positive : 0<length) : Fin source.backing.cells.size :=
  Classical.choose (source.covered (source.backing.id,offset) ⟨rfl,Nat.le_refl _,by omega⟩)

theorem fallbackOverlap {before tracker ctx mode offset length}
    (source : RoleCover before tracker ctx mode offset length) (positive : 0<length) :
    CurrentCallSpatialSourceCover.Active source (fallbackIndex source positive) :=
  ⟨(source.backing.id,offset),⟨rfl,Nat.le_refl _,by omega⟩,
    Classical.choose_spec (source.covered (source.backing.id,offset) ⟨rfl,Nat.le_refl _,by omega⟩)⟩

/-- The Bool cell is identified in the SAME initial common context. -/
def commonIndex {before tracker ctx mode offset length returnOffset}
    (source : RoleCover before tracker ctx mode offset length) (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) : Fin source.backing.cells.size :=
  ⟨(returnIndex ret).val,by
    have backing := ctx.same_backing ret.backingAt source.backingAt same
    have sizes := congrArg (fun b : AllocationCover before=>b.cells.size) backing
    have bound := (returnIndex ret).isLt
    omega⟩

/-- Where the shared Bool cell intersects the source request, its SAME source
grant is mandatory. Outside that request a fixed ACTUAL covered source cell
supplies the real exposed wildcard origin; it conveys no ownership outside
source bytes. -/
def selectedIndex {before tracker ctx mode offset length returnOffset}
    (source : RoleCover before tracker ctx mode offset length) (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) (positive : 0<length) : Fin source.backing.cells.size := by
  classical
  exact if CurrentCallSpatialSourceCover.Active source (commonIndex source ret same)
    then commonIndex source ret same else fallbackIndex source positive

theorem selectedOverlap {before tracker ctx mode offset length returnOffset}
    (source : RoleCover before tracker ctx mode offset length) (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) (positive : 0<length) :
    CurrentCallSpatialSourceCover.Active source (selectedIndex source ret same positive) := by
  classical
  unfold selectedIndex
  split
  · assumption
  · exact fallbackOverlap source positive

theorem selected_common {before tracker ctx mode offset length returnOffset}
    (source : RoleCover before tracker ctx mode offset length) (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id) (positive : 0<length)
    (overlap : CurrentCallSpatialSourceCover.Active source (commonIndex source ret same)) :
    selectedIndex source ret same positive=commonIndex source ret same := by
  classical
  simp only [selectedIndex,ite_eq_left overlap]

/-- Same-allocation source copying retains the original Bool family under
its own fixed cell map, extended at the ONE actual child. -/
theorem same {before tracker ctx offset length returnOffset}
    (source : RoleCover before tracker ctx .mut offset length)
    (ret : RoleCover before tracker ctx .ret returnOffset 1)
    (same : ret.backing.id=source.backing.id)
    (separate : ∀byte,Window source.backing.id offset length byte→Window source.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (distinct : source.backing.allocation.extra.roots.toList.Nodup) (short : source.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat)
    (positive : 0<length)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=source.backing.allocation) :
    let output := CurrentCallSpatialEntryRead.output source frame room start amount
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      Nonempty (UniformWindow (CurrentCallSpatialSourceInstall.copiedMachine source frame room start amount entry)
        ⟨output.global,tracker.retagMode⟩
        (windowData source.backing.id (returnWindow ret).pointer
          (extend (returnWindow ret).precise.completion child
            (source.roles (selectedIndex source ret same positive) (selectedOverlap source ret same positive)).grant))
        0 source.backing.id returnOffset 1 .ret) := by
  let V := returnWindow ret
  let current : UniformWindow before tracker (ret.roles (returnIndex ret) (returnOverlap ret)).identities 0 source.backing.id returnOffset 1 .ret := by
    refine ⟨V.loan,V.pointer,V.allocation,V.precise,V.loanAt,V.pointerAt,V.pointerId.trans same,?_,?_,V.binding,?_,V.parents,?_⟩
    · simpa only [same] using V.present
    · simpa only [same] using V.preciseAt
    · simpa only [same] using V.issued
    · intro byte inside
      apply V.window
      simpa only [same] using inside
  have allocationEq : current.allocation=source.backing.allocation := by
    have backing := ctx.same_backing ret.backingAt source.backingAt same
    exact congrArg AllocationCover.allocation backing
  exact same_selected source current allocationEq separate rfl runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
    (selectedIndex source ret same positive) (selectedOverlap source ret same positive) entry entryEq

end
end DuplicatePrefix.CurrentCallSpatialReturnFrame

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialReturnFrame.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial return-frame dependency {dependency}"
