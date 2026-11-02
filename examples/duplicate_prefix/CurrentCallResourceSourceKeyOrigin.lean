import duplicate_prefix.CurrentCallResourceFnEntry
import duplicate_prefix.GeneralBorrowForestTagHighWaterCtorFrame
namespace DuplicatePrefix.CurrentCallResourceSourceKeyOrigin
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallResourceNormalization CandidateCurrentGrantResources GeneralBorrowFnEntryRegistration
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private def extra (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard

private theorem lookup_exists (mapping : UniKeyMap BorTag) (key : BorTag) (index : UniIndex)
    (member : (key,index)∈mapping.mapping) : ∃ found,mapping.get key=some found := by
  unfold UniKeyMap.get
  cases eq : mapping.mapping.find? (fun row=>row.1==key) with
  | some row => exact ⟨row.2,rfl⟩
  | none =>
    have absent := Array.find?_eq_none.mp eq (key,index) member
    simp at absent

private theorem lookup_member (mapping : UniKeyMap BorTag) (key : BorTag) (index : UniIndex)
    (found : mapping.get key=some index) : ∃ old,(key,old)∈mapping.mapping := by
  unfold UniKeyMap.get at found
  cases eq : mapping.mapping.find? (fun row=>row.1==key) with
  | none => simp [eq] at found
  | some row =>
    have same : row.1=key := by simpa only [beq_iff_eq] using Array.find?_some eq
    exact ⟨row.2,same ▸ Array.mem_of_find?_eq_some eq⟩

private theorem old_lookup_origin (before after : UniKeyMap BorTag) (tag : BorTag)
    (old : ∀ key,tag≠key → after.get key=before.get key) :
    ∀ key index,(key,index)∈after.mapping → key=tag ∨∃ oldIndex,(key,oldIndex)∈before.mapping := by
  intro key index member
  by_cases same : key=tag
  · exact .inl same
  · obtain ⟨found,lookup⟩ := lookup_exists after key index member
    rw [old key (Ne.symm same)] at lookup
    exact .inr (lookup_member before key found lookup)

private theorem insert_origin (before mapping : UniKeyMap BorTag) (tag : BorTag) (index : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh before tag) (fits : before.deassigned.back?=none → before.mapping.size≤4294967295)
    (inserted : before.insert tag=.Inserted mapping index) :
    ∀ key query,(key,query)∈mapping.mapping → key=tag ∨∃old,(key,old)∈before.mapping := by
  cases available : before.deassigned.back? with
  | none =>
    have eq := GeneralBorrowTagMap.insert_append before tag fresh available (fits available)
    rw [eq] at inserted
    cases inserted
    intro key query member
    rcases Array.mem_push.mp member with old | same
    · exact .inr ⟨query,old⟩
    · exact .inl (Prod.mk.inj same).1
  | some free =>
    have eq := GeneralBorrowTagMap.insert_free before tag fresh free available
    rw [eq] at inserted
    cases inserted
    intro key query member
    rcases Array.mem_push.mp member with old | same
    · exact .inr ⟨query,old⟩
    · exact .inl (Prod.mk.inj same).1

private theorem child_of_operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (id : AllocId) (provenance : Provenance) (start amount : UInt64)
    (room : global.nextPointerTag.value < 18446744073709551615) (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation tree global frame id provenance start amount = .ok output) :
    output.child =
      (tree.performBorrowAccessRange (extra provenance)
        (Size.ofBytes start) (Size.ofBytes amount) .Read (registered global frame id room).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes start) (extra provenance) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by
  have allocated := TypedRetagEmpty.allocate_tag global room
  cases provenance with
  | concrete suppliedId tag =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowForestFnEntry.operation,GeneralBorrowForestProtected.read,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl
  | wildcard =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowRawWildcardFnEntryRuntime.operation,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl

/-- Every installed key comes from the original selected tree or the one actual fresh allocation. -/
theorem operation {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    ∀ key index,(key,index)∈output.child.tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨
      ∃oldIndex,(key,oldIndex)∈W.allocation.extra.tagMapping.mapping := by
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,capacity⟩ := CurrentCallResourceFnEntry.prepare_read W runtime state highwater frame room exclusive distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change accessed.tree.nodes=W.allocation.extra.nodes at nodes
  change accessed.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change accessed.tree.locations.size=W.allocation.extra.locations.size at capacity
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have afterRoom : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have afterBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have childEq := child_of_operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
  cases provenance : W.pointer.value.provenance with
  | concrete suppliedId parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [provenance] at binds
    have parentAfter : accessed.tree.nodeAt W.pointer.grant=some parentNode := by change accessed.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : accessed.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    let depth := GeneralBorrowStructuralHistoryMutable.depth accessed.tree afterRuntime.formed.toState
    let slot := GeneralBorrowStructuralHistoryMutable.slot accessed.tree afterRuntime.formed.toState W.pointer.grant parentNode parentAfter afterRoom
    have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth afterRuntime.formed.children afterRuntime.formed.covered
      parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter slot start amount nonzero
      afterRuntime.formed.well afterRuntime.formed.fits afterBounds
    have origins := old_lookup_origin accessed.tree.tagMapping
      (GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree parentTag tracker.global.nextPointerTag start amount).tagMapping tracker.global.nextPointerTag metadata.oldLookup
    rw [childEq]
    rw [tags] at origins
    simpa only [GeneralBorrowFreshMetadataChildMutableSlot.result,accessed,registration,provenance,extra] using origins
  | wildcard =>
    obtain ⟨mapping,index,inserted,_,_⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select accessed.tree afterRuntime.formed.toGraphState tracker.global.nextPointerTag
      freshAfter afterRoom (.ReservedFrz false) .None
    have mapped := GeneralBorrowForestTagHighWaterCtorFrame.mapping accessed.tree tracker.global.nextPointerTag mapping index inserted
      (.ReservedFrz false) .None true rfl rfl rfl (Size.ofBytes start) (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside)
    have origins := insert_origin accessed.tree.tagMapping mapping tracker.global.nextPointerTag index freshAfter (by
      intro noFree
      have aligned := GeneralBorrowFreshStagePool.empty_aligned accessed.tree afterRuntime.formed.allocator.accounting noFree
      change accessed.tree.nodes.data.size+1≤4294967295 at afterRoom
      omega) inserted
    rw [childEq]
    simp only [provenance,extra]
    simp only [accessed,registration,provenance,extra] at mapped
    rw [mapped]
    rw [tags] at origins
    exact origins

/-- Actual constructor geometry retains unique ordered roots. -/
theorem roots {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    output.child.tree.roots.toList.Nodup := by
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,afterRuntime,_,_,nodes,rootFrame,tags,capacity⟩ := CurrentCallResourceFnEntry.prepare_read W runtime state highwater frame room exclusive distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change accessed.tree.nodes=W.allocation.extra.nodes at nodes
  change accessed.tree.roots=W.allocation.extra.roots at rootFrame
  change accessed.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change accessed.tree.locations.size=W.allocation.extra.locations.size at capacity
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have afterRoom : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have afterBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have childEq := child_of_operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
  cases provenance : W.pointer.value.provenance with
  | concrete suppliedId parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [provenance] at binds
    have parentAfter : accessed.tree.nodeAt W.pointer.grant=some parentNode := by change accessed.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : accessed.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    let depth := GeneralBorrowStructuralHistoryMutable.depth accessed.tree afterRuntime.formed.toState
    let slot := GeneralBorrowStructuralHistoryMutable.slot accessed.tree afterRuntime.formed.toState W.pointer.grant parentNode parentAfter afterRoom
    have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth afterRuntime.formed.children afterRuntime.formed.covered
      parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter slot start amount nonzero
      afterRuntime.formed.well afterRuntime.formed.fits afterBounds
    rw [childEq]
    have rootEq := metadata.roots
    rw [rootFrame] at rootEq
    have unique : (GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree parentTag tracker.global.nextPointerTag start amount).roots.toList.Nodup := by rw [rootEq];exact distinct
    simpa only [GeneralBorrowFreshMetadataChildMutableSlot.result,accessed,registration,provenance,extra] using unique
  | wildcard =>
    obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select accessed.tree registration.1 afterRuntime
      tracker.global.nextPointerTag freshAfter afterRoom (.ReservedFrz false) .None
    have exactCtor := GeneralBorrowWildcardConstructorExact.exact accessed.tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter afterRoom mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero afterBounds
    have outside : index∉accessed.tree.roots.toList := by
      intro member
      obtain ⟨node,present,_⟩ := afterRuntime.formed.rootNodes index member
      rw [vacant] at present
      contradiction
    have unique : accessed.tree.roots.toList.Nodup := by rw [rootFrame];exact distinct
    have appended : (accessed.tree.roots.push index).toList.Nodup := by
      rw [Array.toList_push]
      apply List.nodup_append.mpr
      refine ⟨unique,by simp,?_⟩
      intro query member other single equal
      have same : other=index := by simpa using single
      subst other
      subst query
      exact outside member
    rw [childEq]
    simp only [provenance,extra]
    simp only [accessed,registration,provenance,extra] at exactCtor
    rw [exactCtor]
    simpa only [GeneralBorrowPositiveWildcardConstructor.result,WildcardHitZeroConstructor.installed,accessed,registration,provenance,extra] using appended

end
end DuplicatePrefix.CurrentCallResourceSourceKeyOrigin
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSourceKeyOrigin" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved source-key origin dependency {dependency}"
