import duplicate_prefix.CurrentCallExclusiveWindowFrame
import duplicate_prefix.CurrentCallDefaultMutableDisjoint
namespace DuplicatePrefix.CurrentCallExclusiveWindowFrameSeparate
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFnEntryRegistration CurrentCallResourceFnEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private def extra (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard
/-- The existing protected disjoint-window frame with independently retained
technical dictionaries. No family index is renamed or reconstructed. -/
theorem invoke {before tracker data owner id offset length mode targetData targetOwner targetOffset targetLength targetMode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (V : UniformWindow before tracker targetData targetOwner id targetOffset targetLength targetMode)
    (targetPositive : 0 < targetLength) (targetExclusive : demandOf targetMode = .exclusive)
    (allocationEq : V.allocation = W.allocation) (completionEq : V.precise.completion = W.precise.completion)
    (separate : ∀ byte,Window id offset length byte → Window id targetOffset targetLength byte → False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output child,CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      Nonempty (BorrowWitness W output child start amount) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags V.pointer.grant)
        (UInt64.ofNat targetOffset) (UInt64.ofNat targetOffset+UInt64.ofNat targetLength) output.child.tree.locations ∧
      PointerBinds (W.allocation.setExtra output.child.tree) V.pointer ∧
      (∀ byte,Window id targetOffset targetLength byte → byte.2 < V.allocation.len ∧
        Embeds (V.allocation.setExtra output.child.tree) output.global.protectedTags
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) V.pointer.grant byte.2 .exclusive) := by
  obtain ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,⟨witness⟩⟩ :=
    correlated_borrow_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange
    (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  obtain ⟨_,afterRuntime,parents,_,nodes,roots,tags,capacity⟩ := prepare_read_selected W runtime frame room exclusive distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change ParentInterpretation accessed.tree W.precise.completion at parents
  change accessed.tree.nodes = W.allocation.extra.nodes at nodes
  change accessed.tree.roots = W.allocation.extra.roots at roots
  change accessed.tree.tagMapping = W.allocation.extra.tagMapping at tags
  change accessed.tree.locations.size = W.allocation.extra.locations.size at capacity
  have retRuntime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global := by rw [allocationEq];exact runtime
  let retCurrent := registered_window V retRuntime frame room
  have registeredRetRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare V.allocation.extra tracker.global frame id room retRuntime).2.2.2.1
  have retByteBound := (V.window (id,targetOffset+targetLength-1) ⟨rfl,by omega,by omega⟩).1
  have retFits : targetOffset+targetLength < 2^64 := by
    have capacityBound := UInt64.toNat_lt V.allocation.byteSize.bytes
    have extent := V.issued.capability.extent
    omega
  let retStart := UInt64.ofNat targetOffset
  have retStartEq : retStart.toNat = targetOffset := by simp only [retStart,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : targetOffset < 2^64)]
  let retAmount := UInt64.ofNat targetLength
  have retAmountEq : retAmount.toNat = targetLength := by simp only [retAmount,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : targetLength < 2^64)]
  have retEndEq : (retStart+retAmount).toNat = targetOffset+targetLength := by
    rw [UInt64.toNat_add,retStartEq,retAmountEq,Nat.mod_eq_of_lt retFits]
  have beforeBool := (default_frame_rule ".CurrentCallExclusiveWindowFrame.window_owned") retCurrent targetExclusive registeredRetRuntime retStart (retStart+retAmount) (by omega) (by omega)
  change GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority V.allocation.extra V.precise.completion registration.1.protectedTags V.pointer.grant)
    retStart (retStart+retAmount) V.allocation.extra.locations at beforeBool
  rw [allocationEq,completionEq] at beforeBool
  have disjoint : ∀ point : UInt64,retStart.toNat ≤ point.toNat → point.toNat < (retStart+retAmount).toNat →
      point.toNat < start.toNat ∨ (start+amount).toNat ≤ point.toNat := by
    intro point lower upper
    by_cases early : point.toNat < start.toNat
    · exact Or.inl early
    · apply Or.inr
      have noWrap : start.toNat+amount.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
      have endEq : (start+amount).toNat = start.toNat+amount.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
      apply Nat.le_of_not_gt
      intro overlap
      exact separate (id,point.toNat) ⟨rfl,by omega,by omega⟩ ⟨rfl,by omega,by omega⟩
  have boolRead := GeneralBorrowRangeOutsideOwned.owned
    (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion registration.1.protectedTags V.pointer.grant)
    W.allocation.extra (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed runtime.formed.well bounds retStart (retStart+retAmount) disjoint beforeBool
  have afterBool : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority accessed.tree W.precise.completion registration.1.protectedTags V.pointer.grant)
      retStart (retStart+retAmount) accessed.tree.locations := by
    intro cursor valid positive beforeUpper afterLower index node present
    exact boolRead cursor valid positive beforeUpper afterLower index node (by rw [←nodes];exact present)
  obtain ⟨parentNode,parentAt,_,binding⟩ := W.binding
  have parentAfter : accessed.tree.nodes.get W.pointer.grant = some parentNode := by rw [nodes];exact parentAt
  obtain ⟨targetNode,targetAt,_,targetBinding⟩ := V.binding
  rw [allocationEq] at targetAt
  have targetAfter : accessed.tree.nodes.get V.pointer.grant = some targetNode := by rw [nodes];exact targetAt
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1 ≤ 4294967295 := by change accessed.tree.nodes.data.size+1 ≤ _;rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have childEq := (default_frame_rule ".CurrentCallExclusiveWindowFrame.child_of_operation") W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
  change output.child=accessed.tree.newChild (Size.ofBytes start) (extra W.pointer.value.provenance) tracker.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true at childEq
  have sourceLookup : (accessed.tree.newChild (Size.ofBytes start)
      (extra W.pointer.value.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag tracker.global.nextPointerTag = some child := by
    rw [←childEq,←tag]
    exact lookup
  have boolAfter : GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags V.pointer.grant)
      retStart (retStart+retAmount) output.child.tree.locations := by
    rw [childEq,global]
    cases provenance : W.pointer.value.provenance with
    | concrete suppliedId parentTag =>
      simp only [extra]
      rw [provenance] at binding
      have tagEq := binding.2
      have tagged : accessed.tree.indexOfTag parentNode.tag = some W.pointer.grant := afterRuntime.formed.allocator.nodeTags _ _ parentAfter
      obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩ := CurrentCallResourceChild.Disjoint.construct accessed.tree registration.1 W.precise.completion afterRuntime parents
        parentNode.tag tracker.global.nextPointerTag W.pointer.grant V.pointer.grant parentNode targetNode tagged parentAfter targetAfter freshAfter childRoom tagBound tagHeld
        start amount retStart (retStart+retAmount) nonzero childBounds disjoint afterBool
      have same : framedChild = child := Option.some.inj (framedLookup.symm.trans (by simpa only [extra,provenance,tagEq] using sourceLookup))
      subst framedChild
      simpa only [accessed,registration,extra,provenance,tagEq] using framed
    | wildcard =>
      simp only [extra]
      obtain ⟨framedChild,framedLookup,framed⟩ := CurrentCallResourceChild.WildcardDisjoint.disjoint accessed.tree registration.1 W.precise.completion afterRuntime parents
        tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld W.pointer.grant parentNode parentAfter
        start amount retStart (retStart+retAmount) nonzero childBounds V.pointer.grant ⟨targetNode,targetAfter⟩ disjoint afterBool
      have same : framedChild = child := Option.some.inj (framedLookup.symm.trans (by simpa only [extra,provenance] using sourceLookup))
      subst framedChild
      simpa only [accessed,registration,extra,provenance] using framed
  have currentBinding : PointerBinds (W.allocation.setExtra output.child.tree) V.pointer := by
    obtain ⟨next,nextAt,nextTag,_,nextExposed,_⟩ := witness.oldNodes V.pointer.grant targetNode targetAt
    refine ⟨next,nextAt,?_,?_⟩
    · exact witness.runtime.formed.allocator.nodeTags _ _ nextAt
    · cases provenance : V.pointer.value.provenance with
      | concrete suppliedId targetTag =>
        rw [provenance] at targetBinding
        simpa only [provenance,nextTag] using targetBinding
      | wildcard =>
        rw [provenance] at targetBinding
        simpa only [provenance,nextExposed] using targetBinding
  refine ⟨output,child,actual,⟨witness⟩,boolAfter,currentBinding,?_⟩
  intro byte inside
  refine ⟨(V.window byte inside).1,?_⟩
  have targetRange := inside.2
  intro segment member lower upper index node present
  simp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper present ⊢
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have rights := boolAfter position valid (by omega) (by omega) (by omega) index node present
  have realized := CandidateCurrentGrantRuntime.realized _ _ (witness.runtime.possible position valid index node present)
    ((witness.runtime.formed.profile position valid).present index node present)
  constructor
  · intro below
    exact (default_frame_rule ".CurrentCallExclusiveWindowFrame.local_token") _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact (default_frame_rule ".CurrentCallExclusiveWindowFrame.foreign_no_clash") _ _ realized (rights.2 outside) clash


end
end DuplicatePrefix.CurrentCallExclusiveWindowFrameSeparate
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallExclusiveWindowFrameSeparate" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved separate-dictionary exclusive frame dependency {dependency}"
