import duplicate_prefix.CurrentCallResourceFnEntry

namespace DuplicatePrefix.CurrentCallExclusiveWindowFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFnEntryRegistration
open CurrentCallResourceFnEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private def extra (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]

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

private theorem window_owned {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (exclusive : demandOf mode = .exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (lo hi : UInt64) (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      lo hi W.allocation.extra.locations := by
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : W.allocation.extra.locations.entries[position] ∈ W.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  by_cases earlier : lo.toNat ≤ W.allocation.extra.locations.entries[position].range.start.toNat
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,W.allocation.extra.locations.entries[position].range.start.toNat)
      ⟨rfl,by omega,by omega⟩ _ member (Nat.le_refl _) segmentPositive
      (runtime.formed.profile position valid) (runtime.possible position valid)
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,lo.toNat) ⟨rfl,windowLower,by omega⟩ _ member (by omega) afterLower
      (runtime.formed.profile position valid) (runtime.possible position valid)

theorem invoke {before tracker data owner id offset length mode targetOwner targetOffset targetLength targetMode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (V : UniformWindow before tracker data targetOwner id targetOffset targetLength targetMode)
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
  have beforeBool := window_owned retCurrent targetExclusive registeredRetRuntime retStart (retStart+retAmount) (by omega) (by omega)
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
  have childEq := child_of_operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
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
    exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash

/-- The actual Bool Write keeps the current source child's full authority on
its disjoint byte window, regardless of row splitting or operation outcome.
No original-parent authority is restored by this frame. -/
theorem write_outside (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (target : UniIndex) (provenance : ProvenanceExtra) (offset amount : Size)
    (visit : ChildrenVisitMode) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + amount.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.bytes.toNat ∨ (offset.bytes + amount.bytes).toNat ≤ point.toNat)
    (authority : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion held target) lower upper tree.locations) :
    let result := tree.performBorrowAccessRange provenance offset amount .Write held visit
    result.tree = {tree with locations := result.tree.locations} ∧
    GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority result.tree completion held target)
      lower upper result.tree.locations := by
  dsimp only
  have frame := GeneralBorrowFreshReadFrame.frame tree provenance offset amount .Write held visit
  have nodes := congrArg BorrowTree.nodes frame
  have retained := GeneralBorrowRangeOutsideOwned.owned
    (S05CompletedAncestryReadMutable.Authority tree completion held target)
    tree provenance offset amount .Write held visit well bounds lower upper disjoint authority
  refine ⟨frame,?_⟩
  intro position valid positive beforeUpper afterLower index node present
  exact retained position valid positive beforeUpper afterLower index node (by rw [←nodes];exact present)

end
end DuplicatePrefix.CurrentCallExclusiveWindowFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallExclusiveWindowFrame.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved exclusive window frame dependency {dependency}"
