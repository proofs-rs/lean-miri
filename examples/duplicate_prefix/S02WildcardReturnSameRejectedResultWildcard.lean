import duplicate_prefix.S02WildcardSourceWildcardSameInitial
import duplicate_prefix.S02WildcardReturnSameRejectedBody
import duplicate_prefix.S02WildcardPositiveIdUnique
namespace DuplicatePrefix.S02WildcardReturnSameRejectedResultWildcard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The unchanged contract executes the rejected branch and actual Return for
wildcard source and wildcard return in the same resolved allocation. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (rejected : count > len/2) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨reference,output,fresh,available⟩ := S02WildcardSourceWildcardSameInitial.enters address len count input nonempty returnWildcard
  refine ⟨reference,?_⟩
  intro same
  obtain ⟨data,post,actual,nodeReserve,tagReserve⟩ := available same
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker fresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let changed := {(RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted {} reference.id reference.tracker.global.nextPointerTag) count).frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have below := GeneralBorrowForestTagHighWater.mapped data.destination.entry.allocation.extra data.destination.tracker.global.protectedTags
    data.destination.tracker.global.nextPointerTag data.node.tag data.runtime.below data.child
    (data.runtime.formed.allocator.nodeTags data.child data.node data.present)
  have tagDifferent : data.destination.tracker.global.nextPointerTag ≠ reference.tracker.global.nextPointerTag := by
    intro equal
    rw [data.tag,equal] at below
    omega
  have sourceDisjoint : (reference.offset+len).toNat ≤ data.destination.offset.toNat ∨ (data.destination.offset+1).toNat ≤ reference.offset.toNat := by
    rcases data.disjoint with left | right
    · exact Or.inr (Nat.le_trans (by simp only [UInt64.toNat_add];exact Nat.mod_le _ _) left)
    · exact Or.inl right
  have capacity : post.updated.extra.locations.size = post.updated.byteSize := by
    have bounds := post.physical.borrowSize
    have size := post.physical.size
    rw [post.physicalEntry] at bounds size
    exact (congrArg Size.mk bounds).trans size.symm
  have referenceMode : reference.tracker.retagMode = .Default := by
    obtain ⟨tracker,enabled,mode⟩ := input.contract.model.defaultTracker
    have eq : reference.tracker = tracker := Option.some.inj (reference.enabled.symm.trans enabled)
    rw [eq];exact mode
  have trackerEq : data.destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩ :=
    Option.some.inj data.destination.enabled.symm
  have mode : data.destination.tracker.retagMode = .Default := (congrArg MachineHooks.BorrowState.retagMode trackerEq).trans referenceMode
  have addressEq : address = reference.base+reference.offset := reference.pointerAddress
  apply S02WildcardReturnSameRejectedBody.result (Pointer.new .wildcard (Size.ofBytes address)) len count input reference current
    data.destination data.nextFresh changed owned data.child data.child (some reference.tracker.global.nextPointerTag) data.node post rfl data.tag data.hidden
    tagDifferent data.sameId (data.sameId.trans same) sourceDisjoint capacity nodeReserve tagReserve mode rfl rfl rfl
  · simpa only [PositiveRootInstalledFrame.installed,root,adjusted,changed,owned,←addressEq] using actual
  · exact rejected

/-- Allocation uniqueness fixes the original source witness. -/
theorem same_id
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (rejected : count > len/2)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨resolved,run⟩ := result address len count input nonempty returnWildcard rejected
  have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
  exact run (by rw [←unique];exact same)
end
end DuplicatePrefix.S02WildcardReturnSameRejectedResultWildcard
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameRejectedResultWildcard." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved wildcard same rejected Result dependency {dependency}"
