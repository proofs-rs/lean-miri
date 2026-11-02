import duplicate_prefix.CandidateCallBindings

/-! A partial connection for the UNADOPTED ownership candidate: active mutable
contents imply existing raw local Write authority along physical parent paths.
Completed ancestors in other physical components need a separate visitor argument.
No full component/wildcard authority, ordinary coverage or call contract is proved. -/
namespace DuplicatePrefix.CandidateOwnershipAuthority
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCallBindings GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

/-- Existing physical parent edges are retained in the completed forest. -/
theorem physical_path {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {ancestor grant : UniIndex}
    (path : Path tree ancestor grant) : Below completion ancestor grant := by
  induction path with
  | refl node present => exact .refl _
  | step earlier node present edge ih =>
    exact .step ((complete.2.2.2.2.1 _ node present).2.2.1 _ edge) ih

/-- Scalar inclusion transfers the selected local right to the actual raw
state, using the SAME protector bit; no visit/operation result is assumed. -/
theorem local_write {allocation : Allocation Provenance BorrowTree} {held : ProtectedTags}
    {precise : PreciseAllocation} {pointer : PointerInstance} {byte : Nat}
    (refines : Refines allocation held precise)
    (rights : LoanRights allocation held precise pointer byte .mut)
    {segment : Miri.DataStructures.RangeMapSegment LocationTree}
    (stored : segment ∈ allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat ≤ byte) (upper : byte < segment.range.stop.toNat)
    {index : UniIndex} {node : TreeNode} (present : allocation.extra.nodes.get index = some node)
    (path : Path allocation.extra index pointer.grant) :
    OrdinaryBorrowAuthority.LocalWrite (RawState segment.data index node) (held.contains node.tag) := by
  have selected := (rights index node present).1 (physical_path refines.1 path)
  have table := (refines.2.2.2.2 segment stored).2.2.2.2 byte lower upper index node present
  have raw := table.2.2 .Write .LocalAccess selected
  exact raw

private theorem unique_key {α β : Type} (rows : List (α × β))
    (unique : (rows.map Prod.fst).Nodup) {key : α} {first second : β}
    (left : (key, first) ∈ rows) (right : (key, second) ∈ rows) : first = second := by
  induction rows with
  | nil => cases left
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [List.mem_cons] at left right
    rcases left with left | left
    · rcases right with right | right
      · exact (Prod.mk.inj (left.trans right.symm)).2
      · have member : key ∈ tail.map Prod.fst := List.mem_map.mpr ⟨(key, second),right,rfl⟩
        exact False.elim (unique.1 (by simpa only [← congrArg Prod.fst left] using member))
    · rcases right with right | right
      · have member : key ∈ tail.map Prod.fst := List.mem_map.mpr ⟨(key, first),left,rfl⟩
        exact False.elim (unique.1 (by simpa only [← congrArg Prod.fst right] using member))
      · exact ih unique.2 left right

/-- An active mutable byte supplies raw physical-ancestor authority. The grant
and allocation come from the actual finite owner/pointer lookup, not a separately
chosen exposed witness. -/
theorem active_mutable {world : World} {held : ProtectedTags} {interpretation : Interpretation}
    (interprets : Interprets world held interpretation)
    {byte : CandidateFreezeContentResources.Byte} {owner : Nat}
    (charged : interpretation.content byte owner = some ⟨.mut, .active⟩) :
    ∃ loan pointer allocation,
      interpretation.loans[owner]? = some loan ∧
      interpretation.pointers[loan.pointer]? = some pointer ∧ pointer.allocation = byte.1 ∧
      Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
      ∀ segment ∈ allocation.extra.locations.entries.toList,
        segment.range.start.toNat ≤ byte.2 → byte.2 < segment.range.stop.toNat →
        ∀ index node, allocation.extra.nodes.get index = some node →
          Path allocation.extra index pointer.grant →
          OrdinaryBorrowAuthority.LocalWrite (RawState segment.data index node) (held.contains node.tag) := by
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,idEq,live,bound,preciseAt,rights,_⟩ :=
    interprets.2.2.2.2.2.2.2 byte owner _ charged
  obtain ⟨other,otherLive,refines⟩ := interprets.2.2.2.1 _ _ preciseAt
  have equal : allocation = other := unique_key world.toList interprets.1 live otherLive
  subst other
  refine ⟨loan,pointer,allocation,loanAt,pointerAt,idEq,live,bound,?_⟩
  intro segment stored lower upper index node present path
  exact local_write refines (rights rfl) stored lower upper present path

/-- The SAME interpretation used by actual-call bindings supplies the source
argument's physical-ancestor LocalWrite at every owned positive-slice byte.
Empty sources require no grant. This is only the local part of source authority. -/
theorem source_local {before : DuplicatePrefixCallSpecification.Before} {world : World}
    {held : ProtectedTags} {interpretation : Interpretation} {call : CallLoans}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (interprets : Interprets world held interpretation) (claims : Claims interpretation call)
    (bindings : Bindings before world held interpretation call argument len place)
    (nonempty : len ≠ 0) {byte : Nat}
    (lower : call.sourceOffset ≤ byte) (upper : byte < call.sourceOffset + len.toNat) :
    ∃ pointer loan pointerInstance allocation,
      argument = .pointer pointer ∧ interpretation.loans[call.sourceOwner]? = some loan ∧
      interpretation.pointers[loan.pointer]? = some pointerInstance ∧
      pointerInstance.value = pointer ∧ pointerInstance.allocation = call.sourceId ∧
      Present (actualWorld before) call.sourceId allocation ∧ byte < allocation.len ∧
      ∀ segment ∈ allocation.extra.locations.entries.toList,
        segment.range.start.toNat ≤ byte → byte < segment.range.stop.toNat →
        ∀ index node, allocation.extra.nodes.get index = some node →
          Path allocation.extra index pointerInstance.grant →
          OrdinaryBorrowAuthority.LocalWrite (RawState segment.data index node) (held.contains node.tag) := by
  obtain empty | ⟨_,pointer,encoding,loan,pointerInstance,loanAt,pointerAt,valueEq,idEq,_⟩ := bindings.source
  · exact False.elim (nonempty empty.1)
  have window : Window call.sourceId call.sourceOffset call.length (call.sourceId,byte) :=
    ⟨rfl,lower,by change byte < call.sourceOffset + call.length; rw [bindings.length_eq]; exact upper⟩
  have charged := (claims.2.1 (call.sourceId,byte)).2 window
  obtain ⟨actualLoan,actualPointer,allocation,actualLoanAt,actualPointerAt,actualId,live,bound,localRights⟩ :=
    active_mutable interprets charged
  have loanEq : actualLoan = loan := Option.some.inj (actualLoanAt.symm.trans loanAt)
  subst actualLoan
  have pointerEq : actualPointer = pointerInstance := Option.some.inj (actualPointerAt.symm.trans pointerAt)
  subst actualPointer
  exact ⟨pointer,loan,pointerInstance,allocation,encoding,loanAt,pointerAt,valueEq,idEq,
    by simpa only [bindings.world_eq] using live,bound,localRights⟩

end DuplicatePrefix.CandidateOwnershipAuthority
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateOwnershipAuthority." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved candidate authority dependency {dependency}"
