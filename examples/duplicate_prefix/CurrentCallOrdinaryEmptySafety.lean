import duplicate_prefix.CurrentCallOrdinaryEmptyLive
import duplicate_prefix.CurrentCallOrdinaryEmptyNonlive
import duplicate_prefix.CurrentCallOrdinaryEmptyUnlocated
import duplicate_prefix.CurrentCallOrdinaryEmptyLiveCurrent
import duplicate_prefix.CurrentCallOrdinaryEmptyNonliveCurrent
import duplicate_prefix.CurrentCallOrdinaryEmptyUnlocatedCurrent
import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentSafety
import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentData

/-! Exhaustive adopted empty-source dispatch. The actual source classifier
keeps integer, MISS, LIVE, metadata-backed absent, and CURRENT cases distinct;
each branch consumes its derived operational endpoint and returns the original
all-count Result. There is no producer-factory premise. -/
namespace DuplicatePrefix.CurrentCallOrdinaryEmptySafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CurrentCallEmptyClassification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem source_physical {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place) :
    EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer argument) := by
  rcases input.source with zero | positive
  · exact zero.2.1
  · exact False.elim (positive.1 rfl)

private theorem pointer_literal (pointer : Pointer Provenance) (provenance : Provenance)
    (kind : pointer.provenance = provenance) : pointer = Pointer.new provenance pointer.offset := by
  cases pointer
  simp_all [Pointer.new]

private theorem return_present {before tracker family offset capacity}
    (live : LiveRole before tracker family offset 1 capacity false) :
    ∃ entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row => row.1 == family.allocation) = some (family.allocation, entry) := by
  obtain ⟨entry, found, _⟩ := live
  exact ⟨entry, found⟩

private def reindex {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    {nextArgument} (equal : argument=nextArgument) :
    OrdinaryInput options limits remaining span before nextArgument 0 place := equal ▸ input

private theorem reindex_tracker {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    {nextArgument} (equal : argument=nextArgument) : (reindex input equal).tracker=input.tracker := by
  cases equal
  rfl

/-- Empty slices require no source content family. Every initial classifier
alternative and both return backing alternatives reach the original Result. -/
theorem invoke {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (empty : len = 0) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  cases empty
  cases CurrentCallEmptyClassification.classify (source_physical input) with
  | integer address encoding nonnull =>
    cases encoding
    rcases input.returnBacking with live | latent
    · exact CurrentCallOrdinaryEmptyUnlocated.integer address count input (return_present live)
    · exact CurrentCallOrdinaryEmptyUnlocatedCurrent.integer address count input latent
  | concrete pointer encoding id tag provenance nonnull base cached target =>
    cases target with
    | live entry live parent =>
      have argumentEq := encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer
        (pointer_literal pointer (.concrete id tag) provenance))
      cases argumentEq
      rcases input.returnBacking with liveReturn | latentReturn
      · exact CurrentCallOrdinaryEmptyLive.concrete id tag pointer.offset.bytes count input entry live parent (return_present liveReturn)
      · exact CurrentCallOrdinaryEmptyLiveCurrent.concrete id tag pointer.offset.bytes count input entry live parent latentReturn
    | nonlive metadata absent =>
      have argumentEq := encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer
        (pointer_literal pointer (.concrete id tag) provenance))
      cases argumentEq
      rcases input.returnBacking with liveReturn | latentReturn
      · exact CurrentCallOrdinaryEmptyNonlive.concrete id tag pointer.offset.bytes count input metadata absent (return_present liveReturn)
      · exact CurrentCallOrdinaryEmptyNonliveCurrent.concrete id tag pointer.offset.bytes count input metadata absent latentReturn
    | current absent noFunction noVaList registry source root current storage compiler rootCached compatible =>
      obtain ⟨actualBase, offset, argumentEq, payload, missing, noFn, noVa, vacant, rootHit, baseHit, nonzero, _, _⟩ :=
        CurrentCallOrdinaryEmptyCurrentData.concrete input rfl pointer encoding id tag provenance source root
          absent noFunction noVaList registry current storage compiler rootCached compatible
      cases argumentEq
      exact CurrentCallOrdinaryEmptyCurrentSafety.concrete_raw id root actualBase offset input source payload missing noFn noVa vacant rootHit baseHit nonzero count
  | miss pointer encoding provenance nonnull nonstrict query =>
    have argumentEq := encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer
      (pointer_literal pointer .wildcard provenance))
    cases argumentEq
    rcases input.returnBacking with liveReturn | latentReturn
    · exact CurrentCallOrdinaryEmptyUnlocated.miss pointer.offset.bytes count input query (return_present liveReturn)
    · exact CurrentCallOrdinaryEmptyUnlocatedCurrent.miss pointer.offset.bytes count input latentReturn query
  | hit pointer encoding provenance nonnull nonstrict hit =>
    cases targetEq : hit.target with
    | live entry live parent =>
      have argumentEq := encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer
        (pointer_literal pointer .wildcard provenance))
      cases argumentEq
      rcases input.returnBacking with liveReturn | latentReturn
      · exact CurrentCallOrdinaryEmptyLive.wildcard pointer.offset.bytes count input hit entry live (return_present liveReturn)
      · exact CurrentCallOrdinaryEmptyLiveCurrent.wildcard pointer.offset.bytes count input hit entry live latentReturn
    | nonlive metadata absent =>
      have argumentEq := encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer
        (pointer_literal pointer .wildcard provenance))
      cases argumentEq
      rcases input.returnBacking with liveReturn | latentReturn
      · exact CurrentCallOrdinaryEmptyNonlive.wildcard pointer.offset.bytes count input hit metadata absent (return_present liveReturn)
      · exact CurrentCallOrdinaryEmptyNonliveCurrent.wildcard pointer.offset.bytes count input hit metadata absent latentReturn
    | current absent noFunction noVaList registry source root current storage compiler rootCached compatible =>
      obtain ⟨offset, argumentEq, payload, missing, noFn, noVa, vacant, rootHit, baseHit, nonzero, _, _, geometry, exposed⟩ :=
        CurrentCallOrdinaryEmptyCurrentData.wildcard input rfl pointer encoding provenance hit source root
          absent noFunction noVaList registry current storage compiler rootCached
      let normalized:=reindex input argumentEq
      have rootHit' : normalized.tracker.global.rootTag? hit.id=some root := by
        rw [show normalized.tracker=input.tracker from reindex_tracker input argumentEq]
        exact rootHit
      have done:=CurrentCallOrdinaryEmptyCurrentSafety.wildcard_raw hit.id root hit.base offset normalized source payload missing noFn noVa vacant rootHit' baseHit nonzero geometry exposed count
      exact Eq.mp (congrArg (fun value => DuplicatePrefixArgumentCallResult.Result options limits remaining span before value 0 count place) argumentEq.symm) done

end DuplicatePrefix.CurrentCallOrdinaryEmptySafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptySafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved exhaustive empty Result dependency {name}: {dependency}"
