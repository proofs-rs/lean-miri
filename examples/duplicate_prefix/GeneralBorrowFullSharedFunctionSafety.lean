import duplicate_prefix.GeneralBorrowFullSharedCaller
import duplicate_prefix.GenericFunctionPoolSafety
namespace DuplicatePrefix.GeneralBorrowFullSharedFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext GeneralBorrowFreshMetadataChildShared GeneralBorrowFullSharedResources
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

set_option autoImplicit false in
/-- A generated actual borrow history, retaining its derived call resources. -/
structure Generated (seed : Input) (tags : List BorTag) (reserve : Fin 5 → BorTag) where
  input : Input
  location : LocationTree
  history : GeneralBorrowFullSharedRepeat.Run seed tags input
  resources : Resources input location reserve

/-- Choose the actual allocation/generation result from the kernel-checked
construction. All graph, ownership, allocator, freshness and Clean facts are
constructed internally; the choice axiom does not supply any safety premise. -/
def generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (reserve : Fin 5 → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) :
    Generated (GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different) tags reserve := by
  let formed := GeneralBorrowFullSharedResources.generate capacity nonzero rootTag childTag different tags unique
    rootUnused childUnused reserve reserved room
  let final := Classical.choose formed
  let location := Classical.choose (Classical.choose_spec formed)
  have facts := Classical.choose_spec (Classical.choose_spec formed)
  exact ⟨final,location,facts.1,facts.2.1⟩

/-- The generated caller slice retains the arbitrary input allocation length. -/
theorem generated_length (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (unique : tags.Nodup)
    (rootUnused : rootTag ∉ tags) (childUnused : childTag ∉ tags) (reserve : Fin 5 → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) :
    (generated capacity nonzero rootTag childTag different tags unique rootUnused childUnused reserve reserved room).input.len = capacity :=
  (generated capacity nonzero rootTag childTag different tags unique rootUnused childUnused reserve reserved room).history.length

/-- Every UInt64 count executes the genuine duplicate_prefix call to physical
return without UB after actual allocation and finite shared generation.
Scope: arbitrary positive slice length, single-root, unprotected, full-slice
shared append-only histories. Tag supply,
UInt32 headroom, physical caller/storage, runtime/fuel and compiler metadata are
explicit. No initial graph/ownership/allocator/Data, successful operation,
intermediate Plan or trace is an input premise. Counts satisfying 0 < count ≤ len/2 include the actual copying path. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (reserve : Fin 5 → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295)
    (s : GeneralBorrowFullSharedCaller.Caller
      (generated capacity nonzero rootTag childTag different tags unique rootUnused childUnused reserve reserved room).input reserve)
    (count : UInt64) :
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  let result := generated capacity nonzero rootTag childTag different tags unique rootUnused childUnused reserve reserved room
  exact GenericFunctionPoolSafety.invoke
    (GeneralBorrowFullSharedCaller.pool result.input result.location reserve result.resources s) count
end
end DuplicatePrefix.GeneralBorrowFullSharedFunctionSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedFunctionSafety.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved allocated function safety dependency {dependency}"
