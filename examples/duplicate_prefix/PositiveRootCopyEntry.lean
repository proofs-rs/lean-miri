import duplicate_prefix.PositiveRootSuccessProfile
import duplicate_prefix.CopyRootEntry

namespace DuplicatePrefix.PositiveRootCopyEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

/-- Construct the actual copy-call input from the preceding successful root
trace's data invariants. No interpreter operation's success is an input. -/
noncomputable def input
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial caller : CompilerFrameContext.ActualFrame)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer destination : Scalar Provenance) (count : UInt64)
    (shape : PositiveRootSuccessProfile.FrameShape initial caller pointer destination count)
    (tracker : MachineHooks.BorrowState) (thread : ThreadRecord) (tags : Fin 6 → BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity offset len : UInt64)
    (post : PositiveRootSuccessProfile.MachineShape options remaining span before machine tracker thread tags id entry capacity offset len)
    (debug : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (body : initial.body = RootBody.reflected.body.body)
    (identity : initial.bodyIdentity = RootBody.reflected.body.identity)
    (callee : initial.functionInstance = RootBody.reflected.functionInstance)
    (trackNone : initial.trackCallerArg = none)
    (noClocks : initial.extra.dataRace = none)
    (relevant : initial.extra.userRelevance > 0)
    (top : thread.topUserRelevantFrame = some 0)
    (backend : before.user.payload.payload.user.backend = .none) :
    CopyRootEntry.Input options limits remaining span #[] caller machine pointer destination count := by
  have bound (i : Nat) (small : i < 25) : i < caller.locals.size := by
    rw [shape.size]
    exact small
  have cell {i : Nat} (valid : i < caller.locals.size) {row : LocalState Provenance LocalLayout}
      (known : caller.locals[i]? = some row) : caller.locals[i]'valid = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have row18 := cell (bound 18 (by decide)) shape.slot18
  have row19 := cell (bound 19 (by decide)) shape.slot19
  have row21 := cell (bound 21 (by decide)) shape.slot21
  have row24 := cell (bound 24 (by decide)) shape.slot24
  exact {
    debug := debug,tracker := tracker,tracked := post.tracked
    valid := bound 18 (by decide),old := .uninit
    live := congrArg (fun row => row.value) row18
    uncached := congrArg (fun row => row.layout) row18
    noClocks := (congrArg (fun extra => extra.dataRace) shape.extra).trans noClocks
    noRace := post.race,body := shape.body.trans body
    identity := shape.identity.trans identity,callee := shape.callee.trans callee
    trackNone := shape.trackedCaller.trans trackNone
    location := shape.location,fuel := fuel,validationFuel := validationFuel
    ghost := post.ghost,shallow := post.shallow,thread := thread,active := post.active
    top := top,relevant := by rw [shape.extra]; exact relevant
    budget := budget,budgetEq := budgetEq,backend := post.backend.trans backend
    unchecked := post.unchecked,noGc := post.noGc,fixed := post.fixed,source := source,cmp := cmp
    valid19 := bound 19 (by decide),valid21 := bound 21 (by decide),valid24 := bound 24 (by decide)
    live19 := congrArg (fun row => row.value) row19,cache19 := congrArg (fun row => row.layout) row19
    live21 := congrArg (fun row => row.value) row21,cache21 := congrArg (fun row => row.layout) row21
    live24 := congrArg (fun row => row.value) row24,cache24 := congrArg (fun row => row.layout) row24 }

end DuplicatePrefix.PositiveRootCopyEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PositiveRootCopyEntry.input) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved accepted copy-entry input dependency {dependency}"
