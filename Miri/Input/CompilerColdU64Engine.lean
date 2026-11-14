import Miri.Input.CompilerInitialAllocationStore
import Miri.Input.CompilerColdU64Source
import Miri.Input.CompilerColdU64Machine
import Miri.Input.CompilerColdU64RootFinish
import Miri.Input.CompilerInitialAllocationBytes
import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalCompilerMachine
import Miri.Input.EvalTerminatorMachine

/-! Bounded u64 leaf CTFE engine using the existing fixed Step and RootFinish.
No scalar callback or compiler answer is an execution input. Every returned
StepResult successor is retained; an error blocks this run rather than dropping
consumed memory/type effects and allowing a fresh retry. -/
namespace Miri.Input.CompilerColdU64Engine
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private abbrev Host := Input.HostRuntime.Storage Unit Unit Unit Unit Unit String Unit Unit
private abbrev World := Input.EvalWorld.World Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev CoreUser := Input.EvalCoreMachine.User Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev InnerState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Inner World)
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer World)
private abbrev CoreOptions := Input.EvalConfigurationCore.Options
private abbrev CoreLeaves := Input.EvalConfigurationCore.Leaves
  Unit Unit Unit Unit Unit String Unit Unit Host Unit Unit

private def options : CoreOptions := {
  place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
  limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
  compatibilityBudget := 128, varArgsBudget := 128, callbackCapacity := 128
  floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
  userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := true
  retag := {implicitWrites := false, preciseInteriorMut := true} }

private def unknownSync : Unit → Concurrency.SyncObject.AccessKind →
    PlaceMachine.MachineM MiriMemoryKind CoreUser Unit :=
  fun _ _ => fun machine => .error (.unsupported "sync payload access unavailable in bounded CTFE engine") machine

private def leaves (dummy : SpanRef) : CoreLeaves := {
  pointerSource := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := none

  }
  sync := unknownSync
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreign := none
  constQueries := .unavailable
  dynSymName := fun _ => ""
  checkLlvmSymbolClash := fun _ => throw (.unsupported "LLVM symbol registry unavailable in bounded CTFE engine")
  math := none
  mathError := .none
  control := Input.EvalTerminatorMachine.controlAccess
  blockingSources := Input.EvalTerminatorMachine.ioSourcesAccess }

private def rootCall (p : CompilerProviders.Prepared) (source : CompilerColdU64Source.Registered)
    (config : ExecutionMachine.Config MiriMemoryKind CoreUser Unit String ABI.ExternAbi Unit)
    (state : InnerState) : StepResult InnerState (RuntimeStackPlace Provenance) :=
  MachineHooks.run (do
    CompilerColdU64Machine.verify source EvalProjectionMachine.arrays
    let some returnTy := source.body.body.locals[0]?
      | throw (.invalidProgram "CTFE root has no return local")
    let returnLayout ← RuntimeArrayQueries.perform EvalProjectionMachine.arrays
      (RuntimeMetadata.layoutInWorld p.runtime returnTy)
    let hooks := ExecutionMachine.callHooks config options.limits
    let destination ← hooks.allocateStack () returnLayout
    unless source.body.body.argumentCount == 0 do
      throw (.invalidProgram "actual CTFE root must have zero arguments")
    hooks.pushRaw () source.callee source.body (.memory destination) (.stop false)
    hooks.pushDone ()
    pure (.memory destination)) state

structure Result where
  value : UInt64
  root : AllocId
  type : TyId
  pcs : Array (Nat × Nat)
  valtree : Miri.MIR.ValTree

structure Attempt where
  outcome : Except String Result
  allocations : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
  types : RuntimeArrayTypes.World
  blocked : Bool

private def failBefore (world : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (types : RuntimeArrayTypes.World) (message : String) : Attempt :=
  ⟨.error message,world,types,true⟩

private def failAfter (world : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (state : InnerState) (message : String) : Attempt :=
  let store := (EvalWorld.initialCompilerStoreInnerAccess.getStore state.machine.user).getD world.store
  ⟨.error message,store.withMemory state.machine.memory,EvalProjectionMachine.arrays.get state,true⟩

def run (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (currentTypes : RuntimeArrayTypes.World) (sourceCtx : CompilerColdU64Source.Registered)
    (cold : CompilerColdU64Source.ColdBoundary) (requested : CtfeQueryBridge.QueryKey)
    (allocationWorld : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) :
    Attempt := Id.run do
  let allocationWorld := allocationWorld.store.withMemory allocationWorld.memory
  let fail := failBefore allocationWorld currentTypes
  unless requested == sourceCtx.allocationKey do
    return fail "u64 cold leaf requested family/PA key differs from actual source body"

  -- The shared counter is used, but this first cold-leaf comparison remains
  -- pre-runtime: preserving active parent-machine borrow/address state has a
  -- separate admission obligation. No live allocation is discarded.
  unless allocationWorld.memory.live.isEmpty do
    return fail "CTFE engine scope unsupported: runtime live allocations already exist"
  unless sourceCtx.source.sourceRole == .ctfe && sourceCtx.environment.mode == .postAnalysis &&
      sourceCtx.environment.paramEnv.callerBounds.isEmpty &&
      sourceCtx.body.body.phase == .Runtime .PostCleanup && sourceCtx.body.body.basicBlocks.size == 1 do
    return fail "CTFE engine requires its actual u64-unary-Not CTFE body/phase"
  let some returnTy := sourceCtx.body.body.locals[0]?
    | return fail "CTFE root return local absent"
  let run ← match allocationWorld.runs.toList with
    | [(run,_)] => pure run
    | _ => return fail "CTFE engine requires exactly one initial compiler run"
  unless allocationWorld.memory.activeInitialCompilerRun == some run && !allocationWorld.memory.sourceAllocIdWorldActive do
    return fail "cold u64 leaf requires the actual active complete source-counter run"
  let currentSource := allocationWorld.store.withMemory allocationWorld.memory
  unless cold.definition == sourceCtx.definition &&
      currentSource.runs.any (fun row => row.1 == run && row.2 == cold.next) &&
      currentSource.memory.globals.size == cold.globalCount &&
      (currentSource.typedDedup.filter (fun row => row.run == run)).size == cold.dedupCount do
    return fail "cold u64 selected PA allocation boundary is not this current source world"
  let dummy ← match CompilerContextSpan.rootSpan compiler.program with
    | .ok span => pure span
    | .error error => return fail error
  let arch ← match EvalArchitectureMachine.targetArch compiler.intrinsics with
    | .ok arch => pure arch
    | .error error => return fail error
  let targetBits := compiler.runtime.target.base.pointerWidth.bits.toNat
  unless compiler.program.input.producer.targetTriple == "x86_64-unknown-linux-gnu" && arch == "x86_64" && targetBits == 64 && compiler.runtime.target.base.endian == .little do
    return fail "CTFE engine target scope unsupported: requires x86_64 little-endian 64-bit"
  let geometry ← match InitialMachine.geometry targetBits arch false none with
    | .ok geometry => pure geometry
    | .error error => return fail (reprStr error)
  let host : Host := {
    blocking := ⟨none,#[]⟩,clock := .virtual 0,deadlines := .empty,readiness := {},futex := {},sync := {},io := {},events := #[]
    virtualSockets := #[],tcpSockets := #[],nativeLibraries := #[],profiler := none
    control := TerminatorControl.initial ⟨0,0x3f847ae147ae147b,true⟩ }
  let machineConfig : InitialMachine.Configuration Unit Unit := {
    geometry,dummySpan := dummy,provenance := .default,addressMode := .managed
    addressStop := 18446744073709551615,addressReuse := ⟨0.5,0.1⟩
    fixedScheduling := false,trackOutdatedLoads := false,weakMemory := true
    backend := .vclocks,trackedTags := some #[],validation := .Shallow
    alignment := .Int,affinity := none,muteOutput := true,hostUsizeBits := 64 }
  let byteView ← match CompilerInitialAllocation.Bytes.prepare compiler.program compiler.runtime run allocationWorld with
    | .ok bytes => pure bytes
    | .error error => return fail error
  -- InitialMachine.create performs no allocation reservation and returns the
  -- supplied memory/types unchanged; a constructor error has no lost prefix.
  let initial : OuterState ← match InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
      (H := Unit) (D := Unit) (O := String) (Aff := Unit) (B := Unit)
      machineConfig allocationWorld.memory currentTypes
      {inputs := Array.replicate 128 (.index .addressSlack 0),cursor := 0} host with
    | .ok initial => pure initial
    | .error error => return fail (reprStr error)
  let installedUser := EvalWorld.initialCompilerStoreAccess.setStore allocationWorld.store initial.machine.user
  let initial := {initial with machine := {initial.machine with user := installedUser}}
  let inner := ExecutionStateTransport.inward initial
  match EvalConfigurationCore.make compiler image byteView options (leaves dummy) () 256 with
  | .error error => return failAfter allocationWorld inner (reprStr error)
  | .ok baseConfig => do
    let config : ExecutionMachine.Config MiriMemoryKind CoreUser Unit String ABI.ExternAbi Unit :=
      CompilerColdU64Machine.specialize sourceCtx EvalProjectionMachine.arrays compiler.runtime baseConfig
    let (entered,returnResult) := rootCall compiler sourceCtx config inner
    let returnPlace ← match returnResult with
      | .ok place => pure place
      | .error error => return failAfter allocationWorld entered (reprStr error)
    unless returnPlace.layout.ty == returnTy do
      return failAfter allocationWorld entered "CTFE return place lost its actual type identity"
    let mut current := entered
    let mut pcs : Array (Nat × Nat) := #[]
    let some block := sourceCtx.body.body.basicBlocks[0]?
      | return failAfter allocationWorld current "CTFE block absent"
    for _ in [:block.statements.size + 1] do
      let some frame := current.stack.currentFrame? | break
      let .mir location := frame.location
        | return failAfter allocationWorld current "CTFE frame remained in preamble/unwind"
      pcs := pcs.push (location.block,location.statementIndex)
      let (next,outcome) := CompilerColdU64Machine.step sourceCtx EvalProjectionMachine.arrays config options.limits () current
      current := next
      match outcome with
      | .error error => return failAfter allocationWorld current (reprStr error)
      | .ok false => return failAfter allocationWorld current "nonterminal CTFE step returned false"
      | .ok true => pure ()
    unless current.stack.frames.isEmpty do
      return failAfter allocationWorld current "CTFE u64 leaf source exhausted its actual statement/return bound"
    let (terminal,outcome) := CompilerColdU64Machine.step sourceCtx EvalProjectionMachine.arrays config options.limits () current
    current := terminal
    match outcome with
    | .error error => return failAfter allocationWorld current (reprStr error)
    | .ok true => return failAfter allocationWorld current "empty CTFE stack fabricated an event"
    | .ok false => pure ()
    let .memory allocatedPlace := returnPlace
      | return failAfter allocationWorld current "u64 root has no actual allocated return place"
    let resolution := config.access.resolvePointer current.machine.memory allocatedPlace.mplace.ptr 0 current.machine
    let resolved ← match resolution with
      | .error error machine =>
        return failAfter allocationWorld {current with machine} (reprStr error)
      | .ok value machine =>
        current := {current with machine}
        match value with
        | .error address => return failAfter allocationWorld current s!"u64 return pointer has no allocation: {address}"
        | .ok resolved => pure resolved
    let types := EvalProjectionMachine.arrays.get current
    let root ← match CompilerColdU64RootFinish.capture types.arena returnPlace resolved current.machine.memory with
      | .ok root => pure root
      | .error error => return failAfter allocationWorld current error
    let store := (EvalWorld.initialCompilerStoreInnerAccess.getStore current.machine.user).getD allocationWorld.store
    let beforeFinish := store.withMemory allocationWorld.memory
    let (value,world) := CompilerColdU64RootFinish.finishShared
      compiler.runtime.target.base run root beforeFinish current.machine.memory
    match value with
    | .error error => return ⟨.error error,world,types,true⟩
    | .ok value =>
      match CompilerColdU64RootFinish.readValTree compiler.runtime.target.base root world.memory with
      | .error error => return ⟨.error error,world,types,true⟩
      | .ok (actualType,tree) =>
        unless actualType == returnTy do return ⟨.error "u64 allocated ValTree type mismatch",world,types,true⟩
        return ⟨.ok ⟨value,root.id,returnTy,pcs,tree⟩,world,types,false⟩

end Miri.Input.CompilerColdU64Engine
