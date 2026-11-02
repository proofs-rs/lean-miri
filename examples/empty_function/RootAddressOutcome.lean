import empty_function.ManagedAddressRepresentation
import empty_function.NoDrawCachedRootTotal
namespace EmptyFunction.RootAddressOutcome
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
abbrev S := ChoiceExecution.S

structure Post (before : WholeCall.State) (tracker : MachineHooks.BorrowState)
    (final : S) where
  global : GlobalState
  world : TreeRuntimeInput.World final {tracker with global}
  frame : RootFramePost.Frame tracker.global global
  memory : final.memory = before.machine.memory
  threads : final.threads = before.machine.threads
  runtime : final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime
  context : RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload
  race : final.dataRace = before.machine.dataRace
  bases : ∀ id row, before.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
    final.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row
  static : AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.machine.user.addresses
  generation : ∃ next, InputDraft.GenerationRepresentation {before with machine := final} next
  tables : InputDraft.AddressTables {before with machine := final}
  addresses : Preservation.ExistingAddressFacts before {before with machine := final}

private theorem rooted_post (before : WholeCall.State) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World before.machine tracker)
    (old : InputDraft.AddressTables before)
    (id : AllocId) (global : GlobalState) (tag : BorTag)
    (tagged : tracker.global.rootPointerTag id = .ok (global,tag)) (final : S)
    (frame : ManagedAddressFrame.FrameEq {before.machine with borrowTracker := some {tracker with global}} final)
    (geometry : ManagedAddressRepresentation.Post
      {before with machine := {before.machine with borrowTracker := some {tracker with global}}} final) :
    Nonempty (Post before tracker final) := by
  obtain ⟨⟨next,current⟩,bases,static⟩ := geometry
  obtain ⟨addresses,tape,equal⟩ := frame
  have memoryEq : final.memory = before.machine.memory := by rw [equal]; rfl
  have trackerEq : final.borrowTracker = some {tracker with global} := by rw [equal]; rfl
  have threadsEq : final.threads = before.machine.threads := by rw [equal]; rfl
  have runtimeEq : final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime := by rw [equal]; rfl
  have contextEq : RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload := by rw [equal]; rfl
  have raceEq : final.dataRace = before.machine.dataRace := by rw [equal]; rfl
  have rootWorld := RootTagPost.world before.machine final tracker global id tag world memoryEq trackerEq tagged
  have rootFrame := RootFramePost.root tracker.global global id tag tagged
  refine ⟨⟨global,rootWorld,rootFrame,memoryEq,threadsEq,runtimeEq,contextEq,raceEq,bases,static,⟨next,current⟩,current.tables,?_⟩⟩
  exact AddressStaticPost.facts before {before with machine := final} old current.tables memoryEq bases static

/-- The real normal-root callback either preserves the complete current
invariants or stops with its real non-UB error and failed state. -/
theorem normal (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World before.machine tracker)
    (generation : AddressGenerationState) (current : InputDraft.GenerationRepresentation before generation)
    (provenance : CtfeProvenance) (offset : UInt64) (target : AllocationInfo)
    (admission : RawRootAdmission.Normal before.machine.memory provenance.allocId)
    (backing : InputDraft.MetadataBacking before provenance.allocId)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok target)
    (live : before.machine.memory.isAllocLive provenance.allocId = true) (notDead : target.kind ≠ .dead)
    (alignment : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none →
      target.kind ≠ .typeId → InputDraft.AlignmentRepresentation target.align)
    (noRace : before.machine.dataRace = none) (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ pointer final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .ok pointer final ∧
      Nonempty (Post before tracker final)) ∨
    (∃ error failed, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .error error failed ∧ RunLoop.reportsUB error = false) := by
  cases tagged : tracker.global.rootPointerTag provenance.allocId with
  | error error =>
    exact .inr ⟨_,before.machine,NoDrawCachedRootTotal.normal_tag_error before.machine hooks externStatic tracker provenance offset
      admission world.enabled error tagged,rfl⟩
  | ok pair =>
    obtain ⟨global,tag⟩ := pair
    let rooted := {before with machine := {before.machine with borrowTracker := some {tracker with global}}}
    have rootedRep := AddressTransport.representation before rooted rfl rfl generation current
    have geo := ManagedAddressRepresentation.address hooks rooted generation rootedRep provenance.allocId target
      (AddressTransport.backing before rooted rfl _ backing) metadata live notDead alignment noRace
    have shape := ManagedAddressFrame.address hooks rooted.machine provenance.allocId (some .other) current.managed noRace classifier
    have safe := ManagedAddressTotal.address hooks rooted.machine provenance.allocId (some .other) current.managed noRace classifier
    cases assigned : MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks provenance.allocId (some .other) rooted.machine with
    | error error failed =>
      simp only [assigned,MachineAddressPartial.NonUBResult] at safe
      exact .inr ⟨error,failed,NoDrawCachedRootTotal.normal_address_error before.machine hooks externStatic tracker provenance offset
        admission world.enabled global tag tagged error failed assigned,safe⟩
    | ok base final =>
      simp only [assigned,ManagedAddressRepresentation.ResultPost] at geo
      simp only [assigned,ManagedAddressFrame.ResultFrame] at shape
      exact .inl ⟨_,final,RawRootAdmission.root_address ChoiceExecution.tapeAccess hooks externStatic before.machine tracker provenance
        offset base tag global final admission world.enabled tagged assigned width,
        rooted_post before tracker world current.tables provenance.allocId global tag tagged final shape geo⟩


/-- The same partial totality for an exported runtime backing ID. This path
has no CTFE-ID bound and no wrapping source offset. -/
theorem static_root (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World before.machine tracker)
    (generation : AddressGenerationState) (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo)
    (backing : InputDraft.MetadataBacking before id)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true) (notDead : target.kind ≠ .dead)
    (alignment : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none →
      target.kind ≠ .typeId → InputDraft.AlignmentRepresentation target.align)
    (noRace : before.machine.dataRace = none)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ pointer final, ForeignResolverPrelude.root hooks id before.machine = .ok pointer final ∧
      Nonempty (Post before tracker final)) ∨
    (∃ error failed, ForeignResolverPrelude.root hooks id before.machine = .error error failed ∧ RunLoop.reportsUB error = false) := by
  cases tagged : tracker.global.rootPointerTag id with
  | error error =>
    exact .inr ⟨_,before.machine,NoDrawCachedRootTotal.static_tag_error before.machine hooks tracker id
      world.enabled error tagged,rfl⟩
  | ok pair =>
    obtain ⟨global,tag⟩ := pair
    let rooted := {before with machine := {before.machine with borrowTracker := some {tracker with global}}}
    have rootedRep := AddressTransport.representation before rooted rfl rfl generation current
    have geo := ManagedAddressRepresentation.address hooks rooted generation rootedRep id target
      (AddressTransport.backing before rooted rfl id backing) metadata live notDead alignment noRace
    have shape := ManagedAddressFrame.address hooks rooted.machine id (some .other) current.managed noRace classifier
    have safe := ManagedAddressTotal.address hooks rooted.machine id (some .other) current.managed noRace classifier
    cases assigned : MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks id (some .other) rooted.machine with
    | error error failed =>
      simp only [assigned,MachineAddressPartial.NonUBResult] at safe
      exact .inr ⟨error,failed,NoDrawCachedRootTotal.static_address_error before.machine hooks tracker id
        world.enabled global tag tagged error failed assigned,safe⟩
    | ok base final =>
      simp only [assigned,ManagedAddressRepresentation.ResultPost] at geo
      simp only [assigned,ManagedAddressFrame.ResultFrame] at shape
      exact .inl ⟨_,final,NoDrawCachedRootTotal.static_tag_ok before.machine hooks tracker id world.enabled global tag tagged base final assigned,
        rooted_post before tracker world current.tables id global tag tagged final shape geo⟩
end EmptyFunction.RootAddressOutcome
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RootAddressOutcome.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root address outcome axiom {dependency} in {name}"
