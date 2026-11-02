import empty_function.NoDrawCachedRootTotal
import empty_function.RelocationTypeId
import empty_function.RelocationNodrawTablesStep
import empty_function.RootFramePost
import empty_function.ResourceFailures
import empty_function.ForeignResolverPrelude

/-! Error-aware cached/TypeId root callbacks. Address generation is preserved, even when present without a GenRep witness.
Generator availability,
choice supply, numeric room, and root-tag room are not assumptions. -/
namespace EmptyFunction.NoDrawBasicRootTotal
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
abbrev S := ChoiceExecution.S

def ended (before : S) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) : S :=
  {before with borrowTracker := some {tracker with global},user := {before.user with addresses}}

/-- No-draw root success exposes all current-state invariants needed by the
finite relocation fold. The new root cache/counter are allowed to grow. -/
structure Post (before : WholeCall.State) (tracker : MachineHooks.BorrowState)
    (final : S) where
  global : GlobalState
  world : TreeRuntimeInput.World final {tracker with global}
  frame : RootFramePost.Frame tracker.global global
  memory : final.memory = before.machine.memory
  threads : final.threads = before.machine.threads
  tape : ChoiceExecution.tapeAccess.get final = ChoiceExecution.tapeAccess.get before.machine
  runtime : final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime
  context : RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload
  race : final.dataRace = before.machine.dataRace
  bases : ∀ id row, before.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
    final.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row
  static : AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.machine.user.addresses
  inverse : final.user.addresses.intToPtrMap = before.machine.user.addresses.intToPtrMap
  generation : final.user.addresses.generation = before.machine.user.addresses.generation
  tables : InputDraft.AddressTables {before with machine := final}

private noncomputable def post (before : WholeCall.State) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World before.machine tracker)
    (global : GlobalState) (id : AllocId) (tag : BorTag)
    (tagged : tracker.global.rootPointerTag id = .ok (global,tag))
    (addresses : GlobalAddressState)
    (bases : ∀ id row, before.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
      addresses.baseAddr.find? (fun old => old.allocId == id) = some row)
    (static : AddressStaticPost.view addresses = AddressStaticPost.view before.machine.user.addresses)
    (inverse : addresses.intToPtrMap = before.machine.user.addresses.intToPtrMap)
    (generation : addresses.generation = before.machine.user.addresses.generation)
    (tables : InputDraft.AddressTables {before with machine :=
      {before.machine with user := {before.machine.user with addresses}}}) :
    Post before tracker (ended before.machine tracker global addresses) := by
  have rootFrame := RootFramePost.root tracker.global global id tag tagged
  have rootWorld := RootTagPost.world before.machine (ended before.machine tracker global addresses)
    tracker global id tag world rfl rfl tagged
  refine ⟨global,rootWorld,rootFrame,rfl,rfl,rfl,rfl,rfl,rfl,bases,static,inverse,generation,?_⟩
  exact AddressTransport.tables {before with machine := {before.machine with user := {before.machine.user with addresses}}}
    {before with machine := ended before.machine tracker global addresses} rfl rfl tables

/-- Actual address assignment on the zero-draw branches. A cached base takes
precedence; TypeId caches zero only after the actual root tag has been obtained. -/
private theorem address (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (world : TreeRuntimeInput.World before.machine tracker)
    (tables : InputDraft.AddressTables before)
    (id : AllocId) (tag : BorTag) (tagged : tracker.global.rootPointerTag id = .ok (global,tag))
    (classification : (∃ base,before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) ∨
      ∃ info,before.machine.memory.getAllocInfo id = .ok info ∧ info.kind = .typeId ∧
        before.machine.memory.isAllocLive id = true) :
    ∃ base final, MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks id (some .other)
      {before.machine with borrowTracker := some {tracker with global}} = .ok base final ∧
      Nonempty (Post before tracker final) := by
  have cachedCase : ∀ base,
      before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ →
      ∃ base final, MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks id (some .other)
        {before.machine with borrowTracker := some {tracker with global}} = .ok base final ∧
        Nonempty (Post before tracker final) := by
    intro base cached
    refine ⟨base,ended before.machine tracker global before.machine.user.addresses,?_,?_⟩
    · simp [MachineAddress.addrFromAllocId,cached,ended,
        get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    · exact ⟨post before tracker world global id tag tagged _ (by intro _ _ found;exact found)
        rfl rfl rfl tables⟩
  rcases classification with ⟨base,cached⟩ | ⟨info,metadata,kind,live⟩
  · exact cachedCase base cached
  · cases cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
    | some row =>
      have identity : row.allocId = id := by simpa only [beq_iff_eq] using Array.find?_some cached
      have same : row = ⟨id,row.address⟩ := by cases row; simp_all
      rw [same] at cached
      exact cachedCase _ cached
    | none =>
      let addresses := {before.machine.user.addresses with baseAddr := before.machine.user.addresses.baseAddr.push ⟨id,0⟩}
      have assigned := RelocationTypeId.address hooks
        {before.machine with borrowTracker := some {tracker with global}} id info cached metadata kind live
      refine ⟨0,ended before.machine tracker global addresses,assigned,?_⟩
      refine ⟨?_⟩
      apply post before tracker world global id tag tagged addresses
      · intro other row found
        simp only [addresses,Array.find?_push,found,Option.or]
      · rfl
      · rfl
      · rfl
      · have cachedTables := AddressPost.cache_zero_tables before tables id cached
        apply AddressTransport.tables (AddressPost.withAddresses before (before.machine.user.addresses.cacheAddress id 0).state)
          {before with machine := {before.machine with user := {before.machine.user with addresses}}} rfl ?_ cachedTables
        rw [AddressPost.cache_zero _ _ cached]
        rfl

abbrev normal_tag_error := @EmptyFunction.NoDrawCachedRootTotal.normal_tag_error

/-- Normal cached/TypeId root callbacks, including root-cache hits at MAX and
missing roots at MAX. Every stopped state is the actual source stopped state. -/
theorem normal (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World before.machine tracker)
    (tables : InputDraft.AddressTables before)
    (provenance : CtfeProvenance) (offset : UInt64)
    (admission : RawRootAdmission.Normal before.machine.memory provenance.allocId)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (classification : (∃ base,before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩) ∨
      ∃ info,before.machine.memory.getAllocInfo provenance.allocId = .ok info ∧ info.kind = .typeId ∧
        before.machine.memory.isAllocLive provenance.allocId = true) :
    (∃ pointer final, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .ok pointer final ∧
      Nonempty (Post before tracker final)) ∨
    (∃ error failed, PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .error error failed ∧
      RunLoop.reportsUB error = false) := by
  cases tagged : tracker.global.rootPointerTag provenance.allocId with
  | error error =>
    exact Or.inr ⟨_,before.machine,normal_tag_error before.machine hooks externStatic tracker provenance offset
      admission world.enabled error tagged,rfl⟩
  | ok value =>
    obtain ⟨global,tag⟩ := value
    obtain ⟨base,final,assigned,post⟩ := address before hooks tracker global world tables
      provenance.allocId tag tagged classification
    exact Or.inl ⟨_,final,RawRootAdmission.root_address ChoiceExecution.tapeAccess hooks externStatic before.machine
      tracker provenance offset base tag global final admission world.enabled tagged assigned width,post⟩

abbrev static_tag_error := @EmptyFunction.NoDrawCachedRootTotal.static_tag_error

abbrev static_tag_ok := @EmptyFunction.NoDrawCachedRootTotal.static_tag_ok

/-- Actual extern-export backing root, with no CTFE provenance bound on its
runtime allocation ID. Shim/weak declarations do not call this operation. -/
theorem static_root (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World before.machine tracker)
    (tables : InputDraft.AddressTables before)
    (id : AllocId)
    (classification : (∃ base,before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) ∨
      ∃ info,before.machine.memory.getAllocInfo id = .ok info ∧ info.kind = .typeId ∧
        before.machine.memory.isAllocLive id = true) :
    (∃ pointer final, ForeignResolverPrelude.root hooks id before.machine = .ok pointer final ∧
      Nonempty (Post before tracker final)) ∨
    (∃ error failed, ForeignResolverPrelude.root hooks id before.machine = .error error failed ∧
      RunLoop.reportsUB error = false) := by
  cases tagged : tracker.global.rootPointerTag id with
  | error error =>
    exact Or.inr ⟨_,before.machine,static_tag_error before.machine hooks tracker id world.enabled error tagged,rfl⟩
  | ok value =>
    obtain ⟨global,tag⟩ := value
    obtain ⟨base,final,assigned,post⟩ := address before hooks tracker global world tables id tag tagged classification
    exact Or.inl ⟨_,final,static_tag_ok before.machine hooks tracker id world.enabled global tag tagged base final assigned,post⟩

abbrev normal_address_error := @EmptyFunction.NoDrawCachedRootTotal.normal_address_error

abbrev static_address_error := @EmptyFunction.NoDrawCachedRootTotal.static_address_error

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.NoDrawBasicRootTotal.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved no-draw root axiom {dependency} in {name}"
  logInfo m!"Audited {count} no-draw root declarations"
end EmptyFunction.NoDrawBasicRootTotal
