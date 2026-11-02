import empty_function.RootTagPost
import empty_function.RelocationByteFold
import Miri.Interpreter.GlobalAllocationMachine
import Miri.Interpreter.RunLoop
namespace EmptyFunction.GlobalErrorAware
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {K U P : Type}

theorem initExtra_tagged [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (size : Size) (align : Align)
    (tracker : MachineHooks.BorrowState) (global : GlobalState) (root : BorTag)
    (tracked : machine.borrowTracker = some tracker)
    (tagged : tracker.global.rootPointerTag id = .ok (global,root))
    (noRace : machine.dataRace = none)
    (vacant : (extras.get machine.user).allocations.any (fun row => row.1 == id) = false) :
    GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align machine =
      .ok (BorrowTree.new root size)
        (MemoryExtras.putAllocation extras {machine with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩) := by
  have noentry : ¬ ∃ (i : Nat) (h : i < (extras.get machine.user).allocations.size),
      (extras.get machine.user).allocations[i].1=id := by
    simpa only [Array.any_eq_false,beq_iff_eq,not_exists] using vacant
  simp only [GlobalAllocationMachine.initExtra,tracked,tagged,
    bind,EStateM.bind,pure,EStateM.pure,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    noRace,Option.map_none,Option.getD_none]
  simp [MemoryExtras.initAllocation,vacant,MemoryExtras.putAllocation,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,
    set,MonadStateOf.set,EStateM.set,tryCatchThe,tryCatch,MonadExceptOf.tryCatch,EStateM.tryCatch,
    Bind.bind,noentry]

theorem given_tagged_adjust [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (before middle : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (prepare : leaves.bytes.prepare id (RelocationBytePrimitives.snapshot source) source.align =
      pure (RelocationBytePrimitives.snapshot source,none))
    (diagnostic : leaves.diagnostic = fun _ _ _ => pure ())
    (conversion : Allocation.adjustFromTcx source target
      (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
      leaves.globalRootPointer before = .ok converted middle)
    (attributes : RelocationByteFold.Attributes source converted)
    (world : TreeRuntimeInput.World middle tracker)
    (global : GlobalState) (root : BorTag)
    (tagged : tracker.global.rootPointerTag id = .ok (global,root))
    (noRace : middle.dataRace = none)
    (vacant : (extras.get middle.user).allocations.any (fun row => row.1 == id) = false) :
    GlobalAllocationMachine.adjust target extras leaves id source before =
      .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
        (MemoryExtras.putAllocation extras {middle with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩) ∧
    TreeRuntimeInput.World
      (MemoryExtras.putAllocation extras {middle with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩)
      {tracker with global} := by
  have initialized := initExtra_tagged extras middle id source.byteSize source.align tracker global root
    world.enabled tagged noRace vacant
  constructor
  · have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
        .ok (RelocationBytePrimitives.snapshot source) := by
      cases source
      simp [RelocationBytePrimitives.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
        Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]
    simp only [GlobalAllocationMachine.adjust,inspect,prepare,conversion,attributes.size,attributes.align,
      GlobalAllocationMachine.init,diagnostic,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
    simp only [pure,Pure.pure] at initialized
    rw [initialized]
  · exact RootTagPost.world middle _ tracker global id root world rfl rfl tagged

/-- The actual root-tag operation may stop; it requires no spare tag when it
stops. Its successful branch still returns the exact owned tree and World. -/
theorem init_extra [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (size : Size) (align : Align) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World machine tracker) (noRace : machine.dataRace = none)
    (vacant : (extras.get machine.user).allocations.any (fun row => row.1 == id) = false) :
    (∃ global root, tracker.global.rootPointerTag id = .ok (global,root) ∧
      GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align machine =
        .ok (BorrowTree.new root size)
          (MemoryExtras.putAllocation extras {machine with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩) ∧
      TreeRuntimeInput.World
        (MemoryExtras.putAllocation extras {machine with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩)
        {tracker with global}) ∨
    (∃ error final, GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align machine =
      .error error final ∧ RunLoop.reportsUB error = false) := by
  cases tagged : tracker.global.rootPointerTag id with
  | error error =>
    right
    refine ⟨.resourceExhaustion s!"global allocation root tag: {reprStr error}",machine,?_,rfl⟩
    simp [GlobalAllocationMachine.initExtra,world.enabled,tagged,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      get,getThe,MonadStateOf.get,EStateM.get,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  | ok value =>
    obtain ⟨global,root⟩ := value
    exact Or.inl ⟨global,root,rfl,
      initExtra_tagged extras machine id size align tracker global root world.enabled tagged noRace vacant,
      RootTagPost.world machine _ tracker global id root world rfl rfl tagged⟩

/-- Exact restoration of a typed error after the legacy string boundary.
The error state's pendingError takes precedence over fallback classification. -/
theorem ensure_pending [DecidableEq K]
    (kind : K) (hooks : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (id : AllocId) (before : MachineHooks.State K U)
    (memory : MemoryState Provenance BorrowTree K) (state : PlaceMachine.AccessState K U)
    (error : MemoryAccessError) (typed : StepError)
    (raw : MemoryLifecycle.getAllocRaw before.machine.memory ⟨before.machine,none⟩ id (some kind) hooks =
      ⟨memory,state,.error error⟩) (pending : state.pendingError = some typed) :
    GlobalAllocationMachine.ensure kind hooks id before =
      .error typed {before with machine := {state.machine with memory}} := by
  simp [GlobalAllocationMachine.ensure,raw,pending,
    get,getThe,MonadStateOf.get,EStateM.get,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

/-- Untyped getAllocRaw failures are callback stops, rather than UB reports.
This theorem does not erase a pending typed error. -/
theorem ensure_untyped [DecidableEq K]
    (kind : K) (hooks : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (id : AllocId) (before : MachineHooks.State K U)
    (memory : MemoryState Provenance BorrowTree K) (state : PlaceMachine.AccessState K U)
    (error : MemoryAccessError)
    (raw : MemoryLifecycle.getAllocRaw before.machine.memory ⟨before.machine,none⟩ id (some kind) hooks =
      ⟨memory,state,.error error⟩) (pending : state.pendingError = none) :
    ∃ typed final, GlobalAllocationMachine.ensure kind hooks id before = .error typed final ∧
      RunLoop.reportsUB typed = false := by
  refine ⟨.callback s!"global allocation access: {reprStr error}",
    {before with machine := {state.machine with memory}},?_,rfl⟩
  simp [GlobalAllocationMachine.ensure,raw,pending,
    get,getThe,MonadStateOf.get,EStateM.get,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
/-- Exact typed interpretation used by the actual global conversion. -/
def conversionError : AllocationAdjustError StepError → StepError
  | .allocation error => .callback s!"global allocation conversion: {reprStr error}"
  | .byteConversion error | .pointerAdjustment error => error

/-- A finite conversion error stops before initExtra. No tag/counter margin
or invariant on its stopped state is needed. -/
theorem adjust_conversion_error [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (before final : MachineHooks.MachineState K U)
    (error : AllocationAdjustError StepError)
    (prepare : leaves.bytes.prepare id (RelocationBytePrimitives.snapshot source) source.align =
      pure (RelocationBytePrimitives.snapshot source,none))
    (conversion : Allocation.adjustFromTcx source target
      (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
      leaves.globalRootPointer before = .error error final) :
    GlobalAllocationMachine.adjust target extras leaves id source before =
      .error (conversionError error) final := by
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
      .ok (RelocationBytePrimitives.snapshot source) := by
    cases source
    simp [RelocationBytePrimitives.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]
  cases error <;>
    simp [GlobalAllocationMachine.adjust,inspect,prepare,conversion,conversionError,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,
      throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  all_goals with_unfolding_all rfl

/-- A successful byte conversion may still stop at its source root-tag
operation; the exact success and failure alternatives follow actual code. -/
theorem adjust_after_conversion [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (before middle : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (prepare : leaves.bytes.prepare id (RelocationBytePrimitives.snapshot source) source.align =
      pure (RelocationBytePrimitives.snapshot source,none))
    (diagnostic : leaves.diagnostic = fun _ _ _ => pure ())
    (conversion : Allocation.adjustFromTcx source target
      (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
      leaves.globalRootPointer before = .ok converted middle)
    (attributes : RelocationByteFold.Attributes source converted)
    (world : TreeRuntimeInput.World middle tracker) (noRace : middle.dataRace = none)
    (vacant : (extras.get middle.user).allocations.any (fun row => row.1 == id) = false) :
    (∃ global root, tracker.global.rootPointerTag id = .ok (global,root) ∧
      GlobalAllocationMachine.adjust target extras leaves id source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation extras {middle with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩) ∧
      TreeRuntimeInput.World
        (MemoryExtras.putAllocation extras {middle with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩)
        {tracker with global}) ∨
    (∃ error final, GlobalAllocationMachine.adjust target extras leaves id source before =
      .error error final ∧ RunLoop.reportsUB error = false) := by
  rcases init_extra extras middle id source.byteSize source.align tracker world noRace vacant with
    ⟨global,root,tagged,initialized,formed⟩ | ⟨error,final,failed,nonUB⟩
  · obtain ⟨actual,_⟩ := given_tagged_adjust target extras leaves id source converted before middle tracker
      prepare diagnostic conversion attributes world global root tagged noRace vacant
    exact Or.inl ⟨global,root,tagged,actual,formed⟩
  · right
    refine ⟨error,final,?_,nonUB⟩
    have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
        .ok (RelocationBytePrimitives.snapshot source) := by
      cases source
      simp [RelocationBytePrimitives.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
        Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]
    simp only [GlobalAllocationMachine.adjust,inspect,prepare,conversion,attributes.size,attributes.align,
      GlobalAllocationMachine.init,diagnostic,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
    simp only [pure,Pure.pure] at failed
    rw [failed]
    rfl
/-- Ordinary source descriptors carry a typed adjustment failure through
getAllocRaw without losing its changed state or its original error class. -/
theorem get_raw_adjust_error [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before final : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (error : StepError)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before = .error error final) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer) =
        ⟨final.memory,⟨final,some error⟩,
          .error (.globalAccess (.hookFailure "adjustGlobalAllocation" (reprStr error)))⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
  unfold_byte_source ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjustment]

/-- Actual canonical ensure preserves the original resource/callback error,
rather than replacing it with a classified string-boundary memory error. -/
theorem ensure_adjust_error [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (final : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (error : StepError)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before.machine = .error error final) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before =
      .error error {before with machine := final} := by
  have raw := get_raw_adjust_error target extras leaves initializer before.machine final id kind source error
    absent descriptor adjustment
  exact ensure_pending kind _ id before final.memory ⟨final,some error⟩ _ error raw rfl
/-- Internal-static initializers retain the same typed-error bridge. The
initializer equation is an internal compiler-image lookup, not an A input law. -/
theorem get_raw_static_adjust_error [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before final : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (definition : Nat) (source : Allocation CtfeProvenance Unit) (error : StepError)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (evaluated : initializer before.memory ⟨before,none⟩ definition =
      ⟨before.memory,⟨before,none⟩,.ok source⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before = .error error final) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer) =
        ⟨final.memory,⟨final,some error⟩,
          .error (.globalAccess (.hookFailure "adjustGlobalAllocation" (reprStr error)))⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
  unfold_byte_source ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp [evaluated,adjustment]

/-- Same exact restoration for materialized internal static storage. -/
theorem ensure_static_adjust_error [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (final : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (definition : Nat) (source : Allocation CtfeProvenance Unit) (error : StepError)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (evaluated : initializer before.machine.memory ⟨before.machine,none⟩ definition =
      ⟨before.machine.memory,⟨before.machine,none⟩,.ok source⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before.machine = .error error final) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before =
      .error error {before with machine := final} := by
  have raw := get_raw_static_adjust_error target extras leaves initializer before.machine final id kind definition source error
    absent descriptor evaluated adjustment
  exact ensure_pending kind _ id before final.memory ⟨final,some error⟩ _ error raw rfl
def installed (machine : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (allocation : Allocation Provenance BorrowTree) : MachineHooks.MachineState K U :=
  {machine with memory := {machine.memory with live :=
    (machine.memory.live.filter fun row => row.1 != id).push (id,⟨.machine kind,allocation⟩)}}

/-- Internal composition boundary: a proved actual owned adjustment result
runs through getAllocRaw and its actual live insertion without losing nested
callback changes to memory, addresses, tags, choices or threads. -/
theorem get_raw_owned [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before adjusted : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before = .ok (.owned allocation) adjusted) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer) =
        ⟨(installed adjusted id kind allocation).memory,⟨installed adjusted id kind allocation,none⟩,.ok allocation⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
  unfold_byte_source ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjustment]
  unfold_byte_source ".Miri.Memory.MemoryState.insertLive"
  rfl

theorem ensure_owned [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (adjusted : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before.machine = .ok (.owned allocation) adjusted) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before =
      .ok () {before with machine := installed adjusted id kind allocation} := by
  have raw := get_raw_owned target extras leaves initializer before.machine adjusted id kind source allocation absent descriptor adjustment
  simp only [GlobalAllocationMachine.ensure,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,raw]

end EmptyFunction.GlobalErrorAware

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.GlobalErrorAware.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved A global error axiom {dependency} in {name}"
