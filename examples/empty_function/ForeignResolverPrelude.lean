import empty_function.ExternMapping
import empty_function.ChoiceExecution
import empty_function.ReuseTake
import Miri.Interpreter.RunLoop
namespace EmptyFunction.ForeignResolverPrelude
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev root (address : ChoiceExecution.H) : AllocId → EStateM StepError ChoiceExecution.S StrictPointer :=
  (reuse_actual ".EvalPointerSource.staticRootPointer") address

abbrev resolver (s : Static) (address : ChoiceExecution.H) : DefId → EStateM StepError ChoiceExecution.S StrictPointer :=
  (reuse_actual ".EvalPointerSource.externStatic") s.prepared.compiler s.prepared.image address

private theorem extern_view (state : ChoiceExecution.S) :
    EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter state.user) =
      state.user.payload.payload.user.runtime.externStatics := rfl

private theorem declaration (p : CompilerExternStatic.Prepared) (definition : DefId)
    (decl : CompilerExternStatic.Declaration)
    (lookup : p.declarations.find? (·.definition == definition) = some decl)
    (supported : decl.result = .ok ()) :
    (reuse_actual ".CompilerExternStatic.declaration") p definition = .ok decl := by
  unfold_reuse ".CompilerExternStatic.declaration"
  simp [lookup,supported,pure,Pure.pure,Except.pure]

/-- The actual shim branch precedes weak/exported handling, performs its
layout/clash checks, and returns the existing pointer without state effects. -/
theorem shim (s : Static) (address : ChoiceExecution.H) (before : State) (current : ChoiceExecution.S)
    (memory : current.memory = before.machine.memory)
    (runtime : current.user.payload.payload.user.runtime.externStatics = (ExternMapping.runtime before))
    (definition : DefId) (backing : AllocId) (decl : CompilerExternStatic.Declaration) (pointer : StrictPointer)
    (declaration : ExternMapping.Declaration s definition decl)
    (selected : (ExternMapping.entries before decl).find? (·.1 == decl.symbol) = some (decl.symbol,pointer))
    (identity : pointer.provenance.getAllocId = some backing)
    (layout : ExternMapping.LayoutBinding before decl backing)
    (symbols : CompilerForeignSymbols.Prepared)
    (foreignMetadata : s.prepared.compiler.foreignSymbols = .ok symbols)
    (clash : CompilerForeignSymbols.checkSymbolClash symbols decl.symbol = .ok ()) :
    resolver s address definition current = .ok pointer current := by
  have declared := ForeignResolverPrelude.declaration s.prepared.compiler.externStatics definition decl declaration.lookup declaration.supported
  unfold resolver
  unfold_reuse ".EvalPointerSource.externStatic"
  unfold CompilerExternStatic.resolveOn ExternStatic.resolve CompilerExternStatic.hooksOn
  unfold_reuse ".CompilerExternStatic.runtimeDeclaration"
  unfold_reuse ".ExternStatic.checkLayout"
  unfold_reuse ".ExternStatic.concrete"
  unfold_reuse ".CompilerExternStatic.liftMemory"
  have info : current.memory.getAllocInfo backing = .ok layout.info := by rw [memory];exact layout.lookup
  have chosen : (if decl.linkage == .none then
      current.user.payload.payload.user.runtime.externStatics.symbols else
      current.user.payload.payload.user.runtime.externStatics.imports).find? (·.1 == decl.symbol) = some (decl.symbol,pointer) := by
    simpa only [runtime,ExternMapping.entries] using selected
  simp only [beq_iff_eq] at chosen
  simp only [declared,bind,EStateM.bind,pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]
  simp [extern_view,chosen,foreignMetadata,clash,identity,info,show ¬decl.size.bytes > layout.info.size.bytes from UInt64.not_lt.mpr layout.size,
    show ¬decl.align.pow2 > layout.info.align.pow2 from Nat.not_lt.mpr layout.align,
    bind,EStateM.bind,pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]

/-- Missing external-weak cells are returned before exported lookup. The
source deliberately performs no backing layout or mutability check here. -/
theorem weak (s : Static) (address : ChoiceExecution.H) (before : State) (current : ChoiceExecution.S)
    (runtime : current.user.payload.payload.user.runtime.externStatics = (ExternMapping.runtime before))
    (definition : DefId) (decl : CompilerExternStatic.Declaration) (pointer : StrictPointer)
    (declaration : ExternMapping.Declaration s definition decl)
    (noShim : (ExternMapping.entries before decl).find? (·.1 == decl.symbol) = none)
    (linkage : decl.linkage = .externalWeak)
    (size : decl.size = s.prepared.compiler.externStatics.runtime.target.pointerSize)
    (selected : (ExternMapping.runtime before).missingWeak = some pointer) :
    resolver s address definition current = .ok pointer current := by
  have declared := ForeignResolverPrelude.declaration s.prepared.compiler.externStatics definition decl declaration.lookup declaration.supported
  unfold resolver
  unfold_reuse ".EvalPointerSource.externStatic"
  unfold CompilerExternStatic.resolveOn ExternStatic.resolve CompilerExternStatic.hooksOn
  unfold_reuse ".CompilerExternStatic.runtimeDeclaration"
  have missing : before.machine.user.payload.payload.user.runtime.externStatics.imports.find? (·.1 == decl.symbol) = none := by
    simpa [ExternMapping.entries,ExternMapping.runtime,linkage] using noShim
  have weakPointer : before.machine.user.payload.payload.user.runtime.externStatics.missingWeak = some pointer := selected
  simp [declared,extern_view,linkage,size,runtime,missing,weakPointer,ExternMapping.runtime,
    bind,EStateM.bind,pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]


/-- Exported winner selection performs every source metadata check before
calling the real root operation for the mapped runtime backing ID. The root
equation below is an internal composition edge, discharged by root admission. -/
theorem exported (s : Static) (address : ChoiceExecution.H) (before : State)
    (current after : ChoiceExecution.S) (memory : current.memory = before.machine.memory)
    (runtime : current.user.payload.payload.user.runtime.externStatics = ExternMapping.runtime before)
    (definition backingDefinition : DefId) (backing : AllocId)
    (decl : CompilerExternStatic.Declaration) (winner : CompilerExternStatic.Selected)
    (exportId : Input.AllocationId) (global : GlobalAllocation)
    (declaration : ExternMapping.Declaration s definition decl)
    (noShim : (ExternMapping.entries before decl).find? (·.1 == decl.symbol) = none)
    (linkage : decl.linkage ≠ .externalWeak)
    (lookup : s.prepared.compiler.externStatics.selected.find? (·.symbol == decl.symbol) = some winner)
    (supported : winner.winner.status = "supported") (kind : winner.winner.kind = "static")
    (winnerDefinition : winner.winner.definition = some backingDefinition)
    (allocation : winner.winner.allocation = some exportId)
    (image : s.prepared.image.source.any (·.id == exportId) = true)
    (mapping : before.machine.memory.runtimeIdForExport? exportId = some backing)
    (descriptor : before.machine.memory.findGlobal? backing = some global)
    (payload : global.payload = some (.static backingDefinition true false false))
    (layout : ExternMapping.LayoutBinding before decl backing)
    (mutability : (layout.info.mutability == .Mut) = decl.mutable)
    (pointer : StrictPointer) (rooted : root address backing current = .ok pointer after)
    (identity : pointer.provenance.getAllocId = some backing)
    (afterMemory : after.memory = before.machine.memory) :
    resolver s address definition current = .ok pointer after := by
  have declared := ForeignResolverPrelude.declaration s.prepared.compiler.externStatics definition decl declaration.lookup declaration.supported
  have selected : (reuse_actual ".CompilerExternStatic.selected") s.prepared.compiler.externStatics decl.symbol =
      (pure (some winner.winner) : EStateM StepError ChoiceExecution.S (Option CompilerExternStatic.Winner)) := by
    unfold_reuse ".CompilerExternStatic.selected"
    simp [lookup,supported,pure,Pure.pure]
  have currentNoShim : (if decl.linkage == .none then
      current.user.payload.payload.user.runtime.externStatics.symbols else
      current.user.payload.payload.user.runtime.externStatics.imports).find? (·.1 == decl.symbol) = none := by
    simpa only [runtime,ExternMapping.entries] using noShim
  simp only [beq_iff_eq] at currentNoShim
  have currentMapping : current.memory.runtimeIdForExport? exportId = some backing := by rw [memory];exact mapping
  have currentDescriptor : current.memory.findGlobal? backing = some global := by rw [memory];exact descriptor
  have finalInfo : after.memory.getAllocInfo backing = .ok layout.info := by rw [afterMemory];exact layout.lookup
  unfold resolver
  unfold_reuse ".EvalPointerSource.externStatic"
  unfold CompilerExternStatic.resolveOn ExternStatic.resolve CompilerExternStatic.hooksOn
  unfold_reuse ".CompilerExternStatic.runtimeDeclaration"
  unfold_reuse ".ExternStatic.checkLayout"
  unfold_reuse ".ExternStatic.concrete"
  unfold_reuse ".CompilerExternStatic.liftMemory"
  simp only [declared,bind,EStateM.bind,pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]
  simp only [extern_view,beq_iff_eq,currentNoShim,linkage,↓reduceIte,selected]
  simp only [bind,EStateM.bind,pure,Pure.pure,EStateM.pure,kind,winnerDefinition,allocation,get,getThe,MonadStateOf.get,EStateM.get,
    AllocationImage.runtimeId,currentMapping,currentDescriptor,payload,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have imagePresent : (s.prepared.image.source.any (·.id == exportId)) = true := image
  simp only [imagePresent,Bool.not_true,Bool.false_eq_true,↓reduceIte,bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  simp only [Except.pure,EStateM.pure,currentDescriptor,payload,beq_self_eq_true,↓reduceIte]
  simp only [root] at rooted
  rw [rooted]
  simp [identity,finalInfo,declared,mutability,
    show ¬decl.size.bytes > layout.info.size.bytes from UInt64.not_lt.mpr layout.size,
    show ¬decl.align.pow2 > layout.info.align.pow2 from Nat.not_lt.mpr layout.align,
    bind,EStateM.bind,pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]


theorem exported_error (s : Static) (address : ChoiceExecution.H) (before : State)
    (current after : ChoiceExecution.S) (memory : current.memory = before.machine.memory)
    (runtime : current.user.payload.payload.user.runtime.externStatics = ExternMapping.runtime before)
    (definition backingDefinition : DefId) (backing : AllocId)
    (decl : CompilerExternStatic.Declaration) (winner : CompilerExternStatic.Selected)
    (exportId : Input.AllocationId) (global : GlobalAllocation)
    (declaration : ExternMapping.Declaration s definition decl)
    (noShim : (ExternMapping.entries before decl).find? (·.1 == decl.symbol) = none)
    (linkage : decl.linkage ≠ .externalWeak)
    (lookup : s.prepared.compiler.externStatics.selected.find? (·.symbol == decl.symbol) = some winner)
    (supported : winner.winner.status = "supported") (kind : winner.winner.kind = "static")
    (winnerDefinition : winner.winner.definition = some backingDefinition)
    (allocation : winner.winner.allocation = some exportId)
    (image : s.prepared.image.source.any (·.id == exportId) = true)
    (mapping : before.machine.memory.runtimeIdForExport? exportId = some backing)
    (descriptor : before.machine.memory.findGlobal? backing = some global)
    (payload : global.payload = some (.static backingDefinition true false false))
    (layout : ExternMapping.LayoutBinding before decl backing)
    (_mutability : (layout.info.mutability == .Mut) = decl.mutable)
    (error : StepError) (rooted : root address backing current = .error error after) :
    resolver s address definition current = .error error after := by
  have declared := ForeignResolverPrelude.declaration s.prepared.compiler.externStatics definition decl declaration.lookup declaration.supported
  have selected : (reuse_actual ".CompilerExternStatic.selected") s.prepared.compiler.externStatics decl.symbol =
      (pure (some winner.winner) : EStateM StepError ChoiceExecution.S (Option CompilerExternStatic.Winner)) := by
    unfold_reuse ".CompilerExternStatic.selected"
    simp [lookup,supported,pure,Pure.pure]
  have currentNoShim : (if decl.linkage == .none then
      current.user.payload.payload.user.runtime.externStatics.symbols else
      current.user.payload.payload.user.runtime.externStatics.imports).find? (·.1 == decl.symbol) = none := by
    simpa only [runtime,ExternMapping.entries] using noShim
  simp only [beq_iff_eq] at currentNoShim
  have currentMapping : current.memory.runtimeIdForExport? exportId = some backing := by rw [memory];exact mapping
  have currentDescriptor : current.memory.findGlobal? backing = some global := by rw [memory];exact descriptor
  unfold resolver
  unfold_reuse ".EvalPointerSource.externStatic"
  unfold CompilerExternStatic.resolveOn ExternStatic.resolve CompilerExternStatic.hooksOn
  unfold_reuse ".CompilerExternStatic.runtimeDeclaration"
  unfold_reuse ".ExternStatic.checkLayout"
  unfold_reuse ".ExternStatic.concrete"
  unfold_reuse ".CompilerExternStatic.liftMemory"
  simp only [declared,bind,EStateM.bind,pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]
  simp only [extern_view,beq_iff_eq,currentNoShim,linkage,↓reduceIte,selected]
  simp only [bind,EStateM.bind,pure,Pure.pure,EStateM.pure,kind,winnerDefinition,allocation,get,getThe,MonadStateOf.get,EStateM.get,
    AllocationImage.runtimeId,currentMapping,currentDescriptor,payload,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have imagePresent : (s.prepared.image.source.any (·.id == exportId)) = true := image
  simp only [imagePresent,Bool.not_true,Bool.false_eq_true,↓reduceIte,bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  simp only [Except.pure,EStateM.pure,currentDescriptor,payload,beq_self_eq_true,↓reduceIte]
  simp only [root] at rooted
  rw [rooted]

/-- Actual static-root success always retains its runtime allocation ID.
No cached-root or spare-counter assumption is needed to invert success. -/
theorem root_identity_actual (address : ChoiceExecution.H) (current after : ChoiceExecution.S)
    (id : AllocId) (pointer : StrictPointer)
    (actual : root address id current = .ok pointer after) :
    pointer.provenance.getAllocId = some id := by
  cases tracked : current.borrowTracker with
  | none =>
    cases assigned : MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess address id (some .other) current with
    | error error final =>
      simp only [ChoiceExecution.tapeAccess] at assigned
      have equation : root address id current = .error error final := by
        unfold root
        unfold_reuse ".EvalPointerSource.staticRootPointer"
        simp [tracked,assigned,ChoiceExecution.tapeAccess,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
      rw [equation] at actual
      cases actual
    | ok base final =>
      simp only [ChoiceExecution.tapeAccess] at assigned
      have equation : root address id current = .ok (Pointer.new (.concrete id BorTag.one) (Size.ofBytes base)) final := by
        unfold root
        unfold_reuse ".EvalPointerSource.staticRootPointer"
        simp [tracked,assigned,ChoiceExecution.tapeAccess,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
      rw [equation] at actual
      cases actual
      rfl
  | some tracker =>
    cases tagged : tracker.global.rootPointerTag id with
    | error error =>
      have equation : root address id current =
          .error (.resourceExhaustion s!"extern static root tag: {reprStr error}") current := by
        unfold root
        unfold_reuse ".EvalPointerSource.staticRootPointer"
        simp [tracked,tagged,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,Pure.pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
      rw [equation] at actual
      cases actual
    | ok value =>
      obtain ⟨global,tag⟩ := value
      let rooted : ChoiceExecution.S := {current with borrowTracker := some {tracker with global}}
      cases assigned : MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess address id (some .other) rooted with
      | error error final =>
        simp only [ChoiceExecution.tapeAccess] at assigned
        have equation : root address id current = .error error final := by
          unfold root
          unfold_reuse ".EvalPointerSource.staticRootPointer"
          simp [tracked,tagged,assigned,rooted,ChoiceExecution.tapeAccess,get,getThe,MonadStateOf.get,EStateM.get,
            set,MonadStateOf.set,EStateM.set,bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
        rw [equation] at actual
        cases actual
      | ok base final =>
        simp only [ChoiceExecution.tapeAccess] at assigned
        have equation : root address id current = .ok (Pointer.new (.concrete id tag) (Size.ofBytes base)) final := by
          unfold root
          unfold_reuse ".EvalPointerSource.staticRootPointer"
          simp [tracked,tagged,assigned,rooted,ChoiceExecution.tapeAccess,get,getThe,MonadStateOf.get,EStateM.get,
            set,MonadStateOf.set,EStateM.set,bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
        rw [equation] at actual
        cases actual
        rfl
end EmptyFunction.ForeignResolverPrelude
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ForeignResolverPrelude.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved A foreign prelude axiom {dependency} in {name}"
