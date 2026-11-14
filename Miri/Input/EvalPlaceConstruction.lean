import Miri.Input.EvalCoreMachine
import Miri.Input.EvalProjectionMachine
import Miri.Input.CompilerFrameContext

/-! Direct place/compiler construction from pinned interpret/{place,operand,
projection,eval_context}.rs. No complete fallback compiler or projection record
is accepted. Validation is the actual visitor supplied by the final assembly;
the debug type assertion is a genuine compiler query, not an execution oracle. -/
namespace Miri.Input.EvalPlaceConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State

structure Options where
  debugAssertions : Bool
  maxSizeOfVal : Size
  dynamicFuel : Nat
  validation : ValidityMachine.ValidationMode

private def lift (value : Except ProjectionError A) : MachineHooks.M K U A :=
  match value with
  | .ok value => pure value
  | .error error => throw (IntrinsicVectorMachine.projectionError error)

/-- Same cache/read sequence as layout_of_local: cached layouts do not query
normalization again; a failed query cannot install a layout. -/
def localLayout (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (id : LocalId) : MachineHooks.M K U LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let slot ← match frame.getLocal id with
    | .ok value => pure value | .error error => throw (.stack error)
  if let some layout := slot.layout then return layout
  let layout ← CompilerFrameContext.computeLocalLayout p types id
  let (frame,layout) ← match (← MachineHooks.currentFrame).getOrCacheLocalLayout id layout with
    | .ok value => pure value | .error error => throw (.stack error)
  MachineHooks.setCurrentFrame frame
  pure layout

def dynamic (p : CompilerProviders.Prepared) (options : Options)
    (vtable : VTableHooks Provenance (State Os R P H D O Aff B Host) C F A)
    (typeConstants : RuntimeEffectfulLayout.Provider (State Os R P H D O Aff B Host) := RuntimeEffectfulLayout.unavailable) :
    DynamicLayoutHooks Provenance (State Os R P H D O Aff B Host) C where
  target := p.runtime.target.base
  maxSizeOfVal := options.maxSizeOfVal
  classify := fun _ ty => do lift (EvalProjectionMachine.dynamicKind p.lifecycle.calls.symbols.facts
    (EvalProjectionMachine.arrays.get (← get)) ty)
  field := fun _ layout index => EvalProjectionMachine.fieldEffectful p.runtime typeConstants layout index
  packedAlign := fun _ ty => RuntimeArrayQueries.perform EvalProjectionMachine.arrays
    (RuntimeMetadata.packedAlignInWorld p.runtime ty)
  vtableSizeAndAlign := VTable.getSizeAndAlign vtable

/-- The configured validation mode is the source Machine option. Final state
construction must install that same mode; actual enforce/ghost checks sample
the live state. Production place writes use scoped ValidityMachine.placeHooks. -/
def compiler
    (p : CompilerProviders.Prepared) (options : Options)
    (access : ValidityMachine.Access MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (vtable : VTableHooks Provenance (State Os R P H D O Aff B Host) C F A)
    (checkPlaceType : C → MIR.Place → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (validate : C → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (typeConstants : RuntimeEffectfulLayout.Provider (State Os R P H D O Aff B Host) := RuntimeEffectfulLayout.unavailable) :
    PlaceMachine.CompilerHooks MiriMemoryKind (User Os R P H D O Aff B Host) C :=
  let projection := fun (_ : C) => do
    return EvalProjectionMachine.context p.lifecycle.calls.symbols.facts options.maxSizeOfVal options.debugAssertions pointers (← get)
  let localToOp := fun (_ : C) id => PlaceMachine.localToOpCore (localLayout p EvalProjectionMachine.arrays) ValidityMachine.validationInProgress id
  let operand := placeToOpCore MachineHooks.currentFrame options.debugAssertions
    (do match (← get).stack.frameIndex with | .ok i => pure i | .error e => throw (.stack e)) localToOp projection
  {debugAssertions := options.debugAssertions
   layout := fun _ id => CompilerFrameContext.computeLocalLayout p EvalProjectionMachine.arrays id
   localSpan := CompilerFrameContext.localSpan p EvalProjectionMachine.arrays
   validationInProgress := ValidityMachine.validationInProgress
   projection
   deref := fun choice source skip => do
     let source ← operand choice source
     let pointerCompiler := CompilerExecutionProviders.pointerCompiler p.lifecycle.calls.symbols.facts EvalProjectionMachine.arrays
     let memory ← if skip then do
         PointerPlaceMachine.fromImmediate access pointerCompiler choice (← ValidityMachine.readImmediate access source)
       else PointerPlaceMachine.dereference access pointerCompiler (dynamic p options vtable typeConstants) vtable options.dynamicFuel choice source
     pure ⟨.memory memory.mplace,memory.layout⟩
   checkPlaceType
   memoryOffset := fun _ place amount mode metadata => do
     lift (EvalProjectionMachine.memoryOffset pointers (← get) place amount mode metadata)
   debugAbiCheck := fun value layout =>
     if options.debugAssertions then lift (EvalProjectionMachine.assertAbi p.runtime.target value layout.layout) else pure ()
   enforceValidity := fun _ _ => ValidityMachine.enforceValidity
   validate
   willValidateMemory := fun _ => options.validation != .No}

/-- Complete projection dictionary, including stateful runtime array interning,
physical vtable alignment and actual optimized-local reads. -/
def projection
    (p : CompilerProviders.Prepared) (options : Options)
    (access : ValidityMachine.Access MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind (User Os R P H D O Aff B Host) C)
    (vtable : VTableHooks Provenance (State Os R P H D O Aff B Host) C F A)
    (typeConstants : RuntimeEffectfulLayout.Provider (State Os R P H D O Aff B Host) := RuntimeEffectfulLayout.unavailable) :
    PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra where
  place := ValidityMachine.placeHooks access allocation compiler
  target := p.runtime.target.base
  maxSizeOfVal := options.maxSizeOfVal
  dynamic := dynamic p options vtable typeConstants
  dynamicFuel := options.dynamicFuel
  isSliceOrStr := fun _ ty => do
    let sourceKind ← RuntimeArrayQueries.perform EvalProjectionMachine.arrays
      (RuntimeMetadata.shapeKindInWorld p.runtime ty)
    pure (sourceKind == .slice || sourceKind == .str)
  field := fun _ layout index => EvalProjectionMachine.fieldEffectful p.runtime typeConstants layout index
  variant := fun _ layout index => RuntimeArrayQueries.perform EvalProjectionMachine.arrays
    (RuntimeMetadata.variantLayoutInWorld p.runtime layout index)
  packedAlign := fun _ ty => RuntimeArrayQueries.perform EvalProjectionMachine.arrays
    (RuntimeMetadata.packedAlignInWorld p.runtime ty)
  subsliceLayout := fun _ => EvalProjectionMachine.subslice
  layoutOf := fun _ ty => RuntimeEffectfulLayout.layout EvalProjectionMachine.arrays typeConstants CompilerTypingEnv.fullyMonomorphized none p.runtime ty
  localIndex := fun _ id => do
    let operand ← PlaceMachine.localToOpCore (localLayout p EvalProjectionMachine.arrays) ValidityMachine.validationInProgress id
    let value ← ValidityMachine.readImmediate access operand
    let scalar ← match value.imm.toScalar with
      | .ok value => pure value | .error error => throw (ScalarOps.immediateError error)
    match scalar.toTargetUsize access.runtime.pointerSize with
    | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
end Miri.Input.EvalPlaceConstruction
