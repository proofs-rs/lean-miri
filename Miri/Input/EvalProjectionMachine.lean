import Miri.Input.EvalAllocationMachine
import Miri.Input.RuntimeArrayQueries
import Miri.Input.RuntimeEffectfulLayout

/-! Physical projection and canonical type/layout queries on the final World.
Source: interpret/{projection,operand,place}.rs and eval_context.rs. Pure
immediate views are snapshots; indirect/dynamic effects use PlaceDynamic. -/
namespace Miri.Input.EvalProjectionMachine
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalBackendMachine.User
abbrev State := EvalBackendMachine.State
private def query (value : Except String A) : Except ProjectionError A :=
  value.mapError ProjectionError.obligation
private def metadataResult (value : Except RuntimeMetadataError A) : Except ProjectionError A :=
  value.mapError fun error => match error with
    | .unsupported reason => .machineError (.unsupported s!"compiler runtime metadata: {reason}")
    | error => .obligation (toString error)
private def arrayResult (value : Except RuntimeArrayTypes.Error A) : Except ProjectionError A :=
  value.mapError (ProjectionError.obligation ∘ reprStr)
private def lift (value : Except ProjectionError A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (IntrinsicVectorMachine.projectionError error)

def arrays : RuntimeArrayQueries.Access (State Os R P H D O Aff B Host) where
  get := fun s => s.machine.user.payload.payload.user.types
  set := fun s types => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user :=
      {s.machine.user.payload.payload.user with types}}}}}}

/-- The startup representation contains the same World outside the stack
registry. Reassociation changes the lens, never the arena's owner. -/
def outerArrays : RuntimeArrayQueries.Access (EvalWorld.State Os R P H D O Aff B Host) where
  get := fun s => s.machine.user.user.payload.payload.types
  set := fun s types => {s with machine := {s.machine with user := {s.machine.user with user :=
    {s.machine.user.user with payload := {s.machine.user.user.payload with payload :=
      {s.machine.user.user.payload.payload with types}}}}}}

private def kind (world : RuntimeArrayTypes.World) (ty : TyId) : Except ProjectionError TypeShapeKind :=
  query (world.arena.shapeKind ty)

/-- Immediate projection callbacks are read-only views. Any operation requiring
new identities belongs to the stateful projection hooks below. -/
private def readonly (world : RuntimeArrayTypes.World) (action : TypeArena.WorldM α) :
    Except ProjectionError α := do
  let (value,after) ← query (action.run world.arena)
  unless after.typeCount == world.arena.typeCount &&
      after.constantCount == world.arena.constantCount &&
      after.predicateCount == world.arena.predicateCount do
    throw (.obligation "projection snapshot requires effectful type interning")
  pure value

/-- Stateful source-field lens; query and CTFE effects stay in this machine. -/
def fieldEffectful (metadata : RuntimeMetadata)
    (provider : RuntimeEffectfulLayout.Provider (State Os R P H D O Aff B Host))
    (parent : LocalLayout) (index : Nat) : EStateM StepError (State Os R P H D O Aff B Host) LocalLayout :=
  RuntimeEffectfulLayout.fieldLayout arrays provider CompilerTypingEnv.fullyMonomorphized none metadata parent index

def packed (world : RuntimeArrayTypes.World) (ty : TyId) : Except ProjectionError (Option Align) :=
  readonly world (RuntimeMetadata.packedAlignInWorld world.metadata ty)

def field (world : RuntimeArrayTypes.World) (layout : LocalLayout) (index : Nat) :
    Except ProjectionError LocalLayout :=
  readonly world (RuntimeMetadata.fieldLayoutForInWorld world.metadata layout index)

/-- Exact source ABI shape assertion, including provenance restriction on
non-pointer scalars. It does not validate initialized scalar values. -/
def assertAbi (target : RuntimeTargetDataLayout) (value : Immediate Provenance) (layout : LayoutData) :
    Except ProjectionError Unit := do
  let check := fun (value : Memory.Scalar Provenance) (abi : ABI.Scalar) => do
    let size ← abi.size target |>.mapError (fun e => ProjectionError.obligation (reprStr e))
    unless value.size == size do throw (.invariant "immediate scalar ABI size mismatch")
    match abi.primitive with
    | .Pointer _ => pure ()
    | _ => if value.isPointer then throw (.invariant "non-pointer ABI scalar carries provenance")
  match value,layout.backendRepr with
  | .scalar v,.Scalar abi => check v abi
  | .scalarPair a b,.ScalarPair (a := abiA) (b := abiB) => check a abiA; check b abiB
  | .uninit,abi => unless abi.isSized do throw (.invariant "unsized immediate")
  | _,_ => throw (.invariant "immediate does not match ABI")

/-- The source metadata guard and signed conversion precede resolution.
Zero offset and wrapping mode never consult the address/allocation maps. -/
def memoryOffset
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (snapshot : State Os R P H D O Aff B Host) (place : MemPlace Provenance)
    (offset : Size) (mode : OffsetMode) (metadata : MemPlaceMeta Provenance) :
    Except ProjectionError (MemPlace Provenance) := do
  if metadata.hasMeta && !place.metadata.hasMeta then throw (.offset .addedMetadataToThinPlace)
  let mut resolved := none
  if mode == .inbounds then
    if offset.bytes.toNat >= 2^63 then throw (.offset (.offsetDoesNotFitI64 offset))
    if offset != .ZERO then
      if let some provenance := place.ptr.provenance then
        let hooks : AllocAddresses.AddressLookupHooks := {
          sizeOf := fun id => (snapshot.machine.memory.getAllocInfo id).toOption.map (·.size)
          isLive := fun id => some (snapshot.machine.memory.isAllocLive id) }
        let result ← snapshot.machine.user.addresses.ptrGetAlloc (Pointer.new provenance place.ptr.offset)
          (Int64.ofInt offset.bytes.toNat) hooks pointers.arithmetic
          |>.mapError (ProjectionError.machineError ∘ pointers.classifyAddressError)
        resolved := result.map fun (id,amount) => (⟨id,amount,provenance⟩ : ResolvedPointer Provenance)
  let resolver : PointerResolver Provenance Provenance := fun ptr _ =>
    match resolved with | some r => .ok r | none => .error ptr.offset.bytes
  projectionMemoryOffset pointers.arithmetic resolver snapshot.machine.memory.getAllocInfo place offset mode metadata

private def subsliceKnown (world : RuntimeArrayTypes.World) (base : LocalLayout) (count : UInt64) :
    Except ProjectionError (LocalLayout × MemPlaceMeta Provenance) := do
  match ← kind world base.ty with
  | .array =>
    let (_,element) ← arrayResult (RuntimeArrayTypes.arrayInfo world base.ty)
    let (layout,after) ← arrayResult (RuntimeArrayTypes.internElement world element count)
    unless after.arena.typeCount == world.arena.typeCount &&
        after.arena.constantCount == world.arena.constantCount do
      throw (.obligation "subslice constructor requires effectful canonical interning")
    pure (layout,.none)
  | .slice =>
    let scalar ← Memory.Scalar.fromUInt (BitVec.ofNat 128 count.toNat) world.metadata.target.pointerSize
      |>.mapError ProjectionError.scalar
    pure (base,.metadata scalar)
  | _ => throw (.invariant "subslice requires array or slice")

/-- Only immediate operations use this pure snapshot. Dynamic indirect fields,
MIR dereference/local index and constructor-allocating subslices have actual
stateful adapters; trying those effects here is an explicit obligation. -/
def context (prepared : CompilerFactAdapters.Prepared) (maxSizeOfVal : Size) (debug : Bool)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (snapshot : State Os R P H D O Aff B Host) : ProjectionCx Provenance :=
  let world := arrays.get snapshot
  { target := prepared.context.runtime.target.base
    maxSizeOfVal := maxSizeOfVal
    isSliceOrStr := fun ty => do
      let sourceKind ← kind world ty
      pure (sourceKind == .slice || sourceKind == .str)
    field := field world
    variant := fun layout index => readonly world
      (RuntimeMetadata.variantLayoutInWorld world.metadata layout index)
    dynamicAlign := fun _ _ => .error (.obligation "dynamic alignment requires effectful projection")
    packedAlign := packed world
    immediateOffset := fun v source offset target => projectionImmediateOffset
      (assertAbi prepared.context.runtime.target) v source offset target debug
    memoryOffset := memoryOffset pointers snapshot
    subsliceLayout := subsliceKnown world
    layoutOf := fun ty => readonly world (RuntimeMetadata.layoutInWorld world.metadata ty)
    deref := fun _ => .error (.obligation "typed dereference requires effectful projection")
    localIndex := fun _ => .error (.obligation "local index requires effectful local read") }

def dynamicKind (prepared : CompilerFactAdapters.Prepared) (world : RuntimeArrayTypes.World)
    (ty : TyId) : Except ProjectionError DynamicTypeKind := do
  match ← kind world ty with
  | .adt =>
    let view ← query (world.arena.lookupType ty)
    let definition ← match view with
      | .material node => match node.shape with
        | .adt data => pure data.definition
        | _ => throw (.invariant "ADT kind has no ADT source syntax")
      | .constructed (.adt identity _) => query (world.arena.definitionRef identity)
      | _ => throw (.invariant "ADT kind has no ADT constructor")
    let some source := world.arena.definitions[definition]?
      | throw (.obligation "dynamic ADT definition material absent")
    let some declaration := source.adtDeclaration
      | throw (.obligation "dynamic ADT declaration material absent")
    pure (.adt declaration.representation.simd)
  | .tuple => pure (.tuple false)
  | .dynamicTraitObject =>
    let .dynamic expected ← readonly world (CompilerFactAdapters.validityKindInWorld prepared ty)
      | throw (.invariant "dynamic type missing compiler predicates")
    pure (.dynamic expected)
  | .slice => pure .slice | .str => pure .str | .foreign => pure .foreign
  | _ => throw (.invariant "invalid unsized dynamic layout kind")

def dynamic (prepared : CompilerFactAdapters.Prepared)
    (base : DynamicLayoutHooks Provenance (State Os R P H D O Aff B Host) C)
    (provider : RuntimeEffectfulLayout.Provider (State Os R P H D O Aff B Host) := RuntimeEffectfulLayout.unavailable) :
    DynamicLayoutHooks Provenance (State Os R P H D O Aff B Host) C :=
  {base with
    target := prepared.context.runtime.target.base
    classify := fun _ ty => do
      let world := arrays.get (← get)
      if (← lift (kind world ty)) == TypeShapeKind.dynamicTraitObject then
        let some data ← RuntimeArrayQueries.perform arrays
          (WorldDynamicSource.runtimeData prepared.context.runtime (max 256 world.arena.typeCount) ty)
          | throw (StepError.invalidProgram "dynamic projection owner changed its source kind")
        return .dynamic data.predicates
      lift (dynamicKind prepared world ty)
    field := fun _ layout index => fieldEffectful prepared.context.runtime provider layout index
    packedAlign := fun _ ty => RuntimeArrayQueries.perform arrays
      (RuntimeMetadata.packedAlignInWorld prepared.context.runtime ty)}

/-- Array constructor effects occur after caller bounds/stride checks. Slice
metadata is converted with the actual target pointer width. -/
def subslice (base : LocalLayout) (count : UInt64) : EStateM StepError (State Os R P H D O Aff B Host)
    (LocalLayout × MemPlaceMeta Provenance) := do
  let world := arrays.get (← get)
  match ← lift (kind world base.ty) with
  | .array =>
    let (_,element) ← lift (arrayResult (RuntimeArrayTypes.arrayInfo world base.ty))
    return (← RuntimeArrayQueries.arrayLayout arrays element count,.none)
  | .slice => lift (subsliceKnown world base count)
  | _ => throw (.invalidProgram "subslice requires array or slice")

def bindCompiler (prepared : CompilerFactAdapters.Prepared) (maxSizeOfVal : Size)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (base : PlaceMachine.CompilerHooks MiriMemoryKind (User Os R P H D O Aff B Host) C) :=
  {base with
    projection := fun _ => do return context prepared maxSizeOfVal base.debugAssertions pointers (← get)
    memoryOffset := fun _ p offset mode metadata => do lift (memoryOffset pointers (← get) p offset mode metadata)
    debugAbiCheck := fun value layout =>
      if base.debugAssertions then lift (assertAbi prepared.context.runtime.target value layout.layout) else pure ()}

def bindProjection (prepared : CompilerFactAdapters.Prepared)
    (base : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (provider : RuntimeEffectfulLayout.Provider (State Os R P H D O Aff B Host) := RuntimeEffectfulLayout.unavailable) :
    PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra :=
  {base with
    target := prepared.context.runtime.target.base
    dynamic := dynamic prepared base.dynamic provider
    isSliceOrStr := fun _ ty => do
      let sourceKind ← lift (kind (arrays.get (← get)) ty)
      pure (sourceKind == .slice || sourceKind == .str)
    field := fun _ layout index => fieldEffectful prepared.context.runtime provider layout index
    variant := fun _ layout index => RuntimeArrayQueries.perform arrays
      (RuntimeMetadata.variantLayoutInWorld prepared.context.runtime layout index)
    packedAlign := fun _ ty => RuntimeArrayQueries.perform arrays
      (RuntimeMetadata.packedAlignInWorld prepared.context.runtime ty)
    subsliceLayout := fun _ => subslice
    layoutOf := fun _ ty => RuntimeEffectfulLayout.layout arrays provider CompilerTypingEnv.fullyMonomorphized none prepared.context.runtime ty}
end Miri.Input.EvalProjectionMachine
