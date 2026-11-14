import Miri.Input.WorldVTableInstance
import Miri.Input.WorldNeedsDrop
import Miri.Input.CtfeQueryBridge
import Miri.Memory.Allocation

/-! Pinned vtable.rs::vtable_allocation_provider. This module plans source slots
and renders real CTFE Allocation bytes/provenance through mandatory Action
capabilities. It installs no production allocator or runtime factory. -/
namespace Miri.Input.WorldVTableAllocationPlan
open Miri.ABI Miri.Memory GenericSubstitution TraitSelection Miri.Interpreter

structure Principal where
  definition : DefinitionIdentity
  arguments : Array Term
  deriving Repr, DecidableEq
/-- Query cache key: existential principal excludes Self and auto/projection
predicates. This key never denotes the symbolic global vtable allocation. -/
structure QueryKey where
  concrete : Term
  principal : Option Principal
  deriving Repr, DecidableEq
/-- Program-facing GlobalAlloc::VTable key: complete erased existential
predicate syntax and salt are retained, unlike the allocation-query key. -/
structure SymbolicKey where
  concrete : Term
  fullDynamicPredicates : Array Term
  salt : UInt64
  deriving Repr, DecidableEq
inductive Slot where
  | nullDrop | size (bytes : UInt64) | alignment (bytes : UInt64)
  | vacant | method (key : InstanceArena.Key)
  | vptr (key : QueryKey)
  deriving Repr
structure Plan where
  private mk ::
  key : QueryKey
  target : TargetDataLayout
  pointerSize : Size
  pointerAlign : Align
  slots : Array Slot

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

/-- Initial bounded source slice: canonical source u32 (Sized/noDrop), direct principal, no vptr,
final ordinary Item methods. No vtable query/slot/result catalog is read. -/
def prepare (work fuel : Nat) (noTraitVptr : Bool) (concrete : TypeId)
    (principal : Option TraitRef) : RuntimeArrayTypes.CompilerM Plan := do
  let start ← get
  unless start.metadata.source.producer.targetTriple.startsWith "x86_64-" &&
      start.metadata.target.defaultAddressSpace == .ZERO &&
      start.metadata.target.instructionAddressSpace == .ZERO &&
      start.metadata.target.pointerSize.bytes == 8 &&
      start.metadata.target.defaultAddressSpacePointerSpec.pointerAlign.pow2 == 3 do
    throw "source vtable plan requires64bit AS0 data pointers"
  let term ← liftPure (GenericInstantiationWorld.ofType start.arena fuel concrete)
  let term ← RuntimeArrayTypes.liftType (WorldNormalization.normalizeTerm
    start.metadata.normalizationContext work fuel term)
  let concrete ← RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType fuel term)
  let current ← get
  let source ← liftPure do
    match ← current.arena.lookupType concrete with
    | .constructed key => pure key
    | .material node =>
      let some key ← current.arena.materialKey node | throw "source vtable concrete constructor absent"
      let some seed := current.metadata.source.layouts[node.layoutId]?
        | throw "source vtable concrete source layout absent"
      unless seed.primitiveRecipe == some "u32" do
        throw "source vtable concrete source layout provider unavailable"
      pure key
  let .integer false .u32 := source
    | throw "source vtable initial concrete family is canonical u32;other sized families unavailable"
  let layout ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld start.metadata concrete)
  unless layout.layout.isSized do throw "source vtable plan requires Sized concrete type"
  if ← RuntimeArrayTypes.liftType (WorldNeedsDrop.query start.metadata fuel concrete) then
    throw "source vtable nontrivial drop allocation is unavailable"
  let align ← liftPure (layout.layout.align.abi.bytes.mapError toString)
  let mut slots := #[Slot.nullDrop,.size layout.layout.size.bytes,.alignment align]
  let queryPrincipal ← match principal with
    | none => pure none
    | some reference => do
      let segments ← WorldVTableSegments.query work fuel noTraitVptr reference
      let mut root := none
      for (segment,index) in segments.zipIdx do
        match segment with
        | .metadata => unless index == 0 do throw "source vtable duplicate metadata segment"
        | .ownEntries _ true => throw "source vtable upcast/vptr allocation is unavailable"
        | .ownEntries candidate false =>
          if candidate.definition == reference.definition then
            unless root.isNone do throw "source vtable duplicate direct principal segment"
            root := some candidate
          else
            -- Pinned implicit MetaSized is not an upcast-visible user supertrait.
            let world ← get
            let declarations := world.metadata.normalizationContext.traits.traits.filter (·.definition == candidate.definition)
            let #[declaration] := declarations | throw "source vtable implicit bound source ambiguous"
            unless declaration.builtin == some .metaSized && candidate.arguments == #[term] &&
                (← WorldDynMethods.query candidate.definition work fuel).isEmpty do
              throw "source vtable user supertrait allocation is unavailable"
      let some normalized := root | throw "source vtable direct principal segment absent"
      unless normalized.definition == reference.definition && normalized.arguments[0]? == some term do
        throw "source vtable principal concrete Self/key mismatch"
      let world ← get
      let kcfi := world.metadata.source.producer.abiSession.map (fun session => session.sanitizers.contains "kcfi")
      let declarations ← liftPure (WorldVTableInstance.ownDeclarations
        world.metadata.normalizationContext work fuel kcfi normalized)
      for declaration in declarations do
        match declaration with
        | none => slots := slots.push .vacant
        | some declaration =>
          let .item := declaration.kind
            | throw "source vtable function shim allocation is unavailable"
          let id ← WorldVTableInstance.intern fuel declaration
          let after ← get
          let key ← liftPure do
            match ← after.instances.lookup id with
            | .material key | .constructed key => pure key
          let .Item _ := key.kind | throw "source vtable requires a final Item method"
          slots := slots.push (.method key)
      pure (some ⟨normalized.definition,normalized.arguments.extract 1 normalized.arguments.size⟩)
  unless slots.size <= 4096 do throw "source vtable slot bound exceeded"
  pure ⟨⟨term,queryPrincipal⟩,start.metadata.target.base,
    start.metadata.target.pointerSize,start.metadata.target.defaultAddressSpacePointerSpec.pointerAlign,slots⟩

abbrev Action (W D A : Type) := CtfeQueryBridge.Action W D A
abbrev Failure (D : Type) := CtfeQueryBridge.Failure D
/-- Capabilities must use the actual central counter and typed global store.
None/Unsupported never falls through to old imported query rows or compatible
memory. A memory root is always freshly reserved, never byte-deduplicated. -/
structure Access (W D : Type) where
  compilerRun : Nat
  validateRun : Nat → Action W D Unit
  lookupQuery : Nat → QueryKey → Action W D (Option AllocId)
  createUninit : Size → Align → Action W D (Allocation CtfeProvenance Unit)
  internFunction : Nat → InstanceArena.Key → UInt64 → Action W D AllocId
  materializeVptr : Option (Nat → QueryKey → Action W D AllocId)
  reserveFreshMemory : Nat → Allocation CtfeProvenance Unit → Action W D AllocId
  publishQuery : Nat → QueryKey → AllocId → Action W D Unit
  internSymbolic : Option (Nat → SymbolicKey → Action W D AllocId)

private structure M (W D A : Type) where
  run : Action W D A
private instance : Monad (M W D) where
  pure value := ⟨fun world => (.ok value,world)⟩
  bind action next := ⟨fun world =>
    let (result,world) := action.run world
    match result with | .error error => (.error error,world) | .ok value => (next value).run world⟩
private def lift (action : Action W D A) : M W D A := ⟨action⟩
private def fail (reason : String) : M W D A := ⟨fun world => (.error (.unsupported reason),world)⟩
private def checked (value : Except E A) (label : String) [Repr E] : M W D A :=
  match value with | .ok value => pure value | .error error => fail s!"{label}: {reprStr error}"
private def pointer (target : TargetDataLayout) (id : AllocId) : M W D (Scalar CtfeProvenance) := do
  let provenance ← checked (CtfeProvenance.fromAllocId id) "source vtable function provenance"
  pure (Scalar.fromPointer target (Pointer.new provenance Size.ZERO))

/-- Symbolic interning is separate and never implicitly materializes memory.
A missing typed capability rejects before any legacy registry/cache access. -/
def internSymbolic (access : Access W D) (key : SymbolicKey) : Action W D AllocId :=
  match access.internSymbolic with
  | none => fun world => (.error (.unsupported "source symbolic vtable typed interning capability absent"),world)
  | some intern => (do
      lift (access.validateRun access.compilerRun)
      lift (intern access.compilerRun key) : M W D AllocId).run

/-- Allocation query hit does not reserve anything. On a miss the exact order
is host byte backing, slot-order function/vptr intern, writes, immutable finish,
fresh memory ID LAST, query publication. All global failure effects survive. -/
def materialize (access : Access W D) (plan : Plan) : Action W D AllocId := (do
  lift (access.validateRun access.compilerRun)
  if let some id ← lift (access.lookupQuery access.compilerRun plan.key) then return id
  unless plan.pointerSize.bytes == 8 && plan.slots.size >= 3 && plan.slots.size <= 4096 do
    fail "invalid source vtable bounded allocation plan"
  let size := Size.ofBytes (UInt64.ofNat (plan.slots.size * 8))
  let mut allocation ← lift (access.createUninit size plan.pointerAlign)
  unless allocation.byteSize == size && allocation.align == plan.pointerAlign && allocation.mutability == .Mut do
    fail "source vtable backing capability returned wrong shape or immutable storage"
  let bytes ← checked (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len) "source vtable fresh bytes"
  unless bytes.all (· == 0) && allocation.provenanceMap.ptrs.isEmpty && allocation.provenanceMap.byteFragments.isNone do
    fail "source vtable backing is not fresh zeroed/uninitialized compiler storage"
  for index in [:allocation.len] do
    if ← checked (allocation.initializationMask.get (Size.ofBytes (UInt64.ofNat index))) "source vtable uninit mask" then
      fail "source vtable backing is initialized before slot writes"
  for (slot,index) in plan.slots.zipIdx do
    let scalar ← match slot with
      | .vacant => pure none
      | .nullDrop => some <$> checked (Scalar.fromUInt (Prov := CtfeProvenance) 0 plan.pointerSize) "source null drop"
      | .size bytes | .alignment bytes =>
        some <$> checked (Scalar.fromUInt (Prov := CtfeProvenance) (BitVec.ofNat 128 bytes.toNat) plan.pointerSize) "source vtable header"
      | .method key => do
        let id ← lift (access.internFunction access.compilerRun key 0)
        some <$> pointer plan.target id
      | .vptr key => do
        let some query := access.materializeVptr | fail "source vptr allocation-query capability absent"
        some <$> pointer plan.target (← lift (query access.compilerRun key))
    if let some scalar := scalar then
      let range := allocRange (Size.ofBytes (UInt64.ofNat (index * 8))) plan.pointerSize
      match Allocation.writeScalar plan.target range scalar allocation with
      | .ok _ updated => allocation := updated
      | .error error _ => fail s!"source vtable scalar write: {reprStr error}"
  let immutable := allocation.withMutability .Not
  let id ← lift (access.reserveFreshMemory access.compilerRun immutable)
  lift (access.publishQuery access.compilerRun plan.key id)
  pure id : M W D AllocId).run
end Miri.Input.WorldVTableAllocationPlan
