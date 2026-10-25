import Miri.Interpreter.PlaceDynamic
open Miri Miri.ABI Miri.Memory Miri.Interpreter
private def layout (id : Nat) (sized : Bool) (size : UInt64) (align : Align)
    (fields : FieldsShape := .Primitive) : LocalLayout :=
  ⟨id, ⟨fields, .Single 0, .Memory (sized := sized), none, false, ⟨align⟩,
    Size.ofBytes size, none, align, false, 0⟩⟩
private def concrete := layout 0 true 16 ⟨3⟩
private def dynamic := layout 1 false 0 .ONE
private def parent := layout 2 false 1 .ONE (.Arbitrary #[Size.ofBytes 1] #[0])
private def dataId : AllocId := ⟨1, by decide⟩
private def vtableId : AllocId := ⟨2, by decide⟩
private def target : TargetDataLayout := ⟨.little, .w64⟩
private structure S where
  memory : MemoryState AllocId Unit Unit
  trace : Array String := #[]
  counter : Nat := 0
  rejectTrait : Bool := false
private def event (name : String) : PlaceM S Unit :=
  modify fun s => {s with trace := s.trace.push name, counter := s.counter + 1}
private def unavailable (name : String) : PlaceM S A := throw (.unsupported name)
private def placeHooks : PlaceHooks AllocId S Unit Unit := {
  debugAssertions := false
  getFrame := unavailable "frame", setFrame := fun _ => unavailable "frame"
  frameIndex := unavailable "frame", resolveLayout := fun _ _ => unavailable "local layout"
  localToOp := fun _ _ => unavailable "local read", projection := fun _ => unavailable "pure projection"
  deref := fun _ _ _ => unavailable "deref", checkPlaceType := fun _ _ _ => unavailable "typecheck"
  allocateStack := fun _ _ => unavailable "stack", writeMemoryNoValidate := fun _ _ _ => unavailable "write"
  afterLocalMovedToMemory := fun _ _ _ => unavailable "migration"
  memoryOffset := fun _ place amount mode metadata => do
    event "offset"
    let s ← get
    placeMemoryOffset ⟨Size.ofBytes 8⟩
      (fun ptr _ => match ptr.provenance with | some id => .ok ⟨id, ptr.offset, ()⟩ | none => .error 0)
      s.memory.getAllocInfo place amount mode metadata
  writeLocalImmediate := fun _ _ _ _ => unavailable "local write"
  enforceValidity := fun _ _ => unavailable "validity", validate := fun _ _ => unavailable "validate" }
private def vtable : VTableHooks AllocId S Unit Nat Nat := {
  target, isDynamic := fun _ _ => pure true
  memoryOffset := placeHooks.memoryOffset
  resolvePointer := fun _ ptr => do
    event "vtable-resolve"
    match ptr.provenance with
    | none => return .error .danglingInteger
    | some id => return .ok (id, ptr.offset)
  globalVTable := fun _ id => do
    event "vtable-global"
    let s ← get
    return if (s.memory.findGlobal? id).any (fun g => g.kind == .vtable) then some (0, 42) else none
  globalFunction := fun _ _ => unavailable "function"
  predicates := fun _ trait => do
    event s!"predicates:{trait}"
    return #[⟨trait, trait, false⟩]
  normalizePredicate := fun _ pred => do
    event "normalize"
    if (← get).rejectTrait then throw (.unsupported "predicate normalization unavailable")
    return pred.id
  layoutOf := fun _ ty => do
    event "vtable-layout"
    if ty != 0 then unavailable "vtable type layout" else pure concrete
  eraseAndAnonymize := fun _ _ _ => unavailable "erase"
  ensureMonomorphicType := fun _ _ => unavailable "monomorphic"
  ensureMonomorphicDyn := fun _ _ => unavailable "monomorphic"
  globalSalt := fun _ => unavailable "salt"
  reserveVTable := fun _ _ _ _ => unavailable "reserve"
  globalRootPointer := fun _ _ => unavailable "root"
  entries := fun _ _ _ => unavailable "entries"
  assertVirtualInstanceMatches := fun _ _ _ _ _ => unavailable "virtual" }
private def dynHooks : DynamicLayoutHooks AllocId S Unit := PlaceDynamic.withVTable {
  target, maxSizeOfVal := Size.ofBytes 1024
  classify := fun _ ty => do
    event s!"classify:{ty}"
    if ty == 1 then pure (.dynamic 42) else unavailable "dynamic classification"
  field := fun _ _ _ => unavailable "dynamic field"
  packedAlign := fun _ _ => unavailable "dynamic packed"
  vtableSizeAndAlign := fun _ _ _ => unavailable "vtable binding" } vtable
private def hooks : PlaceProjectionHooks AllocId S Unit Unit := {
  place := placeHooks, target, maxSizeOfVal := Size.ofBytes 1024
  dynamic := dynHooks, dynamicFuel := 8
  isSliceOrStr := fun _ _ => pure false
  field := fun _ l field => do
    event "field"
    if l.ty == 2 && field == 0 then pure dynamic else unavailable "project field"
  variant := fun _ _ _ => unavailable "variant"
  packedAlign := fun _ _ => do event "packed"; return none
  subsliceLayout := fun _ _ _ => unavailable "subslice"
  layoutOf := fun _ _ => unavailable "layout"
  localIndex := fun _ _ => unavailable "index" }
private def globalHooks : GlobalAllocationHooks AllocId Unit Unit (Array String) := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory s _ => ⟨memory, s, .error "no static"
  ⟩
  beforeAccessGlobal := fun memory s _ _ _ _ => ⟨memory, s, .error "no raw global"
  ⟩
  adjustGlobalAllocation := fun memory s _ _ => ⟨memory, s, .error "no raw global"⟩ }
private def accessHooks : AllocationAccessHooks AllocId Unit Unit (Array String) Unit := {
  resolvePointer := fun _ s ptr _ => match ptr.provenance with
    | some id => ⟨s.push "memory-resolve", .ok (.ok ⟨id, ptr.offset, ()⟩)⟩
    | none => ⟨s, .error "no address resolution"⟩
  beforeAllocationAccess := fun s _ => ⟨s.push "memory-access", .ok ()⟩
  beforeMemoryRead := fun s extra _ _ _ _ => ⟨s.push "memory-read", extra, .ok ()⟩
  beforeMemoryWrite := fun s extra _ _ _ _ => ⟨s.push "memory-write", extra, .ok ()⟩ }
private def copyHooks : MemoryCopyHooks AllocId Unit Unit (Array String) Unit := {
  synchronizeMemory := fun _ state => state
  pointerAccess := fun memory s ptr size => match ptr.provenance with
    | some id => ⟨memory,s.push "copy-resolve",.ok (if size.bytes == 0 then none else some (id, ptr.offset, ()))⟩
    | none => ⟨memory,s,.error "no exposed copy pointers"⟩
  tryGetAllocId := fun _ _ ptr _ => ptr.provenance
  beforeAllocationAccess := fun memory s _ => ⟨memory,s.push "copy-access",.ok ()⟩
  beforeMemoryRead := fun s memory _ _ _ _ _ => ⟨memory, s.push "copy-read", .ok ()⟩
  beforeMemoryWrite := fun s memory _ _ _ _ _ => ⟨memory, s.push "copy-write", .ok ()⟩ }
private def context : LocalReadContext AllocId Unit Unit (Array String) Unit := {
  runtime := .default, ghostMode := false, globalKind := none, globalHooks, accessHooks
  dynamicLayout := fun memory s _ => ⟨memory, s, .error "effectful layout must have run before access"⟩ }
private def base (metaId : AllocId := vtableId) (metaOffset : Size := Size.ZERO) : RuntimePlace AllocId :=
  ⟨.memory ⟨⟨Size.ZERO, some dataId⟩,
    .metadata (.fromPointer target ⟨metaOffset, metaId⟩), none⟩, parent⟩
private def initial : IO S := do
  let allocation ← match Allocation.fromBytes (Prov := AllocId) (Array.ofFn (fun i : Fin 32 => UInt8.ofNat i.val)) ⟨3⟩ .Mut with
    | .ok allocation => pure allocation | .error _ => throw (IO.userError "allocation")
  let memory0 := MemoryState.setIssuedIds
    (MemoryState.empty : MemoryState AllocId Unit Unit) #[dataId, vtableId]
  let memory1 : MemoryState AllocId Unit Unit := {memory0 with
    nextAllocId := 3, live := #[(dataId, ⟨.stack, allocation⟩)]}
  let memory := MemoryState.setGlobalEntries memory1
    #[⟨vtableId, .vtable, Size.ZERO, .ONE, .Not, some .vtable⟩]
  return { memory }
private def projectField := PlaceDynamic.project hooks () (base) (.Field 0 1)
def main : IO Unit := do
  let s ← initial
  let (place, s) ← match projectField s with
    | .ok place s => pure (place,s) | .error e _ => throw (IO.userError (reprStr e))
  let .memory memory := place.ref | throw (IO.userError "projection became local")
  unless memory.ptr.provenance == some dataId && memory.ptr.offset == Size.ofBytes 8 && memory.metadata.hasMeta do
    throw (IO.userError "DST projection lost provenance/metadata/alignment")
  unless s.trace == #["field", "classify:1", "vtable-resolve", "vtable-global", "predicates:42", "predicates:42",
      "normalize", "normalize", "vtable-layout", "packed", "offset"] do
    throw (IO.userError s!"DST effects reordered: {s.trace}")
  let action := PlaceDynamic.mutableAccess dynHooks () 8 context S.memory S.trace
    (fun s memory trace => {s with memory, trace}) (fun s _ => s) ⟨memory, place.layout⟩
  let s ← match action s with
    | .ok () s => pure s | .error e _ => throw (IO.userError (reprStr e))
  unless s.trace.toList.drop (s.trace.size-3) == ["memory-resolve", "memory-access", "memory-write"] do
    throw (IO.userError "dynamic access skipped real memory hooks")
  unless s.counter == 19 do throw (IO.userError s!"dynamic effects lost counter: {s.counter}")
  match projectField { (← initial) with rejectTrait := true } with
  | .ok _ _ => throw (IO.userError "normalization obligation succeeded")
  | .error _ s => unless s.trace == #["field", "classify:1", "vtable-resolve", "vtable-global", "predicates:42",
      "predicates:42", "normalize"] && s.counter == 7 do throw (IO.userError "failure rolled back state")
  match PlaceDynamic.project hooks () (base dataId) (.Field 0 1) (← initial) with
  | .ok _ _ => throw (IO.userError "data allocation accepted as symbolic vtable")
  | .error _ s => unless s.trace == #["field", "classify:1", "vtable-resolve", "vtable-global"] do
      throw (IO.userError "invalid symbolic vtable ordering")
  let (reserved, result) := s.memory.reserveAllocId
  let id ← match result with | .ok id => pure id | .error _ => throw (IO.userError "destination id")
  let allocation ← match Allocation.fromBytes (Prov := AllocId) (Array.replicate 32 0) ⟨3⟩ .Mut with
    | .ok a => pure a | .error _ => throw (IO.userError "destination allocation")
  let s := { s with memory := { reserved with live := reserved.live.push (id, ⟨.stack, allocation⟩) } }
  let destination : MPlaceTy AllocId := ⟨⟨⟨Size.ZERO, some id⟩, memory.metadata, none⟩, dynamic⟩
  let copy := PlaceDynamic.memoryCopy dynHooks () 8 true (Size.ofBytes 8) copyHooks S.memory S.trace
    (fun s memory trace => {s with memory, trace}) ⟨memory, dynamic⟩ destination
  let copied ← match copy s with
    | .ok () state => pure state | .error e _ => throw (IO.userError (reprStr e))
  unless copied.counter == s.counter + 16 do throw (IO.userError "DST copy lost dynamic state")
  let some entry := copied.memory.live.find? (fun entry => entry.1 == id) | throw (IO.userError "copy destination")
  let bytes ← match entry.2.allocation.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 16)) with
    | .ok bytes => pure bytes | .error _ => throw (IO.userError "copy bytes")
  unless bytes == Array.ofFn (fun i : Fin 16 => UInt8.ofNat (i.val + 8)) do
    throw (IO.userError "dynamic-size copy did not copy vtable-sized range")
  let foreign := { hooks with dynamic := { dynHooks with classify := fun _ _ => do
    event "foreign"; return .foreign } }
  match PlaceDynamic.project foreign () base (.Field 0 1) (← initial) with
  | .ok _ _ => throw (IO.userError "nonzero extern tail offset accepted")
  | .error _ s => unless s.trace == #["field", "foreign"] do
      throw (IO.userError "extern tail ran packed/offset effects")
  let thinBase : RuntimePlace AllocId := ⟨.memory ⟨⟨Size.ZERO, some dataId⟩, .none, none⟩, parent⟩
  match PlaceDynamic.project hooks () thinBase (.Field 0 1) (← initial) with
  | .ok _ _ => throw (IO.userError "missing dynamic metadata accepted")
  | .error _ s => unless s.trace == #["field", "classify:1"] do
      throw (IO.userError "metadata failure effect order")
  match PlaceDynamic.project hooks () (base vtableId (Size.ofBytes 1)) (.Field 0 1) (← initial) with
  | .ok _ _ => throw (IO.userError "interior symbolic vtable pointer accepted")
  | .error _ s => unless s.trace == #["field", "classify:1", "vtable-resolve"] do
      throw (IO.userError "interior vtable pointer looked up global")
  IO.println "effectful DST projection, symbolic vtable, provenance and mutable access passed"
