import Miri.Interpreter.DynamicLayout
open Miri Miri.ABI Miri.Memory Miri.Interpreter

private def layout (id : Nat) (sized : Bool) (size : UInt64 := 4) (align : Align := ⟨2⟩)
    (fields : FieldsShape := .Primitive) : TyAndLayout MIR.TyId := ⟨id, {
  fields, variants := .Single 0, backendRepr := .Memory (sized := sized),
  largestNiche := none, uninhabited := false, align := .new align,
  size := Size.ofBytes size, maxReprAlign := none, unadjustedAbiAlign := align,
  reprC := false, randomizationSeed := 0 }⟩
private def sizedLayout := layout 0 true
private def sliceLayout := layout 1 false 0 ⟨2⟩ (.Array (Size.ofBytes 4) 0)
private def strLayout := layout 2 false 0 .ONE (.Array (Size.ofBytes 1) 0)
private def structLayout := layout 3 false 1 .ONE (.Arbitrary #[Size.ofBytes 1] #[0])
private def tupleLayout := { structLayout with ty := 4 }
private def foreignLayout := layout 5 false 0 .ONE
private def dynLayout := layout 6 false 0 .ONE
private def packedLayout := { structLayout with ty := 7 }
private def foreignTail := { structLayout with ty := 8 }
private abbrev Trace := List String
private def log (name : String) (value : A) : RvalueM Trace A := do
  modify (· ++ [name])
  pure value
private def metadata (len : UInt64) : MemPlaceMeta AllocId :=
  .metadata (.fromScalarInt (.ofUInt64 len))
private def hooks : DynamicLayoutHooks AllocId Trace Unit where
  target := ⟨.little, .w64⟩
  maxSizeOfVal := Size.ofBytes 9223372036854775807
  classify := fun _ ty => do
    let _ ← log s!"classify:{ty}" ()
    match ty with
    | 1 => pure .slice | 2 => pure .str
    | 3 | 7 | 8 => pure (.adt false) | 4 => pure (.tuple false)
    | 5 => pure .foreign | 6 => pure (.dynamic 42)
    | _ => throw (.unsupported "missing dynamic type kind")
  field := fun _ parent index => do
    let _ ← log s!"field:{parent.ty}:{index}" ()
    match parent.ty with
    | 1 => pure sizedLayout
    | 2 => pure (layout 0 true 1 .ONE)
    | 3 | 4 => pure sliceLayout
    | 7 => pure dynLayout
    | 8 => pure foreignLayout
    | _ => throw (.unsupported "missing field")
  packedAlign := fun _ ty => log "packedAlign" (if ty == 7 then some .ONE else none)
  vtableSizeAndAlign := fun _ _ expected => do
    let _ ← log (if expected == some 42 then "vtable:42" else "vtable:unknown") ()
    pure (Size.ofBytes 16, ⟨3⟩)
private def run (action : RvalueM Trace A) := runRvalue action []
private def compute (l : TyAndLayout MIR.TyId) (n : UInt64) :=
  DynamicLayout.sizeAndAlignFromMeta hooks () 8 (metadata n) l
example : (run (DynamicLayout.sizeAndAlignFromMeta hooks () 0 .none sizedLayout)).2 =
    .ok (some (Size.ofBytes 4, ⟨2⟩)) := by decide
example : (run (compute sliceLayout 3)).2 = .ok (some (Size.ofBytes 12, ⟨2⟩)) := by decide
example : (run (compute strLayout 3)).2 = .ok (some (Size.ofBytes 3, .ONE)) := by decide
example : (run (compute structLayout 3)).2 = .ok (some (Size.ofBytes 16, ⟨2⟩)) := by decide
example : (run (compute tupleLayout 3)).2 = .ok (some (Size.ofBytes 16, ⟨2⟩)) := by decide
example : (run (compute packedLayout 0)).2 = .ok (some (Size.ofBytes 17, .ONE)) := by decide
example : (run (compute packedLayout 0)).1 =
    ["classify:7", "field:7:0", "classify:6", "vtable:42", "packedAlign"] := by decide
example : (run (compute foreignTail 0)).2 = .ok none := by decide
example : (run (compute foreignTail 0)).1 = ["classify:8", "field:8:0", "classify:5"] := by decide
example : (run (compute foreignLayout 0)).2 = .ok none := by decide
example : (run (compute sliceLayout 18446744073709551615)).2 =
    .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with maxSizeOfVal := Size.ofBytes 12 }
    () 8 (metadata 3) sliceLayout)).2 = .ok (some (Size.ofBytes 12, ⟨2⟩)) := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with maxSizeOfVal := Size.ofBytes 11 }
    () 8 (metadata 3) sliceLayout)).2 = .error (.undefinedBehavior "InvalidMeta(SliceTooBig)") := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with maxSizeOfVal := Size.ofBytes 15 }
    () 8 (metadata 3) structLayout)).2 = .error (.undefinedBehavior "InvalidMeta(TooBig)") := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta hooks () 8 .none sliceLayout)).2 =
    .error (.invalidProgram "unsized type requires metadata") := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta hooks () 0 (metadata 1) sliceLayout)).2 =
    .error (.resourceExhaustion "dynamic layout recursion fuel") := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with
    field := fun _ _ _ => pure (layout 0 true 0 ⟨2⟩) }
    () 8 (metadata 18446744073709551615) sliceLayout)).2 =
    .ok (some (Size.ZERO, ⟨2⟩)) := by decide
-- The classifier and tail-field queries must never fabricate unknown layouts.
example : (run (compute (layout 99 false) 0)).2 =
    .error (.unsupported "missing dynamic type kind") := by decide

private def allocId : AllocId := ⟨1, by decide⟩
private def pointer : Pointer (Option AllocId) := ⟨Size.ZERO, some allocId⟩
private def predicates (which : Nat) : Array VTablePredicate :=
  if which == 1 then #[⟨10, 2, false⟩, ⟨20, 1, false⟩, ⟨10, 2, false⟩, ⟨99, 9, true⟩]
  else if which == 2 then #[⟨20, 1, false⟩, ⟨11, 2, false⟩]
  else #[⟨30, 1, false⟩]
private def vtableHooks : VTableHooks AllocId Trace Unit Nat Nat where
  target := ⟨.little, .w64⟩
  isDynamic := fun _ _ => pure true
  memoryOffset := fun _ place _ _ md => pure { place with metadata := md }
  resolvePointer := fun _ ptr => log "resolve" (.ok (allocId, ptr.offset))
  globalVTable := fun _ _ => log "globalVTable" (some (0, 1))
  globalFunction := fun _ _ => log "globalFunction" (some 7)
  predicates := fun _ which => log s!"predicates:{which}" (predicates which)
  normalizePredicate := fun _ pred => log s!"normalize:{pred.id}" (if pred.id == 11 then 10 else pred.id)
  layoutOf := fun _ _ => log "layoutOf" sizedLayout
  eraseAndAnonymize := fun _ ty dyn => log "erase" (ty, dyn)
  ensureMonomorphicType := fun _ _ => log "monoType" ()
  ensureMonomorphicDyn := fun _ _ => log "monoDyn" ()
  globalSalt := fun _ => log "salt" 12
  reserveVTable := fun _ _ _ _ => log "reserve" allocId
  globalRootPointer := fun _ _ => log "globalRoot" pointer
  entries := fun _ _ _ => log "entries" #[.size, .vacant, .method 7]
  assertVirtualInstanceMatches := fun _ _ _ _ _ => log "instanceCheck" ()
private def validateABI (_ : Unit) (_ : Nat) (expected : Nat) : RvalueM Trace Unit := do
  let _ ← log "abiCheck" ()
  if expected != 1 then throw (.undefinedBehavior "function ABI mismatch")
example : (run (VTable.getSizeAndAlign (A := Nat) vtableHooks () pointer (some 2))).2 =
    .ok (Size.ofBytes 4, ⟨2⟩) := by decide
example : (run (VTable.getSizeAndAlign (A := Nat) vtableHooks () pointer (some 2))).1 =
    ["resolve", "globalVTable", "predicates:1", "predicates:2", "normalize:20", "normalize:20",
     "normalize:10", "normalize:11", "layoutOf"] := by decide
example : (run (VTable.getSizeAndAlign (A := Nat) vtableHooks () pointer (some 3))).2 =
    .error (.undefinedBehavior "InvalidVTableTrait") := by decide
example : (run (VTable.getPtrVTableType (A := Nat) vtableHooks () { pointer with offset := Size.ofBytes 1 } none)).1 =
    ["resolve"] := by decide
example : (run (VTable.getPtrVTableType (A := Nat) { vtableHooks with
    resolvePointer := fun _ _ => pure (.error .danglingInteger) } () pointer none)).2 =
    .error (.undefinedBehavior "InvalidVTablePointer") := by decide
example : (run (VTable.getPtrVTableType (A := Nat) { vtableHooks with
    globalVTable := fun _ _ => pure none } () pointer none)).2 =
    .error (.undefinedBehavior "InvalidVTablePointer") := by decide
example : (run (VTable.getPointer (A := Nat) vtableHooks () 0 1)).1 =
    ["erase", "monoType", "monoDyn", "salt", "reserve", "globalRoot"] := by decide
example : (run (VTable.getCallableFunction (A := Nat) vtableHooks validateABI () pointer 0)).2 =
    .error (.undefinedBehavior "function ABI mismatch") := by decide
example : (run (VTable.getCallableFunction (A := Nat) vtableHooks validateABI () pointer 1)).1 =
    ["resolve", "globalFunction", "abiCheck"] := by decide
example : (run (VTable.getMethod (A := Nat) vtableHooks validateABI () pointer 2 (some 1) 2 0 7 1)).1 =
    ["resolve", "globalVTable", "predicates:1", "predicates:2", "normalize:20", "normalize:20",
     "normalize:10", "normalize:11", "entries", "instanceCheck", "abiCheck"] := by decide
example : (run (VTable.getMethod (A := Nat) vtableHooks validateABI () pointer 2 (some 1) 1 0 7 1)).2 =
    .error (.undefinedBehavior "dyn call trying to call something that is not a method") := by decide

example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with
    classify := fun _ _ => pure (.adt true) } () 8 (metadata 1) structLayout)).2 =
    .error (.invalidProgram "unsized aggregate cannot be SIMD") := by decide
example : (run (compute (layout 3 false) 1)).2 =
    .error (.invalidProgram "unsized aggregate requires a tail field") := by decide
example : (run (VTable.getSizeAndAlign (A := Nat) { vtableHooks with
    layoutOf := fun _ _ => pure dynLayout } () pointer none)).2 =
    .error (.invalidProgram "there are no vtables for unsized types") := by decide
example : (run (VTable.getPtrFn (A := Nat) vtableHooks () { pointer with offset := Size.ofBytes 1 })).2 =
    .error (.undefinedBehavior "InvalidFunctionPointer") := by decide
example : (run (VTable.getPtrFn (A := Nat) { vtableHooks with globalFunction := fun _ _ => pure none } () pointer)).2 =
    .error (.undefinedBehavior "InvalidFunctionPointer") := by decide
example : (run (VTable.getPointer (A := Nat) { vtableHooks with
    ensureMonomorphicDyn := fun _ _ => do
      let _ ← log "monoDynFailed" ()
      throw (.unsupported "TooGeneric") } () 0 1)).1 = ["erase", "monoType", "monoDynFailed"] := by decide
private def dynPlace : OpTy AllocId :=
  ⟨.indirect ⟨pointer, .metadata (.fromPointer ⟨.little, .w64⟩ ⟨Size.ZERO, allocId⟩), none⟩, dynLayout⟩
example : (match (run (VTable.unpackDynTrait (A := Nat) vtableHooks () dynPlace 2)).2 with
    | .ok ⟨.indirect place, l⟩ => place.metadata == .none && place.ptr == pointer && l == sizedLayout
    | _ => false) = true := by decide
example : (match (run (VTable.unpackDynTrait (A := Nat) { vtableHooks with isDynamic := fun _ _ => pure false }
    () dynPlace 2)).2 with
    | .error (.invalidProgram "unpack_dyn_trait requires dynamic type") => true
    | _ => false) = true := by decide

private abbrev Mem := MemoryState AllocId Unit Unit
private def liftTrace (action : RvalueM Trace A) : RvalueM (Mem × Trace) A := fun state =>
  match action state.2 with
  | .ok value trace => .ok value (state.1, trace)
  | .error error trace => .error error (state.1, trace)
private def memoryHooks : DynamicLayoutHooks AllocId (Mem × Trace) Unit where
  target := hooks.target
  maxSizeOfVal := hooks.maxSizeOfVal
  classify := fun c t => liftTrace (hooks.classify c t)
  field := fun c t i => liftTrace (hooks.field c t i)
  packedAlign := fun c t => liftTrace (hooks.packedAlign c t)
  vtableSizeAndAlign := fun c p t => liftTrace (hooks.vtableSizeAndAlign c p t)
private def memoryPlace : MemoryOperandPlace AllocId :=
  ⟨⟨pointer, metadata 3, none⟩, localMemoryLayout sliceLayout⟩
example : (DynamicLayout.memoryResolver memoryHooks () 8 (fun _ => .ok sliceLayout)
    MemoryState.empty [] memoryPlace).outcome = .ok (some (Size.ofBytes 12, ⟨2⟩)) := by decide
example : (DynamicLayout.memoryResolver memoryHooks () 8 (fun _ => .ok sliceLayout)
    MemoryState.empty [] memoryPlace).hooks = ["classify:1", "field:1:0"] := by decide

/-- Actual executable finite table compared to selected pinned source expressions. -/
def main : IO Unit := do
  for l in [sliceLayout, structLayout] do
    for n in List.range 65 do
      match (run (compute l (UInt64.ofNat n))).2 with
      | .ok (some (size, align)) => IO.println s!"{size.bytes}:{align.pow2}"
      | result => throw (IO.userError s!"unexpected {repr result}")
  for n in [0, 1, 2305843009213693951, 2305843009213693952, 18446744073709551615] do
    match (run (compute sliceLayout n)).2 with
    | .ok (some (size, align)) => IO.println s!"{size.bytes}:{align.pow2}"
    | .error (.undefinedBehavior _) => IO.println "too-big"
    | result => throw (IO.userError s!"unexpected {repr result}")

-- Dynamic trait sizing actually routes through symbolic vtable validation.
example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with
    classify := fun _ _ => pure (.dynamic 2)
    vtableSizeAndAlign := VTable.getSizeAndAlign (A := Nat) vtableHooks }
    () 8 (.metadata (.fromPointer ⟨.little, .w64⟩ ⟨Size.ZERO, allocId⟩)) dynLayout)).2 =
    .ok (some (Size.ofBytes 4, ⟨2⟩)) := by decide
example : (run (DynamicLayout.sizeAndAlignFromMeta { hooks with
    classify := fun _ _ => pure (.dynamic 2)
    vtableSizeAndAlign := VTable.getSizeAndAlign (A := Nat) { vtableHooks with
      resolvePointer := fun _ _ => pure (.error .danglingInteger) } }
    () 8 (.metadata (.fromPointer ⟨.little, .w64⟩ ⟨Size.ZERO, allocId⟩)) dynLayout)).2 =
    .error (.undefinedBehavior "InvalidVTablePointer") := by decide

example : (DynamicLayout.memoryResolver { memoryHooks with
    classify := fun _ _ => do
      modify fun state => (state.1, state.2 ++ ["failed-classification"])
      throw (.unsupported "missing type metadata") }
    () 8 (fun _ => .ok sliceLayout) MemoryState.empty [] memoryPlace).hooks =
    ["failed-classification"] := by decide
example : ([0, 1, 2, 3, 4, 6].all fun index =>
    match (run (VTable.getMethod (A := Nat) { vtableHooks with
      entries := fun _ _ _ => pure #[.dropInPlace, .size, .align, .vacant, .traitVPtr 1, .method 7] }
      validateABI () pointer 2 (some 1) index 0 7 1)).2 with
    | .error (.undefinedBehavior "dyn call trying to call something that is not a method") => true
    | _ => false) = true := by decide
