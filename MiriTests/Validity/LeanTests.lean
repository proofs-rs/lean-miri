import Miri.Memory.Validity

open Miri.ABI
open Miri.Memory
open Miri.Memory.Validity

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def size (bytes : Nat) : Size := Size.ofBytes (UInt64.ofNat bytes)
private def u128 (value : Nat) : U128 := BitVec.ofNat 128 value

private def nullHook : Scalar CtfeProvenance → Array String →
    EStateM.Result String (Array String) Bool := fun _ state => .ok false state

private def safeHooks (pointer : Scalar CtfeProvenance) (nullable : Bool)
    (failMetadata : Bool := false)
    (lookup : PointerAllocLookup := .noAllocationId) :
    SafePointerHooks CtfeProvenance Nat String (Array String) := {
  readImmediate := fun state => .ok pointer (state.push "read")
  resolvePlace := fun original state =>
    .ok ⟨original, pointer, .slice, Size.ofBytes 4, Align.ONE, none, 42⟩
      (state.push "resolve")
  checkWideMetadata := fun _ state =>
    if failMetadata then
      .error (.failure (.uninitialized .rawPointer none)) (state.push "metadata-error")
    else .ok () (state.push "metadata")
  sizeAndAlign := fun _ state => .ok (some (Size.ofBytes 4, Align.ONE))
    (state.push "size-align")
  checkAccess := fun _ _ state => .ok () (state.push "access")
  retagPointer := fun _ _ state => .ok none (state.push "retag")
  writeAdjustedPointer := fun _ state => .ok () (state.push "write-adjusted")
  resetPointerProvenance := fun _ state => .ok () (state.push "reset-provenance")
  markPointerData := fun state => .ok () (state.push "mark-data")
  scalarMayBeNull := fun _ state => .ok nullable (state.push "null-check")
  checkInhabited := fun _ state => .ok true (state.push "inhabited")
  checkAlignment := fun _ _ state => .ok () (state.push "alignment")
  ctfePointerAllocLookup := fun _ _ state => .ok lookup (state.push "ctfe-lookup")
}

private def runSafePointer (hooks : SafePointerHooks CtfeProvenance Nat String (Array String))
    (kind : SafePointerKind) (reset mayDangle : Bool)
    (tracking : Option (RefTracking Nat String × String)) :
    EStateM (ValidityError String) (Array String) (Option (RefTracking Nat String)) :=
  Validity.checkSafePointer hooks kind reset mayDangle none (UInt64.ofNat 100)
    tracking (fun path => path ++ ".<deref>") (fun description =>
      .rangeInvariant s!"unexpected metadata tail: {description}")

private def primitiveHooks : PrimitiveHooks CtfeProvenance String (Array String) := {
  clearProvenance := fun state => .ok () (state.push "clear")
  resetPointerProvenance := fun _ state => .ok () (state.push "reset-pointer")
  addDataRange := fun state => .ok () (state.push "data")
  checkRawPointerMetadata := fun _ state => .ok () (state.push "raw-metadata")
  checkFunctionPointer := fun _ state => .ok () (state.push "function-resolve")
}

def main : IO Unit := do
  let oneByteLayout : ScalarValidityLayout := ⟨size 1, ⟨u128 1, u128 255⟩⟩
  let invalidBool ← match Scalar.fromUInt (u128 2) (size 1) with
    | .ok scalar => pure scalar
    | .error reason => throw (IO.userError s!"invalid bool construction failed: {reason}")
  match Validity.checkPrimitive .boolean oneByteLayout invalidBool nullHook #[] with
  | .error (.failure (.invalidBool 2)) _ => pure ()
  | other => throw (IO.userError s!"invalid bool classification mismatch: {reprStr other}")

  let invalidChar ← match Scalar.fromUInt (u128 0xd800) (size 4) with
    | .ok scalar => pure scalar
    | .error reason => throw (IO.userError s!"invalid char construction failed: {reason}")
  let charLayout : ScalarValidityLayout := ⟨size 4, ⟨u128 0, u128 0x10ffff⟩⟩
  match Validity.checkPrimitive .character charLayout invalidChar nullHook #[] with
  | .error (.failure (.invalidChar 0xd800)) _ => pure ()
  | other => throw (IO.userError s!"invalid char classification mismatch: {reprStr other}")

  let validBool : Scalar CtfeProvenance := Scalar.fromBool true
  match Validity.checkPrimitive .boolean oneByteLayout validBool nullHook #[] with
  | .ok .valid #[] => pure ()
  | other => throw (IO.userError s!"valid bool classification mismatch: {reprStr other}")

  let dummy : Scalar CtfeProvenance := Scalar.fromBool false

  let pointerId ← match AllocId.ofUInt64 7 with
    | some id => pure id
    | none => throw (IO.userError "safe-pointer provenance ID was rejected")
  let pointerProv ← match CtfeProvenance.fromAllocId pointerId with
    | .ok prov => pure prov
    | .error reason => throw (IO.userError s!"safe-pointer provenance failed: {reprStr reason}")
  let pointer := Scalar.fromPointer ⟨.little, .w64⟩ (Pointer.new pointerProv (Size.ofBytes 8))

  let tracker := RefTracking.empty
  match runSafePointer (safeHooks pointer false) (.reference false) false false
      (some (tracker, "root")) #[] with
  | .ok (some visited) events =>
    check (events == #["read", "resolve", "metadata", "size-align", "access",
      "null-check", "inhabited", "alignment"]) "safe-reference checks were reordered"
    check (visited.todo == #[(42, "root.<deref>")]) "safe-reference was not queued for recursion"
  | other => throw (IO.userError s!"safe-reference validation mismatch: {reprStr other}")

  match runSafePointer (safeHooks pointer false) .box true true none #[] with
  | .ok none events =>
    check (events == #["read", "mark-data", "resolve", "metadata", "size-align",
      "reset-provenance", "null-check", "inhabited", "alignment"])
      "may-dangle Box validation performed access or skipped provenance reset"
  | other => throw (IO.userError s!"may-dangle Box validation mismatch: {reprStr other}")

  match runSafePointer (safeHooks pointer true) (.reference true) false false none #[] with
  | .error (.failure (.nullSafePointer (.reference true) true)) events =>
    check (events == #["read", "resolve", "metadata", "size-align", "access", "null-check"])
      "null-reference failure did not stop before inhabitedness/alignment"
  | other => throw (IO.userError s!"null-reference classification mismatch: {reprStr other}")

  match runSafePointer (safeHooks pointer false true) .box false false none #[] with
  | .error (.failure (.uninitialized .rawPointer none)) events =>
    check (events == #["read", "resolve", "metadata-error"])
      "wide-pointer metadata failure did not stop before size/access"
  | other => throw (IO.userError s!"wide-pointer metadata failure mismatch: {reprStr other}")

  let initialTracker : RefTracking Nat String := .empty
  let validateCtfe := fun lookup => Validity.checkSafePointer
      (safeHooks pointer false false lookup) (.reference false) false false
      (some (.static false)) (UInt64.ofNat 100) (some (initialTracker, "ctfe-root"))
      (fun path => path ++ ".<deref>") (fun description =>
        .rangeInvariant s!"unexpected metadata tail: {description}")
  match validateCtfe .noAllocationId #[] with
  | .ok (some visited) events =>
    check (events == #["read", "resolve", "metadata", "size-align", "access",
      "null-check", "inhabited", "alignment", "ctfe-lookup"])
      "CTFE reference allocation lookup was performed at the wrong stage"
    check (visited.todo == #[(42, "ctfe-root.<deref>")])
      "reference with no allocation ID was not recursively queued"
  | other => throw (IO.userError s!"CTFE reference validation mismatch: {reprStr other}")

  match validateCtfe (.global (Size.ofBytes 4) .Not (.static false false)) #[] with
  | .ok (some visited) events =>
    check (events.size == 9) "CTFE non-nested static lookup lost ordered validation effects"
    check (visited.todo.isEmpty) "non-nested CTFE static was recursively validated"
  | other => throw (IO.userError s!"CTFE static skip mismatch: {reprStr other}")

  let validateMutableCtfe := Validity.checkSafePointer
      (safeHooks pointer false false (.global (Size.ofBytes 4) .Not .other)) .box false false
      (some (.constant true)) (UInt64.ofNat 100) (some (initialTracker, "box-root"))
      (fun path => path ++ ".<deref>") (fun description =>
        .rangeInvariant s!"unexpected metadata tail: {description}")
  match validateMutableCtfe #[] with
  | .error (.failure (.mutablePointerToReadOnly .box)) events =>
    check (events.back? == some "ctfe-lookup")
      "mutable-to-read-only CTFE failure did not follow alignment and allocation lookup"
  | other => throw (IO.userError s!"CTFE Box mutability mismatch: {reprStr other}")

  let unavailableHooks := { safeHooks pointer false with
    ctfePointerAllocLookup := fun _ _ state =>
      .error (.machine "allocation lookup unavailable") (state.push "lookup-unavailable") }
  let unavailableLookup := Validity.checkSafePointer unavailableHooks (.reference false)
      false false (some (.constant true)) (UInt64.ofNat 100)
      (some (initialTracker, "lookup-root")) (fun path => path ++ ".<deref>")
      (fun description => .rangeInvariant s!"unexpected metadata tail: {description}")
  match unavailableLookup #[] with
  | .error (.machine "allocation lookup unavailable") events =>
    check (events == #["read", "resolve", "metadata", "size-align", "access",
      "null-check", "inhabited", "alignment", "lookup-unavailable"])
      "unavailable allocation metadata was converted into a validity outcome"
  | other => throw (IO.userError s!"unavailable allocation lookup mismatch: {reprStr other}")

  match Validity.visitPrimitive primitiveHooks (.rawPointer false) oneByteLayout pointer
      true false nullHook #[] with
  | .ok .valid events =>
    check (events == #["reset-pointer", "data", "raw-metadata"])
      "wide raw pointer must reset provenance and mark data before metadata validation"
  | other => throw (IO.userError s!"raw pointer visitor mismatch: {reprStr other}")

  match Validity.visitPrimitive primitiveHooks .functionPointer oneByteLayout pointer
      true true nullHook #[] with
  | .ok .valid events =>
    check (events == #["function-resolve", "data"])
      "recursive function pointer was not resolved before data tracking"
  | other => throw (IO.userError s!"recursive function-pointer visitor mismatch: {reprStr other}")

  match Validity.visitPrimitive primitiveHooks .functionPointer oneByteLayout pointer
      true false (fun _ state => .ok true (state.push "null-check")) #[] with
  | .error (.failure (.nullFunctionPointer true)) events =>
    check (events == #["null-check"])
      "nullable function pointer was accepted or reset before validation"
  | other => throw (IO.userError s!"nullable function-pointer mismatch: {reprStr other}")

  let flags : VisitorFlags := ⟨true, false⟩
  match withMaybeDangling flags true
      (fun nested state =>
        (EStateM.Result.ok nested.mayDangle state : EStateM.Result String (Array String) Bool))
      (#[] : Array String) with
  | .ok (true, restored) _ =>
    check (restored == flags) "MaybeDangling visitor flag was not restored after recursion"
  | other => throw (IO.userError s!"MaybeDangling scope mismatch: {reprStr other}")

  check (ctfeRecursionDecision (.static false) (.reference false)
      (.global (Size.ofBytes 1) .Not (.static false false)) == .ok true)
    "CTFE static reference should skip a non-nested static allocation"
  check (ctfeRecursionDecision .promoted .box
      (.global Size.ZERO .Not (.other)) == .ok false)
    "zero-sized Box should not impose an allocation mutability check"
  check (ctfeRecursionDecision (.constant true) (.reference true)
      (.global (Size.ofBytes 1) .Not .other) ==
        .error (.mutablePointerToReadOnly (.reference true)))
    "mutable reference to non-mutable global memory was accepted"
  check (ctfeRecursionDecision (.constant false) (.reference false)
      (.missingGlobal true) == .ok true)
    "partially interned CTFE allocation should skip recursive descent"
  check (ctfeRecursionDecision (.constant true) (.reference false)
      (.missingGlobal false) == .error (.danglingSafePointer (.reference false)))
    "missing CTFE global allocation was not classified as dangling"

  let cases : Array (PrimitiveKind × PrimitiveStep) := #[
    (.foreign, .valid), (.functionDefinition, .valid), (.rawPointer true, .valid),
    (.rawPointer false, .rawPointerMetadata), (.safeReference, .safePointer),
    (.functionPointer, .functionPointer), (.aggregate, .recurse)]
  for (kind, expected) in cases do
    match Validity.checkPrimitive kind oneByteLayout dummy nullHook #[] with
    | .ok actual #[] => check (actual == expected) s!"primitive step mismatch for {reprStr kind}"
    | other => throw (IO.userError s!"primitive delegation mismatch: {reprStr other}")

  match Validity.checkPrimitive .never oneByteLayout dummy nullHook #[] with
  | .error (.failure .neverValue) _ => pure ()
  | other => throw (IO.userError s!"never-type classification mismatch: {reprStr other}")

  let path : ValidationPath := ⟨"Root", #[.field "inner", .tupleElem 2,
    .arrayElem 7, .deref, .dynDowncast "Concrete"]⟩
  check (path.render == ".inner.2[7].<deref>.<dyn-downcast(Concrete)>")
    "validity path rendering diverged from source write_path"
  check (aggregateFieldPathElem
      ⟨"E", .enum, .multiple 0, 0, none, none, "?"⟩ == .ok .enumTag)
    "enum tag path element was not recognized"
  check (aggregateFieldPathElem
      ⟨"Closure", .closure, .single, 3, none, none, "?"⟩ ==
      .ok (.capturedVar "3")) "closure capture did not use the source numeric fallback"
  check (aggregateFieldPathElem
      ⟨"dyn Trait", .dynamic, .single, 0, none, none, "Concrete"⟩ ==
      .ok (.dynDowncast "Concrete")) "dynamic path did not name the concrete downcast type"
  check (aggregateFieldPathElem
      ⟨"dyn Trait", .dynamic, .single, 1, none, none, "?"⟩ ==
      .error (.dynamicFieldIndex 1)) "nonzero dynamic projection was accepted"
  check (variantPathElem "C" .coroutine 4 none == .ok (.coroutineState 4))
    "coroutine state path was not retained"

  let unionGraph : UnionLayoutGraph := {
    root := 0
    nodes := #[
      ⟨size 12, .unionFields #[1, 2], .single⟩,
      ⟨size 4, .primitive, .single⟩,
      ⟨size 12, .arbitrary #[3, 4] #[size 0, size 8], .single⟩,
      ⟨size 4, .primitive, .single⟩,
      ⟨size 4, .primitive, .single⟩]
  }
  let unionData ← match unionDataRange unionGraph with
    | .ok data => pure data
    | .error reason => throw (IO.userError s!"union data range failed: {reprStr reason}")
  check (unionData.toArray == #[allocRange (size 0) (size 4), allocRange (size 8) (size 4)])
    "nested union field ranges did not preserve source padding gaps"
  let scalarArrayGraph : UnionLayoutGraph := {
    root := 0
    nodes := #[
      ⟨size 5, .array 1 (size 1) (UInt64.ofNat 5) true, .single⟩,
      ⟨size 1, .primitive, .single⟩]
  }
  check (((unionDataRange scalarArrayGraph).map fun data => data.toArray) ==
      .ok #[allocRange (size 0) (size 5)])
    "scalar array union fast path did not coalesce the full element range"
  let stridedArrayGraph : UnionLayoutGraph := {
    root := 0
    nodes := #[
      ⟨size 5, .array 1 (size 2) (UInt64.ofNat 3) false, .single⟩,
      ⟨size 1, .primitive, .single⟩]
  }
  check (((unionDataRange stridedArrayGraph).map fun data => data.toArray) ==
      .ok #[allocRange (size 0) (size 1), allocRange (size 2) (size 1),
        allocRange (size 4) (size 1)])
    "strided union array traversal lost element padding"
  let cyclicGraph : UnionLayoutGraph := {
    root := 0
    nodes := #[⟨size 1, .unionFields #[0], .single⟩]
  }
  check (unionDataRange cyclicGraph == .error (.recursiveLayout 0))
    "malformed recursive layout was converted to an empty data range"

  let unionHooks (mutable : Bool) : UnionVisitHooks String (Array String) := {
    dynamicSize := fun state => .ok (some (size 12)) (state.push "dynamic-size")
    isFreeze := fun state => .ok false (state.push "freeze")
    isMutableMemory := fun state => .ok mutable (state.push "mutable-memory")
    dataRangeOffset := fun state => .ok (size 20) (state.push "data-offset")
  }
  match visitUnion (unionHooks false) (some (.static false)) path true
      (some DataRangeSet.empty) unionGraph #[] with
  | .error (.pathFailure _ .unsafeCellInReadOnlyMemory)
      #[("dynamic-size"), ("freeze"), ("mutable-memory")] => pure ()
  | other => throw (IO.userError s!"union UnsafeCell check/order mismatch: {reprStr other}")
  match visitUnion (unionHooks true) (some .promoted) path true
      (some DataRangeSet.empty) unionGraph #[] with
  | .ok (some data) events =>
    check (events == #["dynamic-size", "freeze", "mutable-memory", "data-offset"])
      "union data-range mutation ran before CTFE Freeze/mutability validation"
    check (data.toArray == #[allocRange (size 20) (size 4), allocRange (size 28) (size 4)])
      "union data offsets were not translated into allocation-relative coordinates"
  | other => throw (IO.userError s!"union visit mismatch: {reprStr other}")

  let unsafeCellCheck : EStateM (ValidityError String) (Array String) Unit :=
    checkUnsafeCell (some (.constant false)) false true path
      (fun state => .ok false (state.push "mutable-query"))
  match unsafeCellCheck #[] with
  | .error (.pathFailure _ .unsafeCellInReadOnlyMemory) #["mutable-query"] => pure ()
  | other => throw (IO.userError s!"UnsafeCell read-only validation mismatch: {reprStr other}")
  let zstUnsafeCell : EStateM (ValidityError String) (Array String) Unit :=
    checkUnsafeCell (some .promoted) true true path
      (fun state => .ok false (state.push "should-not-query"))
  match zstUnsafeCell #[] with
  | .ok () #[] => pure ()
  | other => throw (IO.userError s!"ZST UnsafeCell was not exempted: {reprStr other}")

  let walkHooks : ValueWalkHooks String (Array String) := {
    tryVisitPrimitive := fun node walkPath flags state =>
      .ok (node != 0) (state.push
        s!"primitive:{node}:{walkPath.render}:dangle={flags.mayDangle}")
    checkUnsafeCell := fun node _ _ state => .ok () (state.push s!"unsafe:{node}")
    tryVisitSpecialCase := fun node _ _ state =>
      .ok false (state.push s!"special:{node}")
    visitUnion := fun node count _ _ state =>
      .ok () (state.push s!"union:{node}:{count}")
    visitBox := fun node pointer _ _ state =>
      .ok () (state.push s!"box:{node}:{pointer}")
    readDiscriminant := fun node state => .ok 1 (state.push s!"tag:{node}")
    visitVariantless := fun node _ state => .ok () (state.push s!"empty:{node}")
  }
  let structWalk : ValueWalkGraph := {
    root := 0
    nodes := #[
      { typeName := "S", pathInfo := ⟨"S", .struct, .single, 0, none, none, "?"⟩,
        fields := .arbitrary #[1, 0] #[1, 2], variants := .single,
        fieldNames := #[some "left", some "right"], isLikeMaybeDangling := true },
      { typeName := "u8", pathInfo := ⟨"u8", .other "u8", .single, 0, none, none, "?"⟩,
        fields := .primitive, variants := .single },
      { typeName := "u16", pathInfo := ⟨"u16", .other "u16", .single, 0, none, none, "?"⟩,
        fields := .primitive, variants := .single }]
  }
  match walkValue walkHooks structWalk ⟨"Root", #[]⟩ ⟨false, false⟩ #[] with
  | .ok () events =>
    check (events == #[
      "primitive:0::dangle=false", "unsafe:0", "special:0",
      "primitive:2:.right:dangle=true", "primitive:1:.left:dangle=true"])
      "ValueVisitor did not preserve in-memory field order, paths, or MaybeDangling scope"
  | other => throw (IO.userError s!"struct ValueVisitor walk mismatch: {reprStr other}")
  let enumWalk : ValueWalkGraph := {
    root := 0
    nodes := #[
      { typeName := "E", pathInfo := ⟨"E", .enum, .multiple 0, 0, none, none, "?"⟩,
        fields := .primitive, variants := .multiple #[1, 2],
        variantNames := #[some "A", some "B"] },
      { typeName := "A", pathInfo := ⟨"A", .other "A", .single, 0, none, none, "?"⟩,
        fields := .primitive, variants := .single },
      { typeName := "B", pathInfo := ⟨"B", .other "B", .single, 0, none, none, "?"⟩,
        fields := .primitive, variants := .single }]
  }
  match walkValue walkHooks enumWalk ⟨"E", #[]⟩ ⟨false, false⟩ #[] with
  | .ok () events =>
    check (events == #["primitive:0::dangle=false", "unsafe:0", "special:0",
      "tag:0", "primitive:2:.<enum-variant(B)>:dangle=false"])
      "ValueVisitor did not read the discriminant after fields or select its variant path"
  | other => throw (IO.userError s!"enum ValueVisitor walk mismatch: {reprStr other}")
  let cyclicWalk : ValueWalkGraph := {
    root := 0
    nodes := #[
      { typeName := "Loop", pathInfo := ⟨"Loop", .struct, .single, 0, none, none, "?"⟩,
        fields := .arbitrary #[0] #[0], variants := .single,
        fieldNames := #[some "self"] }]
  }
  match walkValue walkHooks cyclicWalk ⟨"Loop", #[]⟩ ⟨false, false⟩ #[] with
  | .error (.walkInvariant _) events =>
    check (events.size == 3) "recursive by-value layout ran visitor hooks past its cycle boundary"
  | other => throw (IO.userError s!"recursive ValueVisitor layout mismatch: {reprStr other}")

  let placeHooks : ValidatePlaceHooks Nat Nat String (Array String) := {
    isStoredInMemory := fun _ state => .ok true (state.push "stored")
    visitValue := fun place session state => Id.run do
      let state := state.push s!"visit:{place}:dangle={session.flags.mayDangle}"
      if place == 0 then
        let data ← match DataRangeSet.empty.addRange (size 11) (size 2) with
          | .ok value => pure value
          | .error reason => return .error (.rangeSet reason) state
        let tracker := session.refTracking.getD RefTracking.empty
        let tracker := tracker.track 42 (fun _ => session.path.push .deref)
        return .ok { session with dataBytes := some data, refTracking := some tracker } state
      return .ok session state
    allocationRange := fun place state =>
      .ok (if place == 0 then some (size 10, size 5) else none)
        (state.push s!"allocation-range:{place}")
    writeUninit := fun _ range state =>
      .ok () (state.push s!"uninit:{range.start.bytes}:{range.size.bytes}")
    trackedPlace := fun key state => .ok key (state.push s!"tracked:{key}")
  }
  match validatePlace placeHooks 0 "Root" true none
      (some RefTracking.empty) true #[] with
  | .ok () events =>
    check (events == #["stored", "visit:0:dangle=false", "allocation-range:0",
      "uninit:0:1", "uninit:3:2", "tracked:42", "visit:42:dangle=true"])
      "validate_place initialization, padding, or recursive-reference order diverged"
  | other => throw (IO.userError s!"validate_place driver mismatch: {reprStr other}")

  let bad : BadBytesAccess := ⟨allocRange (size 2) (size 4), allocRange (size 3) (size 2)⟩
  check (Validity.classifyReadError .integer (.invalidUninitBytes (some bad)) ==
      some (.uninitialized .integer (some bad))) "uninitialized read was not classified"
  check (Validity.classifyReadError .reference (.readPointerAsInt (some bad)) ==
      some (.pointerAsInt .reference (some bad))) "pointer-as-int read was not classified"
  check (Validity.classifyReadError .rawPointer (.readPartialPointer (size 7)) ==
      some (.partialPointer (size 7))) "partial pointer read was not classified"
  check (Validity.classifyReadError .integer .readOnlyAllocation == none)
    "non-validity allocation failures were incorrectly classified"

  IO.println "primitive validity classifications and delegation checks passed"
