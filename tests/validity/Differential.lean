import Miri.Memory.Validity

open Miri.ABI
open Miri.Memory
open Miri.Memory.Validity

private def size (bytes : Nat) : Size := Size.ofBytes (UInt64.ofNat bytes)
private def bits (value : Nat) : U128 := BitVec.ofNat 128 value
private def scalarLayout (lo hi : Nat) : ScalarValidityLayout :=
  ⟨size 1, ⟨bits lo, bits hi⟩⟩
private def pointerLayout (lo hi : Nat) : ScalarValidityLayout :=
  ⟨size 8, ⟨bits lo, bits hi⟩⟩

private def nullCallback (answer : Except String Bool) :
    Scalar CtfeProvenance → Array String →
      EStateM.Result String (Array String) Bool :=
  fun _ state => match answer with
    | .ok value => .ok value (state.push "null")
    | .error reason => .error reason (state.push "null-error")

private def showError (error : ValidityError String) : String :=
  match error with
  | .failure failure =>
    match Validity.formatFailure failure with
    | .ok message => s!"INVALID:{message}"
    | .error reason => s!"FORMAT:{reason}"
  | .pathFailure _ failure =>
    match Validity.formatFailure failure with
    | .ok message => s!"INVALID:{message}"
    | .error reason => s!"FORMAT:{reason}"
  | .scalar reason => s!"SCALAR:{reason}"
  | .range reason => s!"RANGE:{reprStr reason}"
  | .rangeSet reason => s!"RANGESET:{reprStr reason}"
  | .padding reason => s!"PADDING:{reprStr reason}"
  | .pathInvariant reason => s!"PATH:{reprStr reason}"
  | .unionRange reason => s!"UNION:{reprStr reason}"
  | .walkInvariant reason => s!"WALK:{reason}"
  | .rangeInvariant reason => s!"INVARIANT:{reason}"
  | .machine reason => s!"MACHINE:{reason}"

private def runScalar (tag : String) (scalar : Scalar CtfeProvenance)
    (range : ScalarValidityLayout) (answer : Except String Bool) : IO Unit := do
  match Validity.checkScalar range scalar (nullCallback answer) #[] with
  | .ok () events => IO.println s!"V {tag} OK:{events.size}"
  | .error reason events => IO.println s!"V {tag} {showError reason}:{events.size}"

inductive AddressProvenance where
  | address
  deriving DecidableEq, Repr

instance : PointerProvenance AddressProvenance where
  offsetIsAddr := true
  wildcard := none
  getAllocId := fun _ => none

private def runAddress (tag : String) (scalar : Scalar AddressProvenance)
    (range : ScalarValidityLayout) : IO Unit := do
  let noHook : Scalar AddressProvenance → Array String →
      EStateM.Result String (Array String) Bool := fun _ events =>
    .error "address provenance unexpectedly queried for null" events
  match Validity.checkScalar range scalar noHook #[] with
  | .ok () events => IO.println s!"V {tag} OK:{events.size}"
  | .error reason events => IO.println s!"V {tag} {showError reason}:{events.size}"

def main : IO Unit := do
  let mut data := DataRangeSet.empty
  for (start, count) in #[(8, 4), (0, 4), (4, 4), (10, 3), (20, 2), (100, 0)] do
    data ← match data.addRange (size start) (size count) with
      | .ok updated => pure updated
      | .error reason => throw (IO.userError s!"data-range insertion failed: {reprStr reason}")
  let encoded := String.intercalate "," (data.toArray.toList.map fun range =>
    s!"{range.start.bytes}:{range.size.bytes}")
  IO.println s!"R {encoded}"
  let sourcePath : ValidationPath := ⟨"Root", #[
    .field "field", .enumTag, .variant "Variant", .coroutineTag,
    .coroutineState 7, .capturedVar "capture", .tupleElem 2, .arrayElem 3,
    .deref, .dynDowncast "Concrete", .vtable]⟩
  IO.println s!"P {sourcePath.render}"

  let seeded : RefTracking Nat String := .start 11 "root"
  match seeded.todo.back? with
  | some (key, path) => IO.println s!"T_SEED {key}:{path}:{seeded.seen.contains key}:{seeded.todo.size}"
  | none => throw (IO.userError "reference tracker start did not queue its initial key")

  let tracking : RefTracking Nat String := .empty
  let tracking := tracking.track 2 (fun _ => "two")
  let tracking := tracking.track 2 (fun _ => "duplicate")
  let tracking := tracking.track 5 (fun _ => "five")
  let some ((firstKey, firstPath), tracking) := tracking.next
    | throw (IO.userError "reference tracker lost its first pending item")
  let some ((secondKey, secondPath), tracking) := tracking.next
    | throw (IO.userError "reference tracker lost its second pending item")
  match tracking.next with
  | none => pure ()
  | some _ => throw (IO.userError "reference tracker should be empty after both pops")
  let tracking := tracking.track 2 (fun _ => "again")
  IO.println s!"T {firstKey}:{firstPath}:{secondKey}:{secondPath}:{tracking.seen.size}"
  IO.println s!"T_EMPTY true:{tracking.todo.size}"

  let target : TargetDataLayout := ⟨.little, .w64⟩
  let restricted := scalarLayout 1 255
  let valid ← match Scalar.fromUInt (BitVec.ofNat 128 17) (size 1) with
    | .ok scalar => pure scalar
    | .error reason => throw (IO.userError s!"valid scalar construction failed: {reason}")
  let invalid ← match Scalar.fromUInt (BitVec.ofNat 128 0) (size 1) with
    | .ok scalar => pure scalar
    | .error reason => throw (IO.userError s!"invalid scalar construction failed: {reason}")
  runScalar "int_valid" valid restricted (.ok false)
  runScalar "int_invalid" invalid restricted (.ok false)

  let id ← match AllocId.ofUInt64 1 with
    | some id => pure id
    | none => throw (IO.userError "validity provenance ID was rejected")
  let prov ← match CtfeProvenance.fromAllocId id with
    | .ok prov => pure prov
    | .error reason => throw (IO.userError s!"validity provenance failed: {reprStr reason}")
  let relative := Scalar.fromPointer target (Pointer.new prov (size 17))
  let maxPointer := 18446744073709551615
  runScalar "relative_nonnull" relative (pointerLayout 1 maxPointer) (.ok false)
  runScalar "relative_maybe_null" relative (pointerLayout 1 maxPointer) (.ok true)
  runScalar "relative_null_error" relative (pointerLayout 1 maxPointer) (.error "null-query failed")
  runScalar "relative_unknown_range" relative (pointerLayout 2 maxPointer) (.ok false)
  runScalar "relative_full_range" relative (pointerLayout 0 maxPointer) (.ok false)
  runScalar "wrapped_contains" (← match Scalar.fromUInt (BitVec.ofNat 128 0) (size 1) with
    | .ok scalar => pure scalar
    | .error reason => throw (IO.userError s!"wrapped scalar failed: {reason}"))
    (scalarLayout 254 2) (.ok false)
  runScalar "wrapped_rejects" (← match Scalar.fromUInt (BitVec.ofNat 128 3) (size 1) with
    | .ok scalar => pure scalar
    | .error reason => throw (IO.userError s!"wrapped scalar failed: {reason}"))
    (scalarLayout 254 2) (.ok false)

  runAddress "absolute_valid" (Scalar.fromPointer target (Pointer.new .address (size 17)))
    (pointerLayout 1 maxPointer)
  runAddress "absolute_invalid" (Scalar.fromPointer target (Pointer.new .address (size 0)))
    (pointerLayout 1 maxPointer)

  for (tag, range) in #[
      ("range_wrapping", ⟨bits 254, bits 2⟩),
      ("range_single", ⟨bits 8, bits 8⟩),
      ("range_lower", ⟨bits 0, bits 9⟩),
      ("range_upper", ⟨bits 10, bits 255⟩),
      ("range_middle", ⟨bits 10, bits 20⟩)] do
    match Validity.formatRange range (bits 255) with
    | .ok formatted => IO.println s!"F {tag} {formatted}"
    | .error reason => throw (IO.userError s!"range formatting failed: {reason}")
