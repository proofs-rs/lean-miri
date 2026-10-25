import Miri.Input.Decoder
import Miri.Input.AllocationImage

open Miri Input Memory ABI
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let path ← match args with | p :: _ => pure p | [] => throw (IO.userError "expected compiler target fixture")
  let doc ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument doc.document).mapError toString)
  let target := runtime.target
  let width ← must ((target.pointerSizeIn target.defaultAddressSpace).mapError toString)
  unless width.bytes == 8 do throw (IO.userError "synthetic relocation fixture requires the actual 64-bit target")
  let initial : MemoryState CtfeProvenance Unit Unit := { MemoryState.empty with nextAllocId := 100 }
  let registered := MemoryLifecycle.registerImportedGlobal initial () 77 .memory (.ofBytes 32) .ONE
  let id ← must (registered.outcome.mapError toString)
  let prov ← must ((CtfeProvenance.fromAllocId id).mapError reprStr)
  let encoded := if target.base.endian == .little then "0600000000000000" else "0000000000000006"
  let relocation : Relocation := ⟨0, 77, encoded, true, true, prov.asImmutable⟩
  let source : AllocationMemory := ⟨8, 8, .immutable, encoded, #[⟨false, 0, 8⟩], #[relocation]⟩
  let allocation ← must (AllocationImage.decode target registered.memory source)
  check (allocation.mutability == .Not && allocation.provenanceMap.ptrs.size == 1) "raw import normalized immutable/uninitialized pointer state"
  let initialized ← must ((allocation.initializationMask.get .ZERO).mapError toString)
  check (!initialized) "raw import initialized pointer bytes"
  let raw ← must ((allocation.inspectWithUninitAndPtrOutsideInterpreter 0 8).mapError toString)
  check (raw == (if target.base.endian == .little then #[6,0,0,0,0,0,0,0] else #[0,0,0,0,0,0,0,6])) "raw import changed pointer encoding"
  check (!(allocation.readScalar target.base (allocRange .ZERO width) true).isOk) "uninitialized imported pointer became readable"
  check (!(AllocationImage.decode target (MemoryState.empty : MemoryState CtfeProvenance Unit Unit) source).isOk) "missing relocation target succeeded"
  check (!(AllocationImage.decode target registered.memory { source with initializationRanges := #[⟨true,1,8⟩] }).isOk) "initialization gap succeeded"
  check (!(AllocationImage.decode target registered.memory { source with relocations := #[relocation, relocation] }).isOk) "duplicate relocation succeeded"
  check (!(AllocationImage.decode target registered.memory { source with relocations := #[{ relocation with sharedRef := false }] }).isOk) "invalid immutable/shared provenance was normalized"
  check (!(AllocationImage.decode target registered.memory { source with relocations := #[{ relocation with targetOffsetEncodedBytes := "00" }] }).isOk) "wrong pointer encoding width succeeded"
  check (!(AllocationImage.decode target registered.memory { source with alignBytes := 0 }).isOk) "zero alignment was normalized to alignment one"
  let wrongMask := InitMask.new (.ofBytes 7) true
  check (!(Allocation.fromCompilerImage raw .ONE .Not wrongMask ProvenanceMap.new width).isOk) "wrong init mask length accepted"
  let pointers ← must ((ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 7, prov)]).mapError reprStr)
  check (!(Allocation.fromCompilerImage raw .ONE .Not (InitMask.new width true) pointers width).isOk) "out-of-bounds pointer provenance accepted"
  IO.println "compiler image invariants passed: exact uninitialized pointer storage retained, unreadability preserved, malformed masks/flags/relocations/metadata rejected"
