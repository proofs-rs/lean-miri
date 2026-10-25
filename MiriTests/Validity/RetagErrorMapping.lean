import Miri.Interpreter.ValidityVisitor
import Miri.Interpreter.RunLoop

open Miri.Interpreter
open Miri.ABI
open Miri.Memory
open Miri.Memory.Validity

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw <| IO.userError message

private def failedAt (expectedError : StepError) (expectedState : Nat)
    (result : EStateM.Result StepError Nat Unit) : Bool :=
  match result with
  | .error error state => error == expectedError && state == expectedState
  | .ok _ _ => false

def main : IO Unit := do
  let fieldPath : ValidationPath := ⟨"Root", #[.field "inner", .tupleElem 2]⟩
  check
    (ValidityVisitor.classifyRetagError fieldPath (.reference true)
      .retagWriteToReadOnly ==
      .undefinedBehavior "validation.inner.2: encountered mutable reference pointing to read-only memory")
    "write-to-read-only retag error did not become a path-qualified validity failure"
  check
    (ValidityVisitor.classifyRetagError fieldPath .box
      .retagWriteToReadOnly ==
      .undefinedBehavior "validation.inner.2: encountered box pointing to read-only memory")
    "box retag error did not preserve the source diagnostic kind"
  let retagFailure : EStateM StepError Nat Unit := fun state =>
    .error .retagWriteToReadOnly (state + 1)
  check
    (failedAt (.undefinedBehavior "validation.inner.2: encountered mutable reference pointing to read-only memory")
      42 (ValidityVisitor.mapRetagOutcome fieldPath (.reference true) retagFailure 41))
    "retag failure classification discarded the callback successor state"
  check
    (Miri.Interpreter.RunLoop.reportsUB .retagWriteToReadOnly)
    "typed retag read-only error was not classified as undefined behavior"
  check
    (ValidityVisitor.classifyRetagError fieldPath (.reference false)
      (.machineStop "tag is protected") ==
      .machineStop "tag is protected; while retagging field .inner.2")
    "machine-stop retag error did not receive the validation path"
  let machineStop : EStateM StepError Nat Unit := fun state =>
    .error (.machineStop "tag is protected") (state + 2)
  check
    (failedAt (.machineStop "tag is protected; while retagging field .inner.2")
      43 (ValidityVisitor.mapRetagOutcome fieldPath (.reference false) machineStop 41))
    "machine-stop path mapping discarded the callback successor state"
  check
    (ValidityVisitor.classifyRetagError ⟨"Root", #[]⟩ .box (.machineStop "stop") ==
      .machineStop "stop")
    "root machine-stop diagnostic was changed despite having no projection path"
  check
    (ValidityVisitor.classifyRetagError fieldPath .box (.callback "other") ==
      .callback "other")
    "unrelated typed retag error was changed"
  check
    (ValidityVisitor.classifyPointerAccessError fieldPath (.reference true)
      (.danglingIntegerPointer 0 4 (.dereferenceable "pointer")) ==
      .undefinedBehavior "validation.inner.2: encountered a null reference")
    "null dereference error did not become a path-qualified validity failure"
  check
    (ValidityVisitor.classifyPointerAccessError fieldPath (.reference false)
      (.danglingIntegerPointer 4096 4 (.dereferenceable "pointer")) ==
      .undefinedBehavior "validation.inner.2: encountered a dangling reference (address 4096 has no provenance)")
    "non-null integer pointer error did not retain its no-provenance distinction"
  check
    (ValidityVisitor.classifyPointerAccessError fieldPath .box
      (.pointerOutOfBounds (⟨1, by decide⟩ : AllocId) (Size.ofBytes 8) 7 4
        (.dereferenceable "pointer")) ==
      .undefinedBehavior "validation.inner.2: encountered a dangling box (going beyond the bounds of its allocation)")
    "out-of-bounds dereference error did not become the source validity failure"
  check
    (ValidityVisitor.classifyPointerAccessError fieldPath .box
      (.allocationLookup (.deadAllocation ⟨1, by decide⟩)) ==
      .undefinedBehavior "validation.inner.2: encountered a dangling box (use-after-free)")
    "use-after-free dereference error did not become the source validity failure"
  let misalignment : Misalignment := ⟨Align.ONE, Align.EIGHT⟩
  check
    (ValidityVisitor.classifyPointerAlignmentError fieldPath (.reference true) misalignment ==
      .undefinedBehavior "validation.inner.2: encountered an unaligned reference (required 8 byte alignment but found 1)")
    "misaligned mutable reference did not retain source wording, path, or byte counts"
  check
    (ValidityVisitor.classifyPointerAlignmentError fieldPath .box misalignment ==
      .undefinedBehavior "validation.inner.2: encountered an unaligned box (required 8 byte alignment but found 1)")
    "misaligned Box did not retain its source kind"
  let alignmentFailure : EStateM StepError Nat (Except Misalignment Unit) := fun state =>
    .ok (.error misalignment) (state + 5)
  check
    (failedAt (.undefinedBehavior "validation.inner.2: encountered an unaligned reference (required 8 byte alignment but found 1)")
      46 (ValidityVisitor.mapPointerAlignmentOutcome fieldPath (.reference true) alignmentFailure 41))
    "alignment UB mapping discarded the alignment callback's successor state"
  let unrelatedFailure : EStateM StepError Nat (Except Misalignment Unit) := fun state =>
    .error (.callback "alignment resolver unavailable") (state + 7)
  check
    (failedAt (.callback "alignment resolver unavailable") 48
      (ValidityVisitor.mapPointerAlignmentOutcome fieldPath .box unrelatedFailure 41))
    "non-alignment failure classification or successor state was changed"
  let alignmentError : AccessError := .alignmentCheckFailed ⟨Miri.ABI.Align.ONE, Miri.ABI.Align.ONE⟩
  check
    (ValidityVisitor.classifyPointerAccessError fieldPath .box alignmentError ==
      Miri.Interpreter.MemoryErrors.access alignmentError)
    "non-source-remapped access failure diverged from canonical memory error classification"
  IO.println "Validity retag error mapping: PASS"
