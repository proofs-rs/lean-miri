import duplicate_prefix.RetagReferencePlace
import Miri.Interpreter.TypedMemoryProviders

namespace DuplicatePrefix.S05IntegerReferenceBacking
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false

/-- Raw integer reference bits retain no provenance on the fixed 64-bit target.
An explicit integer-to-pointer cast is a different operation. -/
theorem integer_pointer (target : TargetDataLayout) (width : target.pointerWidth = .w64)
    (address : UInt64) :
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 address) : Scalar Provenance).toPointer target =
      .ok (Pointer.withoutProvenance address) :=
  RetagReferencePlace.integer_to_pointer target address width

/-- Canonical resolution does not consult address caches for absent provenance. -/
theorem unresolved {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (address : UInt64) (size : Int)
    (lower : -9223372036854775808 ≤ size) (upper : size < 9223372036854775808) :
    TypedMemoryProviders.resolvePointer pointers memory (Pointer.withoutProvenance address) size machine =
      .ok (.error address) machine := by
  have outside : ¬(size < -9223372036854775808 ∨ 9223372036854775808 ≤ size) := by omega
  simp [TypedMemoryProviders.resolvePointer,Pointer.withoutProvenance,outside,
    Size.ofBytes,pure,EStateM.pure]


/-- The positive-byte access leaf rejects an unresolved integer address before
allocation lookup. This is a backing lemma, not a complete reference validator. -/
theorem positive_access (target : PointerArithmetic) (lookup : LiveAllocationLookup)
    (address : UInt64) (size : Int) (positive : 0 < size)
    (signed : size < 9223372036854775808) :
    checkAndDerefPtr (Prov := Provenance) (ProvExtra := ProvenanceExtra) target
      (Pointer.withoutProvenance address) size (.dereferenceable "pointer")
      (fun _ _ => .error address) lookup =
      .error (.danglingIntegerPointer address size (.dereferenceable "pointer")) := by
  have lower : (-9223372036854775808 : Int) ≤ size := by omega
  have nonzero : size ≠ 0 := by omega
  have throwing {A : Type} (error : AccessError) : (throw error : Except AccessError A) = .error error := rfl
  unfold checkAndDerefPtr
  unfold_internal ".fitsI64"
  simp [lower,signed,nonzero,bind,Except.bind,throwing]


/-- The production validation observer classifies this access failure as UB.
Neither ordinary-input coverage nor a whole-call failure follows. -/
theorem classified_as_ub (path : ValidationPath)
    (kind : SafePointerKind) (address : UInt64) (size : Int) :
    RunLoop.reportsUB (ValidityVisitor.classifyPointerAccessError path kind
      (.danglingIntegerPointer address size (.dereferenceable "pointer"))) = true := by
  simp [ValidityVisitor.classifyPointerAccessError,RunLoop.reportsUB]

end DuplicatePrefix.S05IntegerReferenceBacking

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05IntegerReferenceBacking." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved integer backing dependency {dependency}"
