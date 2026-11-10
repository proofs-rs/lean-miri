import Miri.Input.AllocationImage
import Miri.Interpreter.Projection

/-! Pinned operand.rs::const_val_to_op for resolved executable MIR.
Compiler normalization and evaluation happen before import. Global conversion
retains memory.rs classification and its TLS/extern distinction; machine hooks
remain stateful and fallible because root adjustment allocates runtime provenance.
-/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

inductive ConstantError where
  | metadata (message : String)
  | query (message : String)
  | scalar (error : ScalarError)
  | immediate (error : ImmediateError)
  | globalAccess (error : GlobalAccessError)
  | memoryAccess (error : MemoryAccessError)
  | tlsConstantPointer (id : AllocId)
  | invariant (message : String)
  deriving Repr

structure ConstantState (P E K H : Type) where
  memory : MemoryState P E K
  hooks : H

abbrev ConstantM (P E K H A : Type) := EStateM ConstantError (ConstantState P E K H) A

/-- Value conversion requires allocation root and extern-static operations. -/
structure ConstantValueQueries (P E K H : Type) where
  adjustGlobalRootPointer : Pointer CtfeProvenance → ConstantM P E K H (Pointer P)
  externStaticPointer : MIR.DefId → ConstantM P E K H (Pointer P)

private def liftResult (value : Except ConstantError A) : ConstantM P E K H A :=
  match value with | .ok value => pure value | .error error => throw error

private def metadata (value : Except String A) : ConstantM P E K H A :=
  liftResult (value.mapError .metadata)

private def size (n : Nat) : ConstantM P E K H Size := do
  if n ≥ 2^64 then throw (.metadata "constant offset/width exceeds u64")
  pure (.ofBytes (UInt64.ofNat n))

/-- Source global_root_pointer classification happens before the machine root
pointer adjustment. Constants cannot point to TLS; foreign statics require the
extern-static hook instead of normal root adjustment. -/
def valueGlobalRootPointer (queries : ConstantValueQueries P E K H)
    (pointer : Pointer CtfeProvenance) : ConstantM P E K H (Pointer P) := do
  let memory := (← EStateM.get).memory
  match memory.findGlobal? pointer.provenance.allocId with
  | some global =>
    match global.payload with
    | some (.static definition isStatic threadLocal foreignItem) =>
      unless isStatic do throw (.invariant "compiler static allocation is not a static")
      if threadLocal then throw (.tlsConstantPointer global.allocId)
      if foreignItem then return ← queries.externStaticPointer definition
    | _ => pure ()
  | none =>
    unless memory.hasExtraFunctionId pointer.provenance.allocId ||
        memory.hasVaListId pointer.provenance.allocId do
      throw (.globalAccess (.notFound pointer.provenance.allocId))
  queries.adjustGlobalRootPointer pointer

private def scalarValue (target : RuntimeTargetDataLayout) (queries : ConstantValueQueries P E K H)
    (value : MIR.ScalarValue) : ConstantM P E K H (Scalar P) := do
  match value with
  | .Int bits width =>
    unless bits < 2^128 do throw (.metadata "scalar constant exceeds u128")
    liftResult ((Scalar.fromUInt (BitVec.ofNat 128 bits) (← size width)).mapError .scalar)
  | .Ptr (.Allocation allocation offset immutable sharedRef) =>
    let memory := (← EStateM.get).memory
    let provenance ← metadata (Input.AllocationImage.provenance memory allocation immutable sharedRef)
    let adjusted ← valueGlobalRootPointer queries (.new provenance (← size offset))
    pure (Scalar.fromPointer target.base adjusted)
  | .Ptr (.Address address width) =>
    let pointerSize ← metadata ((target.pointerSizeIn target.defaultAddressSpace).mapError toString)
    unless width == pointerSize.bytes.toNat && address < 2^(8*width) do
      throw (.metadata "provenance-free pointer width/address mismatch")
    liftResult ((Scalar.fromUInt (BitVec.ofNat 128 address) pointerSize).mapError .scalar)

/-- Source const_val_to_op. Indirect and slice constants carry immutable/shared
CTFE roots; scalar pointers retain their own exported flags. Constructing an
indirect operand does not dereference it or trigger a global initializer. -/
def valueToOpWithLayout (runtime : Input.RuntimeMetadata) (queries : ConstantValueQueries P E K H)
    (value : MIR.ConstValue) (ty : MIR.TyId) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → ConstantM P E K H Bool)) :
    ConstantM P E K H (OpTy P) := do
  let layout ← match known with
    | none => metadata ((runtime.lookup ty).mapError toString)
    | some known => do
      if let some check := checkKnown then
        let computed ← metadata ((runtime.lookup ty).mapError toString)
        unless ← check computed known do
          throw (.invariant "known constant layout differs from compiler layout")
      pure known
  match value with
  | .Indirect allocation offset =>
    unless layout.layout.isSized do throw (.invariant "ptr_to_mplace requires a sized layout")
    let provenance ← metadata (Input.AllocationImage.provenance (← EStateM.get).memory allocation true true)
    let pointer ← valueGlobalRootPointer queries (.new provenance (← size offset))
    pure ⟨.indirect ⟨(⟨pointer.offset, some pointer.provenance⟩ : Pointer (Option P)), .none, none⟩, layout⟩
  | .Scalar scalar => return ⟨.immediate (.scalar (← scalarValue runtime.target queries scalar)), layout⟩
  | .ZeroSized => pure ⟨.immediate .uninit, layout⟩
  | .Slice allocation length =>
    let provenance ← metadata (Input.AllocationImage.provenance (← EStateM.get).memory allocation true true)
    let pointer ← valueGlobalRootPointer queries (.new provenance .ZERO)
    let length ← size length
    let immediate ← liftResult ((Immediate.newSlice ((⟨pointer.offset, some pointer.provenance⟩ : Pointer (Option P))) length.bytes runtime.target.base).mapError .immediate)
    pure ⟨.immediate immediate, layout⟩

def constValueToOp (runtime : Input.RuntimeMetadata) (queries : ConstantValueQueries P E K H)
    (value : MIR.ConstValue) (ty : MIR.TyId) : ConstantM P E K H (OpTy P) :=
  valueToOpWithLayout runtime queries value ty none none

/-- Connect subsequent memory access to source get_global_alloc/get_alloc_raw
including initializer→before_access_global→adjust hooks and owned-only caching. -/
def constantGetAllocRaw [DecidableEq K] (id : AllocId) (globalKind : Option K)
    (hooks : GlobalAllocationHooks P E K H) : ConstantM P E K H (Allocation P E) := do
  let state ← EStateM.get
  let result := MemoryLifecycle.getAllocRaw state.memory state.hooks id globalKind hooks
  EStateM.set { state with memory := result.memory, hooks := result.hooks }
  liftResult (result.outcome.mapError .memoryAccess)

end Miri.Interpreter
