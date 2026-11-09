import Miri.Input.RuntimeMetadata
import Miri.Interpreter.LayoutCompat

/-! Internal connection from compiler input records to the source ABI
compatibility port. Missing compiler predicates/normalization are mandatory
query obligations, never heuristic equivalence based on size or debug strings. -/
namespace Miri.Input.CallCompatibility
open Miri.ABI Miri.Interpreter
abbrev Result := Except RuntimeMetadataError
private def require (value : Option A) (path : String) : Result A := RuntimeMetadata.require value path
private def invalid (path message : String) : RuntimeMetadataError := .invalid path message

def attributes (source : AbiAttributes) : Result ArgAttributes := do
  if source.regularBits >= 2^16 then throw (invalid "regular attributes" "u16 overflow")
  let regular := UInt16.ofNat source.regularBits
  if source.inRegister != (regular &&& 64 == 64) then throw (invalid "InReg" "redundant attribute mismatch")
  let extension := match source.argExtension with
    | .none => ArgExtension.None
    | .zeroExtend => .Zext
    | .signExtend => .Sext
  let align ← source.pointeeAlignBytes.mapM RuntimeMetadata.alignment
  return ⟨regular,extension,← RuntimeMetadata.size source.pointeeSizeBytes,align⟩

private def hintPrimitive (source : AbiRegisterHint) : Result Primitive := do
  match source with
  | .integer (.known kind) signed => return .Int (← RuntimeMetadata.integer kind) signed
  | .float kind => return .Float (← RuntimeMetadata.float kind)
  | .pointer addressSpace => return .Pointer ⟨← RuntimeMetadata.u32 addressSpace "hint address space"⟩

def register (source : AbiRegister) : Result Reg := do
  let kind ← match source.kind with
    | .integer => pure RegKind.Integer | .float => pure .Float | .ppcF128 => pure .PpcF128
    | .vector => pure (RegKind.Vector (hintVectorElem := ← hintPrimitive (← require source.hintElement "register hint")))
  return ⟨kind,Size.fromBits (← RuntimeMetadata.u64 source.sizeBits "register bits")⟩

def castTarget (source : AbiCastTarget) : Result CastTarget := do
  if source.prefixRegisters.size > 8 then throw (invalid "cast prefix" "exceeds source ArrayVec capacity")
  return {
    «prefix» := ← source.prefixRegisters.mapM register
    restOffset := ← source.restOffsetBytes.mapM RuntimeMetadata.size
    rest := ⟨← register source.restRegister,← RuntimeMetadata.size source.restTotalBytes,source.restIsConsecutive⟩
    attrs := ← attributes source.attributes }

def passMode (source : AbiPassMode) : Result PassMode := do
  let expected ← match source.kind with
    | .ignore | .cast => pure 0
    | .direct | .indirect => pure 1
    | .pair | .indirectUnsized => pure 2
  if source.attributes.size != expected then throw (invalid "pass attributes" "arity mismatch")
  let attrsAt (index : Nat) := do attributes (← require source.attributes[index]? s!"pass attributes {index}")
  match source.kind with
  | .ignore => pure .Ignore
  | .direct => return .Direct (← attrsAt 0)
  | .pair => return .Pair (← attrsAt 0) (← attrsAt 1)
  | .cast =>
    let pad ← require source.padI32Count "cast.pad_i32_count"
    if pad >= 256 then throw (invalid "cast padding" "u8 overflow")
    return .Cast (UInt8.ofNat pad) (← castTarget (← require source.castTarget "cast.target"))
  | .indirect =>
    let mode ← require source.indirectMode "indirect mode"
    let mode := match mode with
      | .pointer => IndirectMode.Pointer | .onStack => .OnStack
      | .amdgpuKernelArgument => .AmdgpuKernelArg
    let space ← source.addressSpace.mapM (fun n => AddressSpace.mk <$> RuntimeMetadata.u32 n "indirect address space")
    return .Indirect (← attrsAt 0) space mode
  | .indirectUnsized => return .IndirectUnsized (← attrsAt 0) (← attrsAt 1)

def argument (runtime : RuntimeMetadata) (source : AbiArgument) : Result (ArgAbi TypeId) := do
  let _ ← runtime.node source.typeId
  let layout ← runtime.layoutById source.layoutId
  return ⟨⟨source.typeId,layout⟩,← passMode source.mode⟩

/-- These source compiler queries are absent or only partially represented by
the exporter. Each consumer must supply exact-key evidence or explicit errors.
In particular, item names are not reconstructed from diagnostic def paths. -/
structure Evidence (S : Type) where
  eraseUnsafeBinder : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId
  normalize : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId
  reprEqualUpToSeed : TypeId → TypeId → Miri.Interpreter.LayoutCompat.M S Bool
  itemName : TypeId → Miri.Interpreter.LayoutCompat.M S String
  nonnullOptimizationGuaranteed : TypeId → Miri.Interpreter.LayoutCompat.M S Bool
  isGlobalBox : TypeId → Miri.Interpreter.LayoutCompat.M S Bool
  boxedType : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId
  pointerMetadataType : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId

private def lift (value : Result A) : Miri.Interpreter.LayoutCompat.M S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported (toString e))
def kind (runtime : RuntimeMetadata) (id : TypeId) : Result (Miri.Interpreter.LayoutCompat.TypeKind TypeId) := do
  match (← runtime.node id).shape with
  | .tuple _ => pure .tuple | .never => pure .never | .functionDefinition .. => pure .functionDefinition
  | .closure .. => pure .closure | .coroutine .. => pure .coroutine | .coroutineClosure .. => pure .coroutineClosure
  | .array element .. => pure (.array element)
  | .adt _ => pure .adt
  | .patternType base _ => pure (.pattern base)
  | .unsafeBinder .. => pure .unsafeBinder | .alias .. => pure .alias
  | .reference pointee .. => pure (.reference pointee)
  | .rawPointer pointee _ => pure (.rawPointer pointee)
  | .functionPointer .. => pure .functionPointer
  | .int (.known kind) | .uint (.known kind) => pure (.integer kind)
  | .char => pure .char
  | .bool | .float _ | .foreign _ | .str | .slice _ | .dynamicTraitObject .. => pure .other

def adt (runtime : RuntimeMetadata) (id : TypeId) : Result (Miri.Interpreter.LayoutCompat.AdtInfo TypeId) := do
  let .adt data := (← runtime.node id).shape | throw (.unsupported "non-ADT compiler query")
  let kind := match data.kind with
    | .structKind => Miri.Interpreter.LayoutCompat.AdtKind.Struct | .unionKind => .Union | .enumKind => .Enum
  let mut variants := #[]
  for variant in data.variants do
    unless variant.index == variants.size do throw (invalid "ADT variant" "noncontiguous indices")
    let mut fields := #[]
    for field in variant.fields do
      unless field.index == fields.size do throw (invalid "ADT field" "noncontiguous indices")
      fields := fields.push ({ name := field.name, ty := field.typeId } : Miri.Interpreter.LayoutCompat.Field TypeId)
    variants := variants.push fields
  pure ⟨kind,data.representation.transparent,data.representation.c,data.representation.rust,variants⟩

private def unitLayout (runtime : RuntimeMetadata) : Result (TyAndLayout TypeId) := do
  let mut found := none
  for node in runtime.source.types do
    if let .tuple elements := node.shape then
      if elements.isEmpty then
        if found.isSome then throw (invalid "unit type" "multiple compiler identities")
        found := some node.id
  runtime.lookup (← require found "compiler unit type")

/-- Connect the source algorithm to canonical records while keeping every
missing compiler query explicit and preserving the caller's effect state. -/
def queries (runtime : RuntimeMetadata) (evidence : Evidence S) :
    Miri.Interpreter.LayoutCompat.Queries TypeId S := {
  target := runtime.target
  kind := fun id => lift (kind runtime id)
  adt := fun id => lift (adt runtime id)
  field := fun parent index => lift (runtime.field parent index)
  layoutOf := fun id => lift (runtime.lookup id)
  unitLayout := lift (unitLayout runtime)
  eraseUnsafeBinder := evidence.eraseUnsafeBinder, normalize := evidence.normalize
  reprEqualUpToSeed := evidence.reprEqualUpToSeed, itemName := evidence.itemName
  nonnullOptimizationGuaranteed := evidence.nonnullOptimizationGuaranteed
  isGlobalBox := evidence.isGlobalBox, boxedType := evidence.boxedType
  pointerMetadataType := evidence.pointerMetadataType }

def checkArgumentCompat (runtime : RuntimeMetadata) (evidence : Evidence S) (fuel : Nat)
    (caller callee : AbiArgument) : Miri.Interpreter.LayoutCompat.M S Bool := do
  let caller ← lift (argument runtime caller)
  let callee ← lift (argument runtime callee)
  Miri.Interpreter.LayoutCompat.checkArgumentCompat (queries runtime evidence) fuel caller callee
end Miri.Input.CallCompatibility
