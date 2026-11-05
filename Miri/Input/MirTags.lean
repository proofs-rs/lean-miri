import Miri.Input.Model.Types

namespace Miri.Input.DecoderValues

def statementVariant (tag : String) : StatementVariant :=
  match tag with
  | "Assign" => .assign
  | "FakeRead" => .fakeRead
  | "SetDiscriminant" => .setDiscriminant
  | "StorageLive" => .storageLive
  | "StorageDead" => .storageDead
  | "PlaceMention" => .placeMention
  | "AscribeUserType" => .ascribeUserType
  | "Coverage" => .coverage
  | "Intrinsic" => .intrinsic
  | "ConstEvalCounter" => .constEvalCounter
  | "Nop" => .nop
  | "BackwardIncompatibleDropHint" => .backwardIncompatibleDropHint
  | other => .unknown other

def terminatorVariant (tag : String) : TerminatorVariant :=
  match tag with
  | "Goto" => .goto
  | "SwitchInt" => .switchInt
  | "UnwindResume" => .unwindResume
  | "UnwindTerminate" => .unwindTerminate
  | "Return" => .return
  | "Unreachable" => .unreachable
  | "Drop" => .drop
  | "Call" => .call
  | "TailCall" => .tailCall
  | "Assert" => .assert
  | "Yield" => .yield
  | "CoroutineDrop" => .coroutineDrop
  | "FalseEdge" => .falseEdge
  | "FalseUnwind" => .falseUnwind
  | "InlineAsm" => .inlineAsm
  | other => .unknown other

def rvalueVariant (tag : String) : RvalueVariant :=
  match tag with
  | "Use" => .use
  | "Repeat" => .repeat
  | "Ref" => .ref
  | "ThreadLocalRef" => .threadLocalRef
  | "RawPtr" => .rawPtr
  | "Cast" => .cast
  | "BinaryOp" => .binaryOp
  | "UnaryOp" => .unaryOp
  | "Discriminant" => .discriminant
  | "Aggregate" => .aggregate
  | "CopyForDeref" => .copyForDeref
  | "WrapUnsafeBinder" => .wrapUnsafeBinder
  | "Reborrow" => .reborrow
  | other => .unknown other

def operandVariant (tag : String) : OperandVariant :=
  match tag with
  | "Copy" => .copy
  | "Move" => .move
  | "Constant" => .constant
  | "RuntimeChecks" => .runtimeChecks
  | other => .unknown other

def projectionVariant (tag : String) : ProjectionVariant :=
  match tag with
  | "Deref" => .deref
  | "Field" => .field
  | "Index" => .index
  | "ConstantIndex" => .constantIndex
  | "Subslice" => .subslice
  | "Downcast" => .downcast
  | "OpaqueCast" => .opaqueCast
  | "UnwrapUnsafeBinder" => .unwrapUnsafeBinder
  | "PhantomDeref" => .phantomDeref
  | other => .unknown other

def isKnownStatement (tag : String) : Bool :=
  match statementVariant tag with | .unknown _ => false | _ => true
def isKnownTerminator (tag : String) : Bool :=
  match terminatorVariant tag with | .unknown _ => false | _ => true
def isKnownRvalue (tag : String) : Bool :=
  match rvalueVariant tag with | .unknown _ => false | _ => true
def isKnownOperand (tag : String) : Bool :=
  match operandVariant tag with | .unknown _ => false | _ => true
def isKnownProjection (tag : String) : Bool :=
  match projectionVariant tag with | .unknown _ => false | _ => true


end Miri.Input.DecoderValues
