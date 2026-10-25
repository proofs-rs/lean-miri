import Miri.Interpreter.Rvalue
open Miri Miri.ABI Miri.Interpreter

private def layout : TyAndLayout MIR.TyId := ⟨0, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := Align.ONE,
  reprC := false, randomizationSeed := 0 }⟩
private def place : MIR.Place := ⟨0, #[]⟩
private def operand : MIR.Operand := .Copy place
private def op : OpTy Unit := ⟨.immediate .uninit, layout⟩
private def imm : RvalueImmTy Unit := ⟨.uninit, layout⟩
private abbrev Trace := List String
private def log (name : String) (value : A) : RvalueM Trace A := do
  modify (· ++ [name])
  pure value
private def blocked (name : String) : RvalueM Trace A := do
  modify (· ++ [name])
  throw (.unsupported name)

private def hooks : RvalueHooks Unit Trace Unit Unit := {
  placeLayout := fun _ => layout
  evalPlace := fun _ _ skip => log s!"place:{skip}" ()
  evalOperand := fun _ _ known => log s!"operand:{known.isSome}" op
  evalPlaceToOp := fun _ _ _ => log "placeToOp" op
  readImmediate := fun _ _ => log "readImmediate" imm
  writeImmediate := fun _ _ _ => log "writeImmediate" ()
  writePointer := fun _ _ _ => log "writePointer" ()
  threadLocalPointer := fun _ _ => blocked "threadLocalPointer"
  withRetagMode := fun _ mode action => do
    let _ ← log s!"mode:{reprStr mode}" ()
    let result ← action
    let _ ← log "restoreMode" ()
    return result
  copyOp := fun _ _ _ => log "copy" ()
  copyOpAllowTransmute := fun _ _ _ => log "transmuteCopy" ()
  binaryOp := fun _ _ _ _ => log "binary" imm
  unaryOp := fun _ _ _ => log "unary" imm
  writeAggregate := fun _ _ _ _ => blocked "aggregate"
  writeRepeat := fun _ _ _ => blocked "repeat"
  forceAllocation := fun _ _ => blocked "forceAllocation"
  toRef := fun _ _ => blocked "toRef"
  enforceValidity := fun _ _ => blocked "enforceValidity"
  retagPtrValue := fun _ _ _ => blocked "retagPtrValue"
  placeBaseRaw := fun _ _ => log "baseRaw" true
  normalize := fun _ ty => log "normalize" ty
  cast := fun _ _ _ _ _ => blocked "cast"
  readDiscriminant := fun _ _ => blocked "readDiscriminant"
  discriminantForVariant := fun _ _ _ => blocked "discriminantForVariant" }

private def trace (value : MIR.Rvalue) : Trace :=
  (runRvalue (evalRvalueIntoPlace hooks () value place) []).1

#eval do
  unless (trace (.BinaryOp .Add operand operand) =
    ["place:true", "operand:true", "readImmediate", "operand:true", "readImmediate", "binary", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Use operand .Yes) =
    ["place:true", "operand:true", "mode:Miri.TreeBorrows.RetagPolicy.RetagMode.Default", "copy", "restoreMode"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.CopyForDeref place) == ["place:true"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.RawPtr .Const place) == ["place:true", "baseRaw", "place:false", "forceAllocation"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Reborrow 0 .Not place) == ["place:true", "placeToOp", "transmuteCopy"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.WrapUnsafeBinder operand 0) == ["place:true", "operand:false", "transmuteCopy"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.ThreadLocalRef 0) == ["place:true", "threadLocalPointer"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Aggregate .Tuple #[]) == ["place:true", "aggregate"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((runRvalue (evalRvalueIntoPlace hooks () (.ThreadLocalRef 0) place) []).2 =
    Except.error (StepError.unsupported "threadLocalPointer")) do throw (IO.userError "runtime assertion failed")

#eval do
  unless (trace (.UnaryOp .Neg operand) =
    ["place:true", "operand:true", "readImmediate", "unary", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Discriminant place) =
    ["place:true", "placeToOp", "readDiscriminant"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Ref .Erased .Shared place) =
    ["place:true", "place:true", "forceAllocation"]) do throw (IO.userError "runtime assertion failed")

private def allocated : RvalueHooks Unit Trace Unit Unit := {
  hooks with
  forceAllocation := fun _ _ => log "forceAllocation" ⟨⟨Size.ZERO, none⟩, .none, none⟩
  toRef := fun _ _ => log "toRef" .uninit
  enforceValidity := fun _ _ => log "enforceValidity" false
  retagPtrValue := fun _ _ _ => log "retag" (some imm) }
private def allocatedTrace (value : MIR.Rvalue) : Trace :=
  (runRvalue (evalRvalueIntoPlace allocated () value place) []).1
#eval do
  unless (allocatedTrace (.Ref .Erased (.Mut .TwoPhaseBorrow) place) =
    ["place:true", "place:true", "forceAllocation", "toRef", "mode:Miri.TreeBorrows.RetagPolicy.RetagMode.TwoPhase", "enforceValidity", "retag", "writeImmediate", "restoreMode"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (allocatedTrace (.RawPtr .Const place) =
    ["place:true", "baseRaw", "place:false", "forceAllocation", "toRef", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
private def freshRaw : RvalueHooks Unit Trace Unit Unit := {
  allocated with placeBaseRaw := fun _ _ => log "baseRaw" false }
#eval do
  unless ((runRvalue (evalRvalueIntoPlace freshRaw () (.RawPtr .Const place) place) []).1 =
    ["place:true", "baseRaw", "place:false", "forceAllocation", "toRef", "mode:Miri.TreeBorrows.RetagPolicy.RetagMode.Raw", "retag", "restoreMode", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((runRvalue (evalRvalueIntoPlace freshRaw () (.RawPtr .FakeForPtrMetadata place) place) []).1 =
    ["place:true", "baseRaw", "place:false", "forceAllocation", "toRef", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Cast .IntToInt operand 0) =
    ["place:true", "operand:false", "normalize", "cast"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.Repeat operand .Error) == ["place:true", "repeat"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.BinaryOp .Eq operand operand) =
    ["place:true", "operand:false", "readImmediate", "operand:true", "readImmediate", "binary", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (trace (.BinaryOp .Shl operand operand) =
    ["place:true", "operand:true", "readImmediate", "operand:false", "readImmediate", "binary", "writeImmediate"]) do throw (IO.userError "runtime assertion failed")
private def mismatch : RvalueHooks Unit Trace Unit Unit := {
  hooks with binaryOp := fun _ _ _ _ => log "binary" { imm with layout := { layout with ty := 1 } } }
#eval do
  unless ((runRvalue (evalRvalueIntoPlace mismatch () (.BinaryOp .Add operand operand) place) []).2 =
    Except.error (StepError.invalidProgram "rvalue result layout mismatch")) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((runRvalue (evalRvalueIntoPlace mismatch () (.BinaryOp .Add operand operand) place) []).1 =
    ["place:true", "operand:true", "readImmediate", "operand:true", "readImmediate", "binary"]) do throw (IO.userError "runtime assertion failed")
