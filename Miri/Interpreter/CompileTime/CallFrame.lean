import Miri.Interpreter.CompileTime.Counter
open Miri.Interpreter.CompileTime

/-! Source-only scalar frame execution, independent of the guest machine.
This leaf does not implement CTFE query roots, compiler memory, validation,
recursive interning or query admission. Unsupported operations return explicit
errors; source-value classes remain distinct. -/
namespace Miri.Interpreter.CompileTime.CallFrame
inductive Ty where
  | uint (bits : Nat) | boolean | unit | never | pair (left right : Ty)
  deriving Repr, DecidableEq, BEq
inductive Value where
  | uint (bits value : Nat) | boolean (value : Bool) | unit | uninitialized (ty : Ty) | pair (left right : Value)
  deriving Repr, DecidableEq, BEq
def Value.ty : Value → Ty
  | .uint bits _ => .uint bits | .boolean _ => .boolean | .unit => .unit
  | .uninitialized ty => ty
  | .pair a b => .pair a.ty b.ty
structure Place where
  slot : Nat
  fields : Array Nat := #[]
  deriving Repr, DecidableEq
inductive SourceValueKind where
  | typeValue | literalValue
  deriving Repr, DecidableEq
structure SourceValue where
  kind : SourceValueKind
  span : Nat
  userType : Option Nat
  value : Value
  deriving Repr, DecidableEq
structure ConstantParameter where
  index : Nat
  ty : Ty
  deriving Repr, DecidableEq
structure ConstantArgument where
  index : Nat
  ty : Ty
  value : Value
  deriving Repr, DecidableEq
inductive Reference where
  | parameterConstant (index : Nat) (annotation : Option Nat) (declaredType : Ty) (span : Nat)
  | direct (definition : Nat) (annotation : Option Nat) (declaredType : Ty := .uint 32) (span : Nat := 0)
  | associated (declaration parameter : Nat) (annotation : Option Nat) (declaredType : Ty := .uint 32) (span : Nat := 0)
  deriving Repr, DecidableEq
inductive Operand where
  | copy (place : Place) | move (place : Place) | sourceValue (source : SourceValue) | constant (source : Reference)
  deriving Repr, DecidableEq
inductive Binary where
  | gt | eq | div | addWithOverflow | subWithOverflow
  deriving Repr, DecidableEq
inductive Rvalue where
  | use (value : Operand) (withRetag : Bool) | binary (kind : Binary) (left right : Operand)
  deriving Repr, DecidableEq
inductive Statement where
  | live (slot : Nat) | dead (slot : Nat) | assign (place : Place) (value : Rvalue) | counter | nop
  deriving Repr, DecidableEq
inductive OverflowKind where
  | add | sub
  deriving Repr, DecidableEq
inductive AssertMessage where
  | overflow (kind : OverflowKind) (left right : Operand)
  | divisionByZero (operand : Operand)
  deriving Repr, DecidableEq
inductive Unwind where
  | unreachable | cleanup (target : Nat)
  deriving Repr, DecidableEq
structure Call where
  callee : Nat
  typeArguments : Array Nat := #[]
  arguments : Array Operand
  destination : Place
  target : Nat
  unwind : Unwind
  functionSpan : Nat := 0
  functionOperandSpan : Nat
  functionSourceClass : SourceValueKind
  argumentSpans : Array Nat := #[]
  callSource : String := "normal"
  functionUserType : Option Nat := none
  abi : String := "rust"
  trackCaller : Bool := false
  deriving Repr, DecidableEq
inductive Terminator where
  | goto (target : Nat)
  | switch (value : Operand) (cases : Array (Nat × Nat)) (otherwise : Nat)
  | assert (value : Operand) (expected : Bool) (message : AssertMessage) (target : Nat)
  | ret | call (source : Call) | resume
  deriving Repr, DecidableEq
structure Block where
  statements : Array Statement
  terminator : Terminator
  deriving Repr, DecidableEq
structure Program where
  locals : Array Ty
  argumentCount : Nat
  blocks : Array Block
  deriving Repr, DecidableEq
structure Local where
  live : Bool
  value : Option Value := none
  deriving Repr
structure State where
  constantArguments : Array ConstantArgument := #[]
  locals : Array Local
  block : Nat := 0
  statement : Nat := 0
  steps : Nat := 0
  counters : Nat := 0
  trace : Array (Nat × Nat × Bool) := #[]
  events : Array Counter.Event := #[]
  deriving Repr
inductive Outcome where
  | running (state : State) | returned (value : Value) (state : State) | failed (error : String) (state : State)
  | calling (source : Call) (arguments : Array Value) (state : State)
  deriving Repr
private def project : Value → List Nat → Except String Value
  | value,[] => pure value
  | .pair a _b,0::rest => project a rest
  | .pair _a b,1::rest => project b rest
  | .uninitialized (.pair a _b),0::rest => project (.uninitialized a) rest
  | .uninitialized (.pair _a b),1::rest => project (.uninitialized b) rest
  | _,_ => throw "unsupported or invalid scalar projection"
def read (state : State) (place : Place) : Except String Value := do
  let some slot := state.locals[place.slot]? | throw "absent slot"
  unless slot.live do throw "read from dead slot"
  let some value := slot.value | throw "read from uninitialized slot"
  project value place.fields.toList
def write (program : Program) (state : State) (place : Place) (value : Value) : Except String State := do
  unless place.fields.isEmpty do throw "projected scalar writes not implemented"
  if bound : place.slot < state.locals.size then
    let slot := state.locals[place.slot]
    unless slot.live do throw "write to dead slot"
    let some ty := program.locals[place.slot]? | throw "absent write slot type"
    unless ty == value.ty do throw "scalar assignment type mismatch"
    pure {state with locals := state.locals.set place.slot {slot with value := some value} bound}
  else throw "absent write slot"
private def jump (state : State) (target : Nat) : State := {state with block := target,statement := 0}
private def advance (state : State) : State := {state with statement := state.statement+1}

private def liftExcept (action : Except String α) : EStateM String World α :=
  fun world => match action with | .ok value => .ok value world | .error error => .error error world

/-- Primitive source Param substitution reads the current frame's explicit
constant namespace. It performs no compiler query or allocation. -/
def parameterValue (arguments : Array ConstantArgument) (index : Nat) (declared : Ty) : Except String Value := do
  let #[argument] := arguments.filter (·.index == index) | throw "missing or duplicate current-frame constant argument"
  unless argument.ty == declared && argument.value.ty == declared do throw "constant argument declared type mismatch"
  let .uint 32 bits := argument.value | throw "constant argument outside source u32 policy"
  unless bits < 2^32 do throw "constant argument scalar out of range"
  pure argument.value

private def operandAction (resolve : Reference → EStateM String World Value) (state : State) : Operand → EStateM String World Value
  | .sourceValue source => pure source.value
  -- Pinned eval_operand treats Move like Copy and does not invalidate source.
  | .copy place | .move place => liftExcept (read state place)
  | .constant (.parameterConstant index _ declared _) => liftExcept (parameterValue state.constantArguments index declared)
  | .constant reference => do
    let value ← resolve reference
    let declared := match reference with | .direct _ _ ty _ | .associated _ _ _ ty _ | .parameterConstant _ _ ty _ => ty
    unless value.ty == declared do throw "constant callback contradicts declared source type"
    match value with
    | .uint bits number => unless bits == 32 && number < 2^32 do throw "constant callback scalar out of range"
    | .boolean _ | .unit => pure ()
    | _ => throw "constant callback returned unsupported value"
    pure value
private def rvalueAction (resolve : Reference → EStateM String World Value) (state : State) : Rvalue → EStateM String World Value
  | .use value _ => operandAction resolve state value
  | .binary kind left right => do
    let .uint bits a ← operandAction resolve state left | throw "non-integer scalar binary operand"
    let .uint other b ← operandAction resolve state right | throw "non-integer scalar binary operand"
    unless bits == other && bits > 0 && a < 2^bits && b < 2^bits do throw "invalid scalar binary width/value"
    match kind with
    | .gt => pure (.boolean (a > b))
    | .eq => pure (.boolean (a == b))
    | .div => if b == 0 then throw "division by zero" else pure (.uint bits (a/b))
    | .addWithOverflow => pure (.pair (.uint bits ((a+b) % 2^bits)) (.boolean (a+b ≥ 2^bits)))
    | .subWithOverflow => pure (.pair (.uint bits ((a+2^bits-b) % 2^bits)) (.boolean (a < b)))

def stepWithWorld (program : Program) (config : Miri.Interpreter.CompileTime.Counter.Config) (resolve : Reference → EStateM String World Value) (initial : State) (world : World) : Outcome × World := Id.run do
  let some block := program.blocks[initial.block]? | return (.failed "absent basic block" initial,world)
  unless initial.statement <= block.statements.size do return (.failed "invalid scalar statement position" initial,world)
  let counter := match block.statements[initial.statement]? with | some .counter => true | _ => false
  let state := {initial with trace := initial.trace.push (initial.block,initial.statement,counter)}
  let action : EStateM String World (Option (Sum Value (Call × Array Value)) × State) := do
    if let some instruction := block.statements[state.statement]? then
      let next ← match instruction with
      | .nop => pure state
      | .live slot | .dead slot => do
        if bound : slot < state.locals.size then
          if slot == 0 then throw "storage marker on return place"
          let some ty := program.locals[slot]? | throw "absent storage slot type"
          let value := if instruction matches .live _ then some (Value.uninitialized ty) else none
          pure {state with locals := state.locals.set slot ⟨instruction matches .live _,value⟩ bound}
        else throw "absent storage slot"
      | .assign place value => liftExcept (write program state place (← rvalueAction resolve state value))
      | .counter => pure state
      return (none,advance next)
    match block.terminator with
    | .goto target => pure (none,jump state target)
    | .switch value cases otherwise =>
      let value ← operandAction resolve state value
      let bits ← match value with
        | .uint _ value => pure value | .boolean value => pure (if value then 1 else 0)
        | _ => throw "non-scalar switch operand"
      let target := match cases.find? (·.1 == bits) with | some (_,target) => target | none => otherwise
      pure (none,jump state target)
    | .assert value expected message target =>
      let .boolean actual ← operandAction resolve state value | throw "non-boolean assert operand"
      unless actual == expected do
        -- Pinned CompileTimeMachine::assert_panic evaluates diagnostic operands
        -- left-to-right after the condition fails, before constructing failure.
        match message with
        | .overflow _ left right =>
          let .uint _ _ ← operandAction resolve state left | throw "invalid left overflow diagnostic operand"
          let .uint _ _ ← operandAction resolve state right | throw "invalid right overflow diagnostic operand"
          pure ()
        | .divisionByZero value =>
          let .uint _ _ ← operandAction resolve state value | throw "invalid divide diagnostic operand"
          pure ()
        throw "assertion failed"
      pure (none,jump state target)
    | .call source =>
      let values ← source.arguments.mapM (operandAction resolve state)
      return (some (.inr (source,values)),state)
    | .resume => throw "unsupported CTFE cleanup Resume entered"
    | .ret => return (some (.inl (← liftExcept (read state ⟨0,#[]⟩))),state)
  let (action,world) : Except String (Option (Sum Value (Call × Array Value)) × State) × World := match action.run world with
    | .ok value world => (.ok value,world)
    | .error error world => (.error error,world)
  -- Counter changes commit before a denied lint returns an error, at the same PC.
  let mut state := state
  if counter then
    match Counter.increment config state.counters with
    | .error error => return (.failed error state,world)
    | .ok result =>
      state := {state with counters := result.count,events := state.events.push result.event}
      if result.stopAsReported then return (.failed "long_running_const_eval" state,world)
  match action with
  | .error error => return (.failed error state,world)
  | .ok (value,next) =>
    let next := {next with counters := state.counters,events := state.events}
    match value with
    | some (.inr (source,arguments)) => return (.calling source arguments next,world)
    | _ =>
      let next := {next with steps := state.steps+1}
      return ((match value with | some (.inl value) => .returned value next | _ => .running next),world)

/-- Pure source comparisons use exactly the state-preserving callback machine. -/
def step (program : Program) (config : Counter.Config)
    (resolve : Reference → Except String Value) (initial : State) : Outcome :=
  (stepWithWorld program config (fun reference => liftExcept (resolve reference)) initial ()).1

def initializeState (program : Program) (arguments : Array Value)
    (constantArguments : Array ConstantArgument := #[]) : Except String State := do
  unless program.argumentCount < program.locals.size do throw "scalar return/argument local domain is absent"
  unless arguments.size == program.argumentCount do throw "scalar argument count mismatch"
  let marked := program.blocks.flatMap fun block => block.statements.filterMap fun statement =>
    match statement with | .live slot | .dead slot => some slot | _ => none
  let mut locals := program.locals.mapIdx fun index ty => Local.mk (!marked.contains index) (some (.uninitialized ty))
  for (value,index) in arguments.zipIdx do
    let slot := index+1
    if bound : slot < locals.size then
      let some ty := program.locals[slot]? | throw "absent scalar argument type"
      unless ty == value.ty do throw "scalar argument type mismatch"
      locals := locals.set slot ⟨true,some value⟩ bound
    else throw "absent scalar argument slot"
  pure {locals,constantArguments}
end Miri.Interpreter.CompileTime.CallFrame
