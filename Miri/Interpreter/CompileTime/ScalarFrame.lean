import Miri.Interpreter.CompileTime.Counter

/-! Source-only scalar frame execution, independent of the guest machine.
This leaf does not implement CTFE query roots, compiler memory, validation,
recursive interning or query admission. Unsupported operations return explicit
errors; source-value classes remain distinct. -/
namespace Miri.Interpreter.CompileTime.ScalarFrame
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
  deriving Repr
inductive SourceValueKind where
  | typeValue | literalValue
  deriving Repr
structure SourceValue where
  kind : SourceValueKind
  span : Nat
  userType : Option Nat
  value : Value
  deriving Repr
inductive Operand where
  | copy (place : Place) | move (place : Place) | sourceValue (source : SourceValue)
  deriving Repr
inductive Binary where
  | gt | addWithOverflow | subWithOverflow
  deriving Repr
inductive Rvalue where
  | use (value : Operand) (withRetag : Bool) | binary (kind : Binary) (left right : Operand)
  deriving Repr
inductive Statement where
  | live (slot : Nat) | dead (slot : Nat) | assign (place : Place) (value : Rvalue) | counter | nop
  deriving Repr
inductive OverflowKind where
  | add | sub
  deriving Repr
inductive AssertMessage where
  | overflow (kind : OverflowKind) (left right : Operand)
  deriving Repr
inductive Terminator where
  | goto (target : Nat)
  | switch (value : Operand) (cases : Array (Nat × Nat)) (otherwise : Nat)
  | assert (value : Operand) (expected : Bool) (message : AssertMessage) (target : Nat)
  | ret
  deriving Repr
structure Block where
  statements : Array Statement
  terminator : Terminator
  deriving Repr
structure Program where
  locals : Array Ty
  argumentCount : Nat
  blocks : Array Block
  deriving Repr
structure Local where
  live : Bool
  value : Option Value := none
  deriving Repr
structure State where
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
  deriving Repr
private def project : Value → List Nat → Except String Value
  | value,[] => pure value
  | .pair a _b,0::rest => project a rest
  | .pair _a b,1::rest => project b rest
  | .uninitialized (.pair a _b),0::rest => project (.uninitialized a) rest
  | .uninitialized (.pair _a b),1::rest => project (.uninitialized b) rest
  | _,_ => throw "unsupported or invalid scalar projection"
private def read (state : State) (place : Place) : Except String Value := do
  let some slot := state.locals[place.slot]? | throw "absent slot"
  unless slot.live do throw "read from dead slot"
  let some value := slot.value | throw "read from uninitialized slot"
  project value place.fields.toList
private def operand (state : State) : Operand → Except String Value
  | .sourceValue source => pure source.value
  -- Pinned eval_operand treats Move like Copy and does not invalidate source.
  | .copy place | .move place => read state place
private def rvalue (state : State) : Rvalue → Except String Value
  | .use value _ => operand state value
  | .binary kind left right => do
    let .uint bits a ← operand state left | throw "non-integer scalar binary operand"
    let .uint other b ← operand state right | throw "non-integer scalar binary operand"
    unless bits == other && bits > 0 && a < 2^bits && b < 2^bits do throw "invalid scalar binary width/value"
    match kind with
    | .gt => pure (.boolean (a > b))
    | .addWithOverflow => pure (.pair (.uint bits ((a+b) % 2^bits)) (.boolean (a+b ≥ 2^bits)))
    | .subWithOverflow => pure (.pair (.uint bits ((a+2^bits-b) % 2^bits)) (.boolean (a < b)))
private def write (program : Program) (state : State) (place : Place) (value : Value) : Except String State := do
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

def step (program : Program) (config : Counter.Config) (initial : State) : Outcome := Id.run do
  let some block := program.blocks[initial.block]? | return .failed "absent basic block" initial
  unless initial.statement <= block.statements.size do return .failed "invalid scalar statement position" initial
  let counter := match block.statements[initial.statement]? with | some .counter => true | _ => false
  let state := {initial with trace := initial.trace.push (initial.block,initial.statement,counter)}
  let action : Except String (Option Value × State) := do
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
      | .assign place value => write program state place (← rvalue state value)
      | .counter => pure state
      return (none,advance next)
    match block.terminator with
    | .goto target => pure (none,jump state target)
    | .switch value cases otherwise =>
      let value ← operand state value
      let bits ← match value with
        | .uint _ value => pure value | .boolean value => pure (if value then 1 else 0)
        | _ => throw "non-scalar switch operand"
      let target := match cases.find? (·.1 == bits) with | some (_,target) => target | none => otherwise
      pure (none,jump state target)
    | .assert value expected message target =>
      let .boolean actual ← operand state value | throw "non-boolean assert operand"
      unless actual == expected do
        -- Pinned CompileTimeMachine::assert_panic evaluates diagnostic operands
        -- left-to-right after the condition fails, before constructing failure.
        let .overflow _ left right := message
        let .uint _ _ ← operand state left | throw "invalid left overflow diagnostic operand"
        let .uint _ _ ← operand state right | throw "invalid right overflow diagnostic operand"
        throw "assertion failed"
      pure (none,jump state target)
    | .ret => return (some (← read state ⟨0,#[]⟩),state)
  -- Counter changes commit before a denied lint returns an error, at the same PC.
  let mut state := state
  if counter then
    match Counter.increment config state.counters with
    | .error error => return .failed error state
    | .ok result =>
      state := {state with counters := result.count,events := state.events.push result.event}
      if result.stopAsReported then return .failed "long_running_const_eval" state
  match action with
  | .error error => return .failed error state
  | .ok (value,next) =>
    let next := {next with counters := state.counters,events := state.events,steps := state.steps+1}
    return match value with | some value => .returned value next | none => .running next

def initializeState (program : Program) (arguments : Array Value) : Except String State := do
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
  pure {locals}
def run (program : Program) (config : Counter.Config) : Nat → State → Outcome
  | 0,state => .failed "scalar frame traversal budget exhausted" state
  | fuel+1,state => match step program config state with
    | .running state => run program config fuel state | other => other
end Miri.Interpreter.CompileTime.ScalarFrame
