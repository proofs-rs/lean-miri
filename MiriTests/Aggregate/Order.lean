import Miri.Interpreter.Aggregate
open Miri Miri.Interpreter Miri.ABI Miri.Memory

def layout (zst : Bool := false) : LocalLayout :=
  ⟨0, ⟨.Arbitrary #[] #[], .Single 0, .Memory (sized := true), none, false,
    ⟨.ONE⟩, Size.ofBytes (if zst then 0 else 8), none, .ONE, false, 0⟩⟩
def operand (id : Nat) : MIR.Operand := .Copy ⟨id, #[]⟩
abbrev Log := Array String

def event (s : String) : RvalueM Log Unit := do
  let log ← EStateM.get
  EStateM.set (log.push s)

def hooks (len : UInt64) (fail : Option String := none) (zstMeta : Bool := true) :
    AggregateHooks Unit Log Unit Nat :=
  { target := ⟨.little, .w64⟩
    placeLayout := fun _ => layout
    evalOperand := fun _ op known => do
      let id := match op with | .Copy p => p.localId | _ => 99
      event s!"eval:{id}:{known.isSome}"
      if fail == some s!"eval:{id}" then throw (.callback "eval failed")
      return ⟨.immediate .uninit, layout (id == 2 && zstMeta)⟩
    readPointer := fun _ _ => do event "pointer"; return ⟨Size.ZERO, none⟩
    readScalar := fun _ _ => do
      event "scalar"
      match Scalar.fromUInt (BitVec.ofNat 128 3) (Size.ofBytes 8) with
      | .ok scalar => return scalar
      | .error _ => throw (.invalidProgram "test scalar")
    projectDowncast := fun _ _ variant => do event s!"downcast:{variant}"; return variant
    projectField := fun _ _ field => do event s!"field:{field}"; return field
    copyOp := fun _ _ _ => event "copy"
    copyOpNoValidate := fun _ _ _ transmute => do
      event s!"copy-raw:{transmute}"
      if fail == some "copy" then throw (.callback "copy failed")
    writeDiscriminant := fun _ variant _ => event s!"discriminant:{variant}"
    enforceValidity := fun _ _ => do event "enforce"; return true
    validate := fun _ _ => event "validate-reset"
    forceAllocation := fun _ dest => do event "force"; return dest
    length := fun _ _ => do event "length"; return len
    getPlaceAllocMut := fun _ _ => event "mut-access"
    projectIndex := fun _ _ index => do event s!"index:{index}"; return 0
    placePointer := fun _ => .ok ⟨Size.ZERO, none⟩
    wrappingOffset := fun ptr size => .ok { ptr with offset := size }
    memCopyRepeatedly := fun _ _ _ _ count nonoverlap => event s!"repeat:{count}:{nonoverlap}" }

def logOf (action : RvalueM Log Unit) : Log :=
  match action #[] with
  | .ok _ state | .error _ state => state

#eval (do
  unless logOf (writeAggregate (hooks 0) () .Tuple #[operand 1, operand 2] 0) ==
  #["field:0", "eval:1:true", "copy-raw:false", "field:1", "eval:2:true", "copy-raw:false",
    "discriminant:0", "enforce", "validate-reset"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeAggregate (hooks 0) () (.Adt 0 3 #[] none (some 7)) #[operand 1] 0) ==
  #["downcast:3", "field:7", "eval:1:true", "copy-raw:false", "discriminant:3", "enforce", "validate-reset"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeAggregate (hooks 0 (some "copy")) () .Tuple #[operand 1, operand 2] 0) ==
  #["field:0", "eval:1:true", "copy-raw:false"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeAggregate (hooks 0) () (.RawPtr 0 .Not) #[operand 1, operand 2] 0) ==
  #["eval:1:false", "pointer", "eval:2:false", "copy"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeAggregate (hooks 0 none false) () (.RawPtr 0 .Not) #[operand 1, operand 2] 0) ==
  #["eval:1:false", "pointer", "eval:2:false", "scalar", "copy"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeRepeat (hooks 0) () (operand 1) 0) ==
  #["eval:1:false", "force", "length", "mut-access"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeRepeat (hooks 1) () (operand 1) 0) ==
  #["eval:1:false", "force", "length", "index:0", "copy", "repeat:0:true"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeRepeat (hooks 4) () (operand 1) 0) ==
  #["eval:1:false", "force", "length", "index:0", "copy", "repeat:3:true"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)
#eval (do
  unless logOf (writeRepeat (hooks 4 (some "eval:1")) () (operand 1) 0) ==
  #["eval:1:false"] do
    throw (IO.userError "aggregate source order mismatch") : IO Unit)

def main : IO Unit := IO.println "aggregate and repeat source-order tests passed"

#eval (do
  for kind in [MIR.AggregateKind.Array 0, .Closure 0 #[], .Coroutine 0 #[], .CoroutineClosure 0 #[]] do
    unless logOf (writeAggregate (hooks 0) () kind #[] 0) ==
        #["discriminant:0", "enforce", "validate-reset"] do
      throw (IO.userError "non-ADT aggregate branch")
  unless logOf (writeAggregate (hooks 0) () (.Adt 0 2 #[] none (some 0)) #[] 0) == #["downcast:2"] do
    throw (IO.userError "union arity must follow downcast")
  match writeAggregate (hooks 0) () (.RawPtr 0 .Not) #[operand 1] 0 #[] with
  | .ok _ _ => throw (IO.userError "raw pointer arity accepted")
  | .error _ state => unless state.isEmpty do throw (IO.userError "raw pointer arity touched operands")
  : IO Unit)
