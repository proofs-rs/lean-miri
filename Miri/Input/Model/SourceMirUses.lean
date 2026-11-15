import Miri.Input.Model.SourceMir
/-! Generic optimized-MIR parameter place-use syntax. No deduced attributes,
usage bitsets or monomorphic query answers are stored. -/
namespace Miri.Input.SourceMirUses
inductive ProjectionHead where
  | deref | other
  deriving Repr, DecidableEq
inductive MutatingContext where
  | store | setDiscriminant | asmOutput | call | yield | drop | borrow | rawBorrow | projection
  deriving Repr, DecidableEq
inductive NonMutatingContext where
  | inspect | copy | move | sharedBorrow | fakeBorrow | rawBorrow | placeMention | projection
  deriving Repr, DecidableEq
inductive Context where
  | nonUse
  | mutating (context : MutatingContext)
  | nonMutating (context : NonMutatingContext)
  deriving Repr, DecidableEq
structure Place where
  localId : Nat
  firstProjection : Option ProjectionHead
  deriving Repr, DecidableEq
inductive Kind where
  | place (place : Place) (context : Context)
  | callMove (place : Place)
  | tailCall
  deriving Repr, DecidableEq
structure Event where
  block : Nat
  statement : Nat
  kind : Kind
  deriving Repr, DecidableEq
structure Body where
  argumentCount : Nat
  spreadArgument : Option Nat
  phase : SourceMir.Phase
  blockStatementCounts : Array Nat
  events : Array Event
  deriving Repr, DecidableEq
inductive Optimization where
  | no | less | more | aggressive | size | sizeMin
  deriving Repr, DecidableEq
structure Compilation where
  optimization : Optimization
  incremental : Bool
  freezeLangItemPresent : Option Bool := none
  deriving Repr, DecidableEq
structure Declaration where
  definition : DefinitionId
  body : Option Body
  compilation : Option Compilation
  alwaysConst : Option Bool := none
  deriving Repr, DecidableEq
structure Material where
  declarations : Array Declaration
  deriving Repr, DecidableEq
end Miri.Input.SourceMirUses
