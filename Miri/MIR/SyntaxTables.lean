import Miri.MIR.Syntax
import Miri.MIR.Table
import Miri.ABI.Size

namespace Miri.MIR

@[unbox] structure PlaceId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure ProjectionId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure ProjectionListId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure OperandId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure OperandListId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure ConstantId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure RvalueId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure StatementId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure TerminatorId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure BlockNodeId where
  index : Nat
  deriving Repr, DecidableEq
@[unbox] structure BodyId where
  index : Nat
  deriving Repr, DecidableEq

structure ConstantNode where
  operand : ConstOperand
  evaluation : Except String ConstValue
  deriving Repr, DecidableEq

structure PlaceNode where
  typeId : TyId
  localId : LocalId
  projection : ProjectionListId
  deriving Repr, DecidableEq

inductive OperandNode where
  | Copy (place : PlaceId)
  | Move (place : PlaceId)
  | Constant (constant : ConstantId)
  | RuntimeChecks (check : RuntimeChecks)
  deriving Repr, DecidableEq

abbrev AggregateNode := AggregateForm Nat

abbrev RvalueNode := RvalueForm PlaceId OperandId TypeConstId Nat AggregateNode OperandListId

abbrev IntrinsicNode := NonDivergingIntrinsicForm OperandId
abbrev StatementKindNode := StatementKindForm PlaceId RvalueId IntrinsicNode
abbrev SpannedOperandNode := SpannedOperandForm OperandId
abbrev InlineAsmOperandNode := InlineAsmOperandForm PlaceId OperandId ConstantId
abbrev InlineAsmNode := InlineAsmTerminatorForm InlineAsmOperandNode
abbrev AssertNode := AssertKindForm OperandId
abbrev TerminatorKindNode := TerminatorKindForm PlaceId OperandId SpannedOperandNode AssertNode InlineAsmNode

structure StatementNode where
  sourceInfo : SourceInfo
  kind : StatementKindNode
  deriving Repr, DecidableEq

structure TerminatorNode where
  sourceInfo : SourceInfo
  kind : TerminatorKindNode
  deriving Repr, DecidableEq

structure BlockNode where
  statements : Array StatementId
  terminator : TerminatorId
  cleanup : Bool
  deriving Repr, DecidableEq

structure BodyNode where
  phase : MirPhase
  argumentCount : Nat
  spreadArgument : Option LocalId
  locals : Array TyId
  basicBlocks : Array BlockNodeId
  sourceScopeCount : Nat
  alwaysLive : Array LocalId
  deriving Repr, DecidableEq

structure SyntaxTables where
  regions : SharedTable Region := #[]
  arguments : SharedTable (Array GenericArg) := #[]
  projections : SharedTable ProjectionElem := #[]
  projectionLists : SharedTable (Array ProjectionId) := #[]
  places : SharedTable PlaceNode := #[]
  operands : SharedTable OperandNode := #[]
  operandLists : SharedTable (Array OperandId) := #[]
  constants : SharedTable ConstantNode := #[]
  rvalues : SharedTable RvalueNode := #[]
  statements : SharedTable StatementNode := #[]
  terminators : SharedTable TerminatorNode := #[]
  blocks : SharedTable BlockNode := #[]
  bodies : SharedTable BodyNode := #[]
  deriving Repr, DecidableEq

end Miri.MIR
