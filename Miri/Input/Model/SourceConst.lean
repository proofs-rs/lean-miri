import Miri.Input.Model.SourceMir

/-! Typed initializer syntax, without fabricated runtime frame/source metadata.
These expressions are evaluated only for a demanded compiler constant/static.
Unsupported instructions remain explicit source constructors. -/
namespace Miri.Input.SourceConst
structure Block where
  statements : Array SourceMir.StatementKind
  terminator : SourceMir.TerminatorKind
  deriving Repr, DecidableEq
structure Body where
  locals : Array SourceTypes.TypeRef
  required : Array SourceMir.Constant
  blocks : Array Block
  deriving Repr, DecidableEq
end Miri.Input.SourceConst
