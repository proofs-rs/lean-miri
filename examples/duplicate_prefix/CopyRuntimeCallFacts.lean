import duplicate_prefix.GuardCompilerFacts

/-! Source shape for the zero-argument runtime guard call in check_language_ub. -/
namespace DuplicatePrefix.CopyRuntimeCallFacts
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter
open DuplicatePrefix

theorem runtime_call_terminator :
    CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]?.map
      (·.terminator.kind) = some (.Call
        (.Constant ⟨⟨158⟩, none, .Val .ZeroSized 243⟩) #[] ⟨1, #[]⟩ (some 1)
        .Continue .Misc ⟨159⟩) := by
  with_unfolding_all rfl

theorem parent_unit_prefix_source :
    CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]?.map
      (·.statements.map (·.kind)) = some #[.StorageLive 1, .StorageLive 2,
        .Assign ⟨2, #[]⟩ (.Aggregate .Tuple #[])] := by
  with_unfolding_all rfl

end DuplicatePrefix.CopyRuntimeCallFacts
