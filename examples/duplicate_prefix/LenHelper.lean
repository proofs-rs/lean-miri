import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.SharedReferenceMetadata
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.LenHelper
open Miri Miri.ABI Miri.Input Miri.Interpreter
noncomputable abbrev resolved := HelperCompilerFacts.lenCall
noncomputable abbrev body := HelperCompilerFacts.lenBody
noncomputable abbrev abi := HelperCompilerFacts.lenAbi
noncomputable abbrev rawLayout := SharedReferenceMetadata.sharedLayout
noncomputable abbrev abiQuery := HelperCompilerFacts.abiQuery resolved.callee
noncomputable abbrev bodyQuery := HelperCompilerFacts.bodyQuery resolved.callee
theorem abi_eq : abiQuery = .ok abi := HelperCompilerFacts.len_abi_eq
theorem body_eq : bodyQuery = .ok body := HelperCompilerFacts.len_body_eq
theorem raw_layout_eq : PreparedReflection.actual.runtime.lookup 7 = .ok rawLayout := by with_unfolding_all rfl
theorem raw_layout_type : rawLayout.ty = 7 := by with_unfolding_all rfl
theorem callee_kind : resolved.callee.kind = .Item 1 := by with_unfolding_all rfl
end DuplicatePrefix.LenHelper
