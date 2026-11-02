import duplicate_prefix.RootCompilerFacts

/-! Exact immutable ABI/body queries for the four calls made directly by the
root. Callees are obtained from canonical call-site resolution, never names. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.HelperCompilerFacts
open Miri Miri.ABI Miri.Input Miri.Interpreter

noncomputable def rootCall (block : Nat) :=
  CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls ⟨RootBody.reflected.body.identity.index, block⟩

private def checkedOk {Error Value : Type} :
    (value : Except Error Value) → value.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

private theorem checkedOk_eq {Error Value : Type}
    (value : Except Error Value) (success : value.isOk = true) :
    value = .ok (checkedOk value success) := by
  cases value with
  | ok value => rfl
  | error error => cases success

theorem len_site_supported : (rootCall 2).isOk = true := by decide +kernel
theorem as_mut_ptr_site_supported : (rootCall 6).isOk = true := by decide +kernel
theorem add_site_supported : (rootCall 7).isOk = true := by decide +kernel
theorem copy_site_supported : (rootCall 8).isOk = true := by decide +kernel

noncomputable def lenCall := checkedOk (rootCall 2) len_site_supported
noncomputable def asMutPtrCall := checkedOk (rootCall 6) as_mut_ptr_site_supported
noncomputable def addCall := checkedOk (rootCall 7) add_site_supported
noncomputable def copyCall := checkedOk (rootCall 8) copy_site_supported

theorem len_call_eq : rootCall 2 = .ok lenCall := checkedOk_eq _ _
theorem as_mut_ptr_call_eq : rootCall 6 = .ok asMutPtrCall := checkedOk_eq _ _
theorem add_call_eq : rootCall 7 = .ok addCall := checkedOk_eq _ _
theorem copy_call_eq : rootCall 8 = .ok copyCall := checkedOk_eq _ _

noncomputable def abiQuery (callee : CallInstance) :=
  CompilerInstanceAbi.abiOfInstance PreparedReflection.actual.compiler.lifecycle.instances callee #[]
noncomputable def bodyQuery (callee : CallInstance) :=
  CallResolution.loadedBodyOfInstance PreparedReflection.actual.compiler.lifecycle.calls.calls callee

theorem len_abi_supported : (abiQuery lenCall.callee).isOk = true := by decide +kernel
theorem as_mut_ptr_abi_supported : (abiQuery asMutPtrCall.callee).isOk = true := by decide +kernel
theorem add_abi_supported : (abiQuery addCall.callee).isOk = true := by decide +kernel
theorem copy_abi_supported : (abiQuery copyCall.callee).isOk = true := by decide +kernel

theorem len_body_supported : (bodyQuery lenCall.callee).isOk = true := by decide +kernel
theorem as_mut_ptr_body_supported : (bodyQuery asMutPtrCall.callee).isOk = true := by decide +kernel
theorem add_body_supported : (bodyQuery addCall.callee).isOk = true := by decide +kernel
theorem copy_body_supported : (bodyQuery copyCall.callee).isOk = true := by decide +kernel

noncomputable def lenAbi := checkedOk (abiQuery lenCall.callee) len_abi_supported
noncomputable def asMutPtrAbi := checkedOk (abiQuery asMutPtrCall.callee) as_mut_ptr_abi_supported
noncomputable def addAbi := checkedOk (abiQuery addCall.callee) add_abi_supported
noncomputable def copyAbi := checkedOk (abiQuery copyCall.callee) copy_abi_supported
noncomputable def lenBody := checkedOk (bodyQuery lenCall.callee) len_body_supported
noncomputable def asMutPtrBody := checkedOk (bodyQuery asMutPtrCall.callee) as_mut_ptr_body_supported
noncomputable def addBody := checkedOk (bodyQuery addCall.callee) add_body_supported
noncomputable def copyBody := checkedOk (bodyQuery copyCall.callee) copy_body_supported

theorem len_abi_eq : abiQuery lenCall.callee = .ok lenAbi := checkedOk_eq _ _
theorem as_mut_ptr_abi_eq : abiQuery asMutPtrCall.callee = .ok asMutPtrAbi := checkedOk_eq _ _
theorem add_abi_eq : abiQuery addCall.callee = .ok addAbi := checkedOk_eq _ _
theorem copy_abi_eq : abiQuery copyCall.callee = .ok copyAbi := checkedOk_eq _ _
theorem len_body_eq : bodyQuery lenCall.callee = .ok lenBody := checkedOk_eq _ _
theorem as_mut_ptr_body_eq : bodyQuery asMutPtrCall.callee = .ok asMutPtrBody := checkedOk_eq _ _
theorem add_body_eq : bodyQuery addCall.callee = .ok addBody := checkedOk_eq _ _
theorem copy_body_eq : bodyQuery copyCall.callee = .ok copyBody := checkedOk_eq _ _

theorem len_shape :
    (lenAbi.args.map (·.layout.ty), lenAbi.ret.layout.ty, lenBody.body.argumentCount,
      lenBody.body.locals.size, lenBody.body.basicBlocks.size) = (#[7], 5, 1, 3, 2) := by decide +kernel

theorem as_mut_ptr_shape :
    (asMutPtrAbi.args.map (·.layout.ty), asMutPtrAbi.ret.layout.ty, asMutPtrBody.body.argumentCount,
      asMutPtrBody.body.locals.size, asMutPtrBody.body.basicBlocks.size) = (#[3], 8, 1, 5, 1) := by decide +kernel

theorem add_shape :
    (addAbi.args.map (·.layout.ty), addAbi.ret.layout.ty, addBody.body.argumentCount,
      addBody.body.locals.size, addBody.body.basicBlocks.size) = (#[8, 5, 26], 8, 2, 5, 1) := by decide +kernel

theorem copy_shape :
    (copyAbi.args.map (·.layout.ty), copyAbi.ret.layout.ty, copyBody.body.argumentCount,
      copyBody.body.locals.size, copyBody.body.basicBlocks.size) = (#[9, 8, 5, 26], 2, 3, 17, 8) := by decide +kernel

theorem len_caller_location :
    CompilerRuntimeQueries.requiresCallerLocation PreparedReflection.actual.compiler.lifecycle.calls.runtime
      lenCall.callee = .ok false := by with_unfolding_all rfl

theorem as_mut_ptr_caller_location :
    CompilerRuntimeQueries.requiresCallerLocation PreparedReflection.actual.compiler.lifecycle.calls.runtime
      asMutPtrCall.callee = .ok false := by with_unfolding_all rfl

theorem add_caller_location :
    CompilerRuntimeQueries.requiresCallerLocation PreparedReflection.actual.compiler.lifecycle.calls.runtime
      addCall.callee = .ok true := by with_unfolding_all rfl

theorem copy_caller_location :
    CompilerRuntimeQueries.requiresCallerLocation PreparedReflection.actual.compiler.lifecycle.calls.runtime
      copyCall.callee = .ok true := by with_unfolding_all rfl

open Lean Elab Command in
run_cmd do
  for declaration in #[``len_call_eq, ``as_mut_ptr_call_eq, ``add_call_eq, ``copy_call_eq,
      ``len_abi_eq, ``as_mut_ptr_abi_eq, ``add_abi_eq, ``copy_abi_eq,
      ``len_body_eq, ``as_mut_ptr_body_eq, ``add_body_eq, ``copy_body_eq,
      ``len_shape, ``as_mut_ptr_shape, ``add_shape, ``copy_shape,
      ``len_caller_location, ``as_mut_ptr_caller_location, ``add_caller_location, ``copy_caller_location] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.HelperCompilerFacts
