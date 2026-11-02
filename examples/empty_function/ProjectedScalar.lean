import empty_function.InputDraft
namespace EmptyFunction.ProjectedScalar
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- Payload/outer width agreement follows from the public constructor image;
no successful scalar or memory operation is an input field. -/
 theorem conversion (target : TargetDataLayout) (value : Scalar Provenance)
    (canonical : InputDraft.RawCanonicalScalar target value) :
    ∃ result, value.toBitsOrPtrInternal value.size = .ok result := by
  cases canonical with
  | integer payload encoding nonzero width truncated =>
    subst value
    refine ⟨.bits payload.toBitsUnchecked,?_⟩
    with_unfolding_all
      simp [Scalar.toBitsOrPtrInternal,Scalar.fromScalarInt,Miri.Memory.Scalar.size,ScalarInt.size,ScalarInt.toBits,
        ScalarInt.toBitsUnchecked,Except.mapError,pure,Pure.pure,Except.pure,bind,Bind.bind,Except.bind]
  | pointer pointer encoding =>
    subst value
    refine ⟨.pointer pointer,?_⟩
    with_unfolding_all
      simp [Scalar.toBitsOrPtrInternal,Scalar.fromPointer,Miri.Memory.Scalar.size,ScalarInt.size,pure,Pure.pure,Except.pure]

end EmptyFunction.ProjectedScalar
