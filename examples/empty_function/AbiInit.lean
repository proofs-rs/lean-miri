import Miri.Interpreter.LayoutCompat
namespace EmptyFunction.AbiInit
open Miri Miri.ABI Miri.Interpreter
set_option autoImplicit false
variable {S : Type}
theorem unit_same (q : LayoutCompat.Queries MIR.TyId S) (fuel : Nat) (arg : ArgAbi MIR.TyId)
    (ignored : arg.mode = .Ignore) (backend : arg.layout.layout.backendRepr = .Memory (sized := true)) :
    LayoutCompat.checkArgumentCompat q fuel arg arg = pure true := by
  simp [LayoutCompat.checkArgumentCompat,LayoutCompat.layoutCompat,
    ArgAbi.eqAbi,PassMode.eqAbi,PassMode.isDirect,LayoutData.eqAbi,ignored,backend,
    BackendRepr.eqUpToValidity,BackendRepr.isBool,
    bind,EStateM.bind,pure,EStateM.pure]
  rfl
end EmptyFunction.AbiInit
