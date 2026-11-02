import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.LenCallResultFrame

namespace DuplicatePrefix.S02SharedPreLenReturnFields
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
noncomputable section

/-- The Ref temporary changes only the local array and program counter. -/
theorem prelen_place (site : CompilerFrameContext.ActualFrame)
    (valid : 12 < site.locals.size) (value : Immediate Provenance) :
    (GeneralBorrowForestSharedPreLenFrame.after site valid value).returnPlace = site.returnPlace := rfl

theorem prelen_continuation (site : CompilerFrameContext.ActualFrame)
    (valid : 12 < site.locals.size) (value : Immediate Provenance) :
    (GeneralBorrowForestSharedPreLenFrame.after site valid value).returnContinuation = site.returnContinuation := rfl

theorem prelen_varargs (site : CompilerFrameContext.ActualFrame)
    (valid : 12 < site.locals.size) (value : Immediate Provenance) :
    (GeneralBorrowForestSharedPreLenFrame.after site valid value).vaList = site.vaList := rfl

end
end DuplicatePrefix.S02SharedPreLenReturnFields

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SharedPreLenReturnFields.prelen_place) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved shared prelen place dependency {dependency}"
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SharedPreLenReturnFields.prelen_continuation) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved shared prelen continuation dependency {dependency}"
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SharedPreLenReturnFields.prelen_varargs) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved shared prelen varargs dependency {dependency}"
