import duplicate_prefix.S02WildcardSourceWildcardInstalledReturnFacts
import duplicate_prefix.S02ConcreteSourceWildcardRejectedGuardLocal
import duplicate_prefix.S02SharedPreLenReturnFields

namespace DuplicatePrefix.S02WildcardSourceWildcardGuardReturnFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Ref/len and the false guard preserve the installed runtime Return fields. -/
theorem transfer
    (entry site guard : CompilerFrameContext.ActualFrame)
    (count len : UInt64)
    (shape : GenericFunctionEntryPrefix.Shape entry site count)
    (validDest : 12 < site.locals.size) (value : Immediate Provenance)
    (valid11 : 11 < (GeneralBorrowForestSharedPreLenFrame.after site validDest value).locals.size)
    (place : MPlaceTy Provenance)
    (installedReturn : entry.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (installedContinuation : entry.returnContinuation = .stop true)
    (installedVarargs : entry.vaList = #[])
    (guardPlace : guard.returnPlace =
      (LenCallResultFrame.resultFrame (GeneralBorrowForestSharedPreLenFrame.after site validDest value)
        valid11 len).returnPlace)
    (guardContinuation : guard.returnContinuation =
      (LenCallResultFrame.resultFrame (GeneralBorrowForestSharedPreLenFrame.after site validDest value)
        valid11 len).returnContinuation)
    (guardVarargs : guard.vaList =
      (LenCallResultFrame.resultFrame (GeneralBorrowForestSharedPreLenFrame.after site validDest value)
        valid11 len).vaList) :
    guard.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
    guard.returnContinuation = .stop true ∧ guard.vaList = #[] := by
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  obtain ⟨_,_,_,_,_,lenPlace,lenContinuation,_,lenVarargs,_⟩ :=
    LenCallResultFrame.attributes caller valid11 len
  have eqPlace : guard.returnPlace = entry.returnPlace := by
    calc
      guard.returnPlace = (LenCallResultFrame.resultFrame caller valid11 len).returnPlace := guardPlace
      _ = caller.returnPlace := lenPlace
      _ = site.returnPlace := S02SharedPreLenReturnFields.prelen_place site validDest value
      _ = entry.returnPlace := shape.returnPlace
  have eqContinuation : guard.returnContinuation = entry.returnContinuation := by
    calc
      guard.returnContinuation = (LenCallResultFrame.resultFrame caller valid11 len).returnContinuation := guardContinuation
      _ = caller.returnContinuation := lenContinuation
      _ = site.returnContinuation := S02SharedPreLenReturnFields.prelen_continuation site validDest value
      _ = entry.returnContinuation := shape.continuation
  have eqVarargs : guard.vaList = entry.vaList := by
    calc
      guard.vaList = (LenCallResultFrame.resultFrame caller valid11 len).vaList := guardVarargs
      _ = caller.vaList := lenVarargs
      _ = site.vaList := S02SharedPreLenReturnFields.prelen_varargs site validDest value
      _ = entry.vaList := shape.vaList
  exact ⟨eqPlace ▸ installedReturn,eqContinuation ▸ installedContinuation,
    eqVarargs ▸ installedVarargs⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardGuardReturnFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardGuardReturnFrame.transfer) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard rejected guard frame transfer dependency {dependency}"
