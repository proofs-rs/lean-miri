import Miri.Interpreter.CompileTime.RootFinish

namespace CtfeRootFinishTests
open Miri.Interpreter.CompileTime.RootFinish
private def internOk (_ : Nat) (world : List String) : Except InternError Unit × List String :=
  (.ok (),world ++ ["intern"])
private def internBad (_ : Nat) (world : List String) : Except InternError Unit × List String :=
  (.error .danglingPointer,world ++ ["intern:error-effects"])
private def validateOk (_ : Nat) (world : List String) : Except String Unit × List String :=
  (.ok (),world ++ ["validate"])
private def validateBad (_ : Nat) (world : List String) : Except String Unit × List String :=
  (.error "validation diagnostic",world ++ ["validate:error-effects"])
private def report (_ : InternError) (world : List String) : String × List String :=
  ("interning diagnostic",world ++ ["report"])
private def makeResult (root : Nat) (world : List String) : Nat × List String :=
  (root,world ++ ["make"])

theorem successKeepsRootAndOrder :
    finish internOk validateOk report makeResult 13 [] =
      .returned 13 ["intern","validate","make"] := rfl

theorem interningErrorIsDeferredUntilAfterValidation :
    finish internBad validateOk report makeResult 13 [] =
      .failed .interningReport "interning diagnostic"
        ["intern:error-effects","validate","report"] := rfl

theorem validationFailureOverridesInterningErrorWithoutRollback :
    finish internBad validateBad report makeResult 13 [] =
      .failed .validation "validation diagnostic"
        ["intern:error-effects","validate:error-effects"] := rfl

theorem validationFailureKeepsSuccessfulInterningEffects :
    finish internOk validateBad report makeResult 13 [] =
      .failed .validation "validation diagnostic"
        ["intern","validate:error-effects"] := rfl

#print axioms successKeepsRootAndOrder
#print axioms interningErrorIsDeferredUntilAfterValidation
#print axioms validationFailureOverridesInterningErrorWithoutRollback
#print axioms validationFailureKeepsSuccessfulInterningEffects
end CtfeRootFinishTests

#print axioms Miri.Interpreter.CompileTime.RootFinish.validationFailureWins
#print axioms Miri.Interpreter.CompileTime.RootFinish.deferredInterningFailure
#print axioms Miri.Interpreter.CompileTime.RootFinish.successfulFinish
