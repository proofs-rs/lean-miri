import Miri.Input.CompilerFrameContext
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedPhaseFrame
open Miri Miri.Input Miri.Memory Miri.Interpreter
set_option autoImplicit false
structure Frame (before after : CompilerFrameContext.ActualFrame) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  returnPlace : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  varargs : after.vaList = before.vaList
  localsIdentity : after.localsIdentity = before.localsIdentity
end DuplicatePrefix.GeneralBorrowFreshRootScopedPhaseFrame
