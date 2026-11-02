import duplicate_prefix.GeneralBorrowSharedBankGcAction
import duplicate_prefix.GeneralBorrowSharedRootBankExposure
namespace DuplicatePrefix.GeneralBorrowSharedBankExposureGcAction
open Miri.Memory
inductive Action where
  | borrow (tag : BorTag) (position : Nat)
  | gc (extraLive : Array BorTag)
  | exposeRoot

def tags : List Action → List BorTag
  | [] => []
  | .borrow tag _ :: rest => tag :: tags rest
  | .gc _ :: rest => tags rest
  | .exposeRoot :: rest => tags rest

def Choices : Nat → List Action → Prop
  | _,[] => True
  | count,.borrow _ position :: rest => position < count ∧ Choices (count+1) rest
  | count,.gc _ :: rest => Choices count rest
  | count,.exposeRoot :: rest => Choices count rest
end DuplicatePrefix.GeneralBorrowSharedBankExposureGcAction
