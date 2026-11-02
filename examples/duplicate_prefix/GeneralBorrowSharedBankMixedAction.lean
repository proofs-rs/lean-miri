import duplicate_prefix.GeneralBorrowSharedBankGcAction
import duplicate_prefix.GeneralBorrowSharedRootAccess
namespace DuplicatePrefix.GeneralBorrowSharedBankMixedAction
open Miri.Memory Miri.TreeBorrows
inductive Action where
  | borrow (tag : BorTag) (position : Nat)
  | gc (extraLive : Array BorTag)
  | exposeRoot
  | rootAccess (kind : AccessKind)

def tags : List Action → List BorTag
  | [] => []
  | .borrow tag _ :: rest => tag :: tags rest
  | .gc _ :: rest => tags rest
  | .exposeRoot :: rest => tags rest
  | .rootAccess _ :: rest => tags rest

def Choices : Nat → List Action → Prop
  | _,[] => True
  | count,.borrow _ position :: rest => position < count ∧ Choices (count+1) rest
  | count,.gc _ :: rest => Choices count rest
  | count,.exposeRoot :: rest => Choices count rest
  | count,.rootAccess kind :: rest => Choices (GeneralBorrowSharedRootAccess.count kind count) rest
/-- Selectable count follows constructors and resets only at root Write. -/
def handlesAfter : Nat → List Action → Nat
  | count,[] => count
  | count,.borrow _ _ :: rest => handlesAfter (count+1) rest
  | count,.gc _ :: rest => handlesAfter count rest
  | count,.exposeRoot :: rest => handlesAfter count rest
  | count,.rootAccess kind :: rest => handlesAfter (GeneralBorrowSharedRootAccess.count kind count) rest
end DuplicatePrefix.GeneralBorrowSharedBankMixedAction
