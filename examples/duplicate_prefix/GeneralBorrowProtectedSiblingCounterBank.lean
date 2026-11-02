import duplicate_prefix.GeneralBorrowProtectedSiblingBankGeneration
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBank
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Constructor tags are absent from the requested schedule: the adapter obtains
one from actual GlobalState.newPointerTag at each shared/mutable constructor. -/
inductive Instruction where
  | borrow (position : Nat)
  | mutable
  | gc (extraLive : Array BorTag)
  | exposeRoot
  | rootAccess (kind : AccessKind)

def allocations : List Instruction → Nat
  | [] => 0
  | .borrow _ :: rest => allocations rest+1
  | .mutable :: rest => allocations rest+1
  | _ :: rest => allocations rest

def Choices : Nat → List Instruction → Prop
  | _,[] => True
  | count,.borrow position :: rest => position < count ∧ Choices (count+1) rest
  | _,.mutable :: rest => Choices 1 rest
  | count,.gc _ :: rest => Choices count rest
  | count,.exposeRoot :: rest => Choices count rest
  | count,.rootAccess kind :: rest => Choices (GeneralBorrowSharedRootAccess.count kind count) rest

/-- Exact chronological allocation trace. Nonconstructor actions preserve the
whole global; every constructor uses precisely the tag returned by newPointerTag. -/
inductive Allocation : GlobalState → List Instruction → List GeneralBorrowSharedBankMutableAction.Action → GlobalState → Prop where
  | nil (global) : Allocation global [] [] global
  | borrow {global advanced final tag position rest actions}
      (actual : global.newPointerTag = .ok (advanced,tag)) (tail : Allocation advanced rest actions final) :
      Allocation global (.borrow position::rest) (.borrow tag position::actions) final
  | mutable {global advanced final tag rest actions}
      (actual : global.newPointerTag = .ok (advanced,tag)) (tail : Allocation advanced rest actions final) :
      Allocation global (.mutable::rest) (.mutable tag::actions) final
  | gc {global final extra rest actions} (tail : Allocation global rest actions final) :
      Allocation global (.gc extra::rest) (.gc extra::actions) final
  | exposeRoot {global final rest actions} (tail : Allocation global rest actions final) :
      Allocation global (.exposeRoot::rest) (.exposeRoot::actions) final
  | rootAccess {global final kind rest actions} (tail : Allocation global rest actions final) :
      Allocation global (.rootAccess kind::rest) (.rootAccess kind::actions) final

structure Planned (initial : GlobalState) (instructions : List Instruction) where
  actions : List GeneralBorrowSharedBankMutableAction.Action
  global : GlobalState
  allocated : Allocation initial instructions actions global
  unchanged : global = {initial with nextPointerTag := global.nextPointerTag}
  nextNat : global.nextPointerTag.value.toNat = initial.nextPointerTag.value.toNat+allocations instructions
  count : (GeneralBorrowSharedBankMutableAction.tags actions).length = allocations instructions
  above : ∀ tag ∈ GeneralBorrowSharedBankMutableAction.tags actions,initial.nextPointerTag.value.toNat ≤ tag.value.toNat
  below : ∀ tag ∈ GeneralBorrowSharedBankMutableAction.tags actions,tag.value.toNat < global.nextPointerTag.value.toNat
  unique : (GeneralBorrowSharedBankMutableAction.tags actions).Nodup
  choices : ∀ count,Choices count instructions → GeneralBorrowSharedBankMutableAction.Choices count actions
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBank
