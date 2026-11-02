import duplicate_prefix.ConcreteEmptyRootArgumentScope
namespace DuplicatePrefix.ConcreteEmptyRootArgumentProperties
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open RootFrameData EmptyRootArguments ConcreteEmptyRootArguments
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
 theorem untouched (root : RootFrame) (adjusted : Immediate Provenance) (borrowFrame : FrameState) (allocation : AllocId) (tag : BorTag)
    (n : UInt64) (id : Fin 25) (ne1 : id.val ≠ 1) (ne2 : id.val ≠ 2) :
    ((RootArgumentsTwo.result (firstDone root adjusted borrowFrame allocation tag) n).frame.locals[id.val]'
      ((RootArgumentsTwo.result (firstDone root adjusted borrowFrame allocation tag) n).valid id)).value =
      (root.frame.locals[id.val]'(root.valid id)).value := by
  simp only [RootArgumentsTwo.result,ConcreteEmptyRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,
    TypedRetagEntry.frameWithBorrow,firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame,i1,i2,
    Array.getElem_set,ne1,ne2,Ne.symm ne1,Ne.symm ne2,show ¬(1:Nat)=2 by decide,show ¬(2:Nat)=1 by decide,
    eq_self_iff_true,ite_true,ite_false,root.size]
end DuplicatePrefix.ConcreteEmptyRootArgumentProperties
