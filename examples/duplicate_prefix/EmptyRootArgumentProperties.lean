import duplicate_prefix.EmptyRootArguments
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.EmptyRootArgumentProperties
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootFrameData EmptyRootArguments
 theorem untouched (root : RootFrame) (address n : UInt64) (id : Fin 25)
    (ne1 : id.val ≠ 1) (ne2 : id.val ≠ 2) :
    ((result root address n).frame.locals[id.val]'((result root address n).valid id)).value =
      (root.frame.locals[id.val]'(root.valid id)).value := by
  simp only [result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame, i1, i2,
    Array.getElem_set, ne1, ne2, Ne.symm ne1, Ne.symm ne2,
    show ¬(1:Nat)=2 by decide, show ¬(2:Nat)=1 by decide,
    eq_self_iff_true, ite_true, ite_false, root.size]
 theorem extra (root : RootFrame) (address n : UInt64) :
    (result root address n).frame.extra = root.frame.extra := by
  simp only [result, secondLive, secondCache, firstDone, firstLive, firstCache,
    live, write, cache, atSpan, LocalOperands.cachedLayoutFrame]
end DuplicatePrefix.EmptyRootArgumentProperties
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.EmptyRootArgumentProperties.untouched, ``DuplicatePrefix.EmptyRootArgumentProperties.extra] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root argument frame property {dependency}"
