import duplicate_prefix.CopyInstall
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.CopyArgumentProperties
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CopyFrameData CopyInstall
 theorem untouched (root : RootFrame) (source destination : Scalar Provenance) (n : UInt64) (id : Fin 17)
    (ne1 : id.val ≠ 1) (ne2 : id.val ≠ 2) (ne3 : id.val ≠ 3) :
    ((result root source destination n).frame.locals[id.val]'((result root source destination n).valid id)).value =
    (root.frame.locals[id.val]'(root.valid id)).value := by
  unfold result
  rw [completed_other _ 2 id (by simpa using ne3),completed_other _ 1 id (by simpa using ne2),completed_other _ 0 id (by simpa using ne1)]
 theorem extra (root : RootFrame) (source destination : Scalar Provenance) (n : UInt64) :
    (result root source destination n).frame.extra = root.frame.extra := by
  simp only [result,completed,cached,write,live,cache,atSpan,LocalOperands.cachedLayoutFrame]
end DuplicatePrefix.CopyArgumentProperties
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyArgumentProperties.untouched, ``DuplicatePrefix.CopyArgumentProperties.extra] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy argument property {dependency}"
