import Miri.Input.CtfeQueryMemo
open Miri.Input CtfeQueryBridge CtfeQueryMemo
private def key (family : Family := .value) : QueryKey :=
  ⟨family,CompilerTypingEnv.fullyMonomorphized,⟨⟨.Item 0,⟨0,17⟩,#[]⟩,none⟩⟩
private abbrev Mem := Store String Nat
private def reported := (do
  let _ ← memo key (pure (.finished (.error (.reported "diagnostic" (some ⟨7⟩)))))
  memo key (pure (.finished (.ok 99))) : StateM Mem _).run Store.empty
#guard reported.2.providerCalls.size == 1 && reported.2.count == 1
#guard match reported.1 with | .finished (.error (.reported "diagnostic" (some span))) => span.id == 7 | _ => false
private def families := (do
  let _ ← memo key (pure (.finished (.ok 37)))
  memo (key .allocation) (pure (.finished (.ok 73))) : StateM Mem _).run Store.empty
#guard families.2.count == 2 && families.2.providerCalls.size == 2
#guard match families.1 with | .finished (.ok 73) => true | _ => false
private def missing := (do
  let _ ← memo key (pure (.finished (.error (.unsupported "missing source"))))
  memo key (pure (.finished (.ok 99))) : StateM Mem _).run Store.empty
#guard missing.2.providerCalls.size == 2 && missing.2.count == 1
#guard match missing.1 with | .finished (.ok 99) => true | _ => false
private def cycle := (memo key (memo key (pure (.finished (.ok 99)))) : StateM Mem _).run Store.empty
#guard cycle.2.count == 0 && cycle.2.activeCount == 0 && cycle.2.providerCalls.size == 1
#guard match cycle.1 with | .cycle active => active == #[key,key] | _ => false
private def separate := (memo key (pure (.finished (.ok 11))) : StateM Mem _).run Store.empty
#guard separate.2.providerCalls.size == 1
#guard match separate.1 with | .finished (.ok 11) => true | _ => false
def main : IO Unit := IO.println "PASS execution-local CTFE memo results, terminal errors, family separation and unreported cycle requests"
