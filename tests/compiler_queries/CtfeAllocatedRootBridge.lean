import Miri.Input.CtfeQueryBridge
namespace CtfeAllocatedRootBridgeTests
open Miri.Input Miri.MIR CompilerTypingEnv CtfeQueryBridge
private def callee : InstanceArena.Key := ⟨.Item 0,⟨0,17⟩,#[]⟩
private def seed : SourceOperand := ⟨⟨0,#[],none⟩,0,none⟩
private def access : Access (List String) String Nat := {
  validate := fun _ world => (.ok (),world ++ ["source"])
  resolve := fun _ _ world => (.ok (some callee),world ++ ["resolve"])
  queryInput := fun key world => (.ok ⟨key.family,key.environment,key.global⟩,world ++ ["normalize"])
  evaluate := fun _ world => (.error (.unsupported "no provider"),world) }
private def roots : AllocatedRootAccess (List String) String Nat Nat := {
  executeRoot := fun _ world => (.ok 13,world ++ ["execute-allocated-root"])
  intern := fun _ _ world => (.error .danglingPointer,world ++ ["global-install-effect"])
  validateRoot := fun _ _ world => (.error (.reported "validation" none),world ++ ["validation-failure"])
  reportIntern := fun _ _ world => (.reported "intern" none,world ++ ["deferred-report"])
  makeResult := fun _ root world => (root,world ++ ["make-result"]) }
private def checked := evaluate (access.withAllocatedRoots roots) fullyMonomorphized seed []
#guard checked.2 == ["source","resolve","normalize","execute-allocated-root","global-install-effect","validation-failure"]
#guard match checked.1 with | .error (.reported "validation" none) => true | _ => false
private def deferred := evaluate (access.withAllocatedRoots {roots with
  validateRoot := fun _ _ world => (.ok (),world ++ ["validate"])}) fullyMonomorphized seed []
#guard deferred.2 == ["source","resolve","normalize","execute-allocated-root","global-install-effect","validate","deferred-report"]
#guard match deferred.1 with | .error (.reported "intern" none) => true | _ => false
private def noAllocator : AllocatedRootAccess (List String) String Empty Nat := {
  executeRoot := fun _ world => (.error (.unsupported "exact allocator snapshot unavailable"),world ++ ["allocator-unavailable"])
  intern := fun _ root => nomatch root
  validateRoot := fun _ root => nomatch root
  reportIntern := fun _ _ world => (.unsupported "no diagnostic capability",world)
  makeResult := fun _ root => nomatch root }
private def unavailable := evaluate (access.withAllocatedRoots noAllocator) fullyMonomorphized seed []
#guard unavailable.2 == ["source","resolve","normalize","allocator-unavailable"]
#guard match unavailable.1 with | .error (.unsupported _) => true | _ => false
end CtfeAllocatedRootBridgeTests
def main : IO Unit := IO.println "PASS actual adapter control: execute/intern/validation/deferred order, retained World effects, unavailable allocator has no possible Root"
