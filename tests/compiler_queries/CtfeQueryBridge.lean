import Miri.Input.CtfeQueryBridge

namespace CtfeBridgeTests
open Miri.Input Miri.MIR CompilerTypingEnv CtfeQueryBridge
private def seed : SourceOperand := ⟨⟨0,#[],some 2⟩,0,some ⟨99⟩⟩
private def callee : InstanceArena.Key := ⟨.Item 0,⟨0,17⟩,#[]⟩
private def access : Access (Array String) String Nat := {
  validate := fun _ world => (.ok (),world.push "validate")
  resolve := fun _ _ world => (.ok (some callee),world.push "resolve")
  queryInput := fun key world => (.ok ⟨key.family,key.environment,key.global⟩,world.push "normalize-erase")
  evaluate := fun _ world => (.error (.tooGeneric (some ⟨5⟩)),world.push "evaluate") }
private def evaluated := evaluate access fullyMonomorphized seed #[]
#guard evaluated.2 == #["validate","resolve","normalize-erase","evaluate"]
#guard match evaluated.1 with | .error (.tooGeneric (some span)) => span.id == 99 | _ => false
private def unresolved := evaluate {access with resolve := fun _ _ world =>
  (.ok none,world.push "resolve")} fullyMonomorphized seed #[]
#guard unresolved.2 == #["validate","resolve"]
#guard match unresolved.1 with | .error (.tooGeneric none) => true | _ => false
private def resolutionError := evaluate {access with resolve := fun _ _ world =>
  (.error (.reported "resolution" (some ⟨7⟩)),world.push "resolve")} fullyMonomorphized seed #[]
#guard match resolutionError.1 with | .error (.reported "resolution" none) => true | _ => false
private def unavailable := evaluate {access with queryInput := fun _ world =>
  (.error (.unsupported "missing normalization material"),world.push "normalize-erase")}
  fullyMonomorphized seed #[]
#guard unavailable.2 == #["validate","resolve","normalize-erase"]
#guard match unavailable.1 with | .error (.unsupported _) => true | _ => false
#guard (QueryKey.mk .value fullyMonomorphized ⟨callee,none⟩) !=
  (QueryKey.mk .allocation fullyMonomorphized ⟨callee,none⟩)
private def wrongFamily := evaluate {access with queryInput := fun key world =>
  (.ok ⟨.allocation,key.environment,key.global⟩,world.push "normalize-erase")}
  fullyMonomorphized seed #[]
#guard wrongFamily.2 == #["validate","resolve","normalize-erase"]
#guard match wrongFamily.1 with | .error (.internal _) => true | _ => false
end CtfeBridgeTests

def main : IO Unit := IO.println "PASS CTFE source/query stages, state-retaining errors, span rules and distinct query families"
