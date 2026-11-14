import Miri.Interpreter.CompileTime.Counter
open Miri.Interpreter.CompileTime.Counter
private def accepts (result : Except String Step) (expected : Step) : Bool :=
  match result with | .ok value => value == expected | .error _ => false

#guard accepts (increment ⟨64,true,true⟩ 19) ⟨20,.lint true,true⟩
#guard accepts (increment ⟨64,true,false⟩ 19) ⟨20,.lint false,false⟩
#guard accepts (increment ⟨64,true,false⟩ 31) ⟨32,.progressWarning 32,false⟩
#guard accepts (increment ⟨64,true,false⟩ 32) ⟨33,.none,false⟩
#guard accepts (increment ⟨64,false,true⟩ 1999999) ⟨2000000,.lint true,true⟩
#guard accepts (increment ⟨64,false,false⟩ 4194303) ⟨4194304,.progressWarning 4194304,false⟩
#guard accepts (increment ⟨64,false,true⟩ (2^64-1)) ⟨2^64-1,.none,false⟩

def main : IO Unit := IO.println "PASS pinned CTFE counter limits, progress events and host-usize overflow boundary"
