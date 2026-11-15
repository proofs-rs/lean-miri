import Miri.Frontend.FoundationFnAbi

open Lean Miri.Frontend.Foundation

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: FoundationFnAbi.lean FOUNDATION_JSON")
  let doc ← IO.ofExcept (decode (← IO.ofExcept (Json.parse (← IO.FS.readFile path))))
  let check := fun condition => unless condition do throw (IO.userError "ABI material mismatch")
  let boolean ← IO.ofExcept (rustPassMode doc.target "x86_64" false (.primitive "bool" ""))
  check (boolean.kind == .direct)
  let some attr := boolean.attributes[0]? | throw (IO.userError "missing scalar attributes")
  check (attr.regularBits == 128 && attr.argExtension == .zeroExtend)
  let cast ← IO.ofExcept (rustPassMode doc.target "x86_64" false (.array (.primitive "uint" "u8") 3))
  let some material := cast.castTarget | throw (IO.userError "missing cast")
  check (cast.kind == .cast && cast.padI32Count == some 0)
  check (material.restRegister.sizeBits == 24 && material.restTotalBytes == 3)
  check (material.attributes.regularBits == 128 && material.prefixRegisters.isEmpty)
  let indirect ← IO.ofExcept (rustPassMode doc.target "x86_64" true (.array (.primitive "uint" "u16") 9))
  let some attr := indirect.attributes[0]? | throw (IO.userError "missing indirect attributes")
  check (indirect.kind == .indirect && indirect.indirectMode == some .pointer)
  check (attr.regularBits == 670 && attr.pointeeSizeBytes == 18 && attr.pointeeAlignBytes == some 2)
  let ignored ← IO.ofExcept (rustPassMode doc.target "x86_64" false (.tuple #[]))
  check (ignored.kind == .ignore && ignored.attributes.isEmpty)
  let binding : AbiTypeBinding := ⟨.primitive "bool" "", 47, 83⟩
  let abi ← IO.ofExcept (rustFunctionAbiComponent doc.target "x86_64"
    ⟨true, false, true, false, true, false⟩ #[binding] binding)
  check (abi.returnValue.typeId == 47 && abi.returnValue.layoutId == 83)
  check (abi.fixedCount == 1 && abi.canUnwind && !abi.cVariadic)
  for (arch, ty) in [("aarch64", ConcreteType.primitive "uint" "u8"),
      ("x86_64", ConcreteType.pointer "raw_pointer" (.primitive "uint" "u8"))] do
    match rustPassMode doc.target arch false ty with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "unsupported ABI accepted")
  IO.println "foundation exact ABI component checks passed (parametric IDs only)"
