import Miri.Input.CompilerDiscriminantFacts
import Miri.Input.Decoder
open Lean Miri.Input TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected compiler export")
  let source := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let context ← must (CompilerFacts.ofProgram runtime (← must (lowerProgram source)))
  let material ← must (World.ofDocument source)
  let mut empty ← must (World.ofMaterial #[] #[] #[] material.pointerBytes)
  -- Occupy a small numeric ID with another constructor before requesting u8.
  let (_,occupied) ← must ((World.internType (.tuple #[])).run empty)
  empty := occupied
  let keys := #["u8","u16","u32","u64","u128","i8","i16","i32","i64","i128","bool",
    "pointer_tag_integer","usize","isize","unit","unit_pointer_const","unit_pointer_mut",
    "imm_u8_pointer","imm_u8_pointer_pointer"]
  for key in keys do
    let expected ← must (CompilerPrimitiveFacts.primitiveType runtime key)
    let expectedTerm ← must (GenericInstantiationWorld.ofType material 4096 expected)
    let (actual,after) ← must ((CompilerFacts.primitiveTypeInWorld context key).run empty)
    empty := after
    check ((← must (GenericInstantiationWorld.ofType empty 4096 actual)) == expectedTerm)
      s!"empty-prefix primitive differs from compiler constructor: {key}"
    let (actual,_) ← must ((CompilerFacts.primitiveTypeInWorld context key).run material)
    check (actual == expected) s!"material primitive identity changed: {key}"
  check (empty.materialTypes.isEmpty && empty.definitions.isEmpty) "primitive borrowed material prefix"
  check (!((CompilerFacts.primitiveTypeInWorld context "missing_primitive").run empty).isOk)
    "unknown primitive key accepted"
  let wrongWidth ← must (World.ofMaterial #[] #[] #[] (if material.pointerBytes == 8 then 4 else 8))
  check (!((CompilerFacts.primitiveTypeInWorld context "usize").run wrongWidth).isOk)
    "primitive query ignored active world/target width mismatch"
  let ((array,discrTy,layout,value),after) ← must ((do
    let byte ← CompilerFacts.primitiveTypeInWorld context "u8"
    let usize ← CompilerFacts.primitiveTypeInWorld context "usize"
    let length ← World.internConstant (.Value usize ⟨#[.Leaf 2 (← get).pointerBytes],0⟩)
    let array ← World.internType (.array byte length)
    let discrTy ← CompilerFacts.requiredTypeInWorld context array "discriminant_type"
    let layout ← CompilerDiscriminantFacts.discriminantLayout context array
    let value ← CompilerDiscriminantFacts.discriminantValue context array 0
    pure (array,discrTy,layout,value)).run empty)
  check (value.isNone && layout.ty == discrTy && layout.layout.size.bytes == 1)
    "empty-prefix array discriminant query borrowed unrelated material ID"
  check (!((CompilerDiscriminantFacts.variantForDiscriminant context array 0).run after).isOk)
    "empty-prefix array acquired enum values"
  let some definition := source.definitions.find? (fun definition => definition.aliasDeclaration.isNone)
    | throw (IO.userError "missing non-alias definition for malformed alias control")
  let (alias,withAlias) ← must ((World.internType (.alias .free false ⟨definition.crateIndex,definition.index⟩ #[])).run material)
  check (!((CompilerDiscriminantFacts.discriminantValue context alias 0).run withAlias).isOk)
    "alias with missing raw declaration silently acquired non-enum result"
  check (!((CompilerFacts.requiredTypeInWorld context alias "discriminant_type").run withAlias).isOk)
    "alias with missing raw declaration acquired discriminant type"
  IO.println s!"PASS {keys.size} world primitive constructors, material identity, empty-prefix collision and array discriminants"
