import Miri.Frontend.ImportMIR
import Miri.Input.EvalPreparation
import Miri.Input.CompilerGlobalBytes
import Lean.Elab.Deriving.ToExpr
import Std.Data.HashMap.Lemmas

/-! Safe quotation of the typed preparation data shared by the two fixed inputs.
Hash tables are reconstructed from their entries; dependent allocation-image
indexes use the public constructor. No quotation supplies an execution theorem. -/

open Lean Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

namespace DuplicatePrefix.Reflection

def natMap {α : Type} (entries : List (Nat × α)) : Std.HashMap Nat α :=
  Std.HashMap.ofList entries
private def uint64Map {α : Type} (entries : List (UInt64 × α)) : Std.HashMap UInt64 α :=
  Std.HashMap.ofList entries
private def pairMap {α : Type} (entries : List ((Nat × Nat) × α)) : Std.HashMap (Nat × Nat) α :=
  Std.HashMap.ofList entries
private def stringMap {α : Type} (entries : List (String × α)) : Std.HashMap String α :=
  Std.HashMap.ofList entries

theorem natMap_getD {α : Type} (entries : List (Nat × α)) (key : Nat) (fallback : α) :
    (natMap entries).getD key fallback =
      (entries.findSomeRev? fun (candidate, value) => if candidate == key then some value else none).getD fallback := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  simp only [natMap, Std.HashMap.ofList_eq_insertMany_empty,
    Std.HashMap.getElem?_insertMany_list, Std.HashMap.getElem?_empty, Option.or_none]

theorem natMap_getElem {α : Type} (entries : List (Nat × α)) (key : Nat) :
    (natMap entries)[key]? =
      entries.findSomeRev? (fun (candidate, value) => if candidate == key then some value else none) := by
  simp only [natMap, Std.HashMap.ofList_eq_insertMany_empty,
    Std.HashMap.getElem?_insertMany_list, Std.HashMap.getElem?_empty, Option.or_none]

instance {α : Type} [ToExpr α] : ToExpr (Std.HashMap Nat α) where
  toTypeExpr := mkApp2 (mkConst ``Std.HashMap [0, 0]) (toTypeExpr Nat) (toTypeExpr α)
  toExpr value := mkApp2 (mkConst ``natMap) (toTypeExpr α) (toExpr value.toList)
instance {α : Type} [ToExpr α] : ToExpr (Std.HashMap UInt64 α) where
  toTypeExpr := mkApp2 (mkConst ``Std.HashMap [0, 0]) (toTypeExpr UInt64) (toTypeExpr α)
  toExpr value := mkApp2 (mkConst ``uint64Map) (toTypeExpr α) (toExpr value.toList)
instance {α : Type} [ToExpr α] : ToExpr (Std.HashMap (Nat × Nat) α) where
  toTypeExpr := mkApp2 (mkConst ``Std.HashMap [0, 0]) (toTypeExpr (Nat × Nat)) (toTypeExpr α)
  toExpr value := mkApp2 (mkConst ``pairMap) (toTypeExpr α) (toExpr value.toList)
instance {α : Type} [ToExpr α] : ToExpr (Std.HashMap String α) where
  toTypeExpr := mkApp2 (mkConst ``Std.HashMap [0, 0]) (toTypeExpr String) (toTypeExpr α)
  toExpr value := mkApp2 (mkConst ``stringMap) (toTypeExpr α) (toExpr value.toList)

open Lean Elab Command in
private partial def deriveQuote (name : Name) : StateT NameSet CommandElabM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let some info := (← getEnv).find? name | return
  if !name.toString.startsWith "Miri." then return
  match info with
  | .inductInfo indInfo =>
    let existing ← liftM <| liftTermElabM <| Meta.forallTelescopeReducing indInfo.type fun xs _ => do
      Meta.synthInstance? (← Meta.mkAppM ``ToExpr
        #[mkAppN (mkConst name (indInfo.levelParams.map Level.param)) xs])
    if existing.isSome then return
    for ctor in indInfo.ctors do
      for dependency in (← getConstInfo ctor).type.getUsedConstants do
        if dependency != name then deriveQuote dependency
    liftM <| elabCommand (← `(deriving instance ToExpr for $(mkIdent name)))
  | .defnInfo definition =>
    let typeFormer ← liftM <| liftTermElabM <|
      Meta.forallTelescopeReducing definition.type fun _ body => pure body.isSort
    if typeFormer then
      for dependency in definition.value.getUsedConstants do
        if dependency != name then deriveQuote dependency
  | _ => pure ()

open Lean Elab Command in
elab "derive_duplicate_prefix_quote " names:ident,* : command => do
  let resolved ← names.getElems.mapM fun name => resolveGlobalConstNoOverload name.raw
  discard <| (resolved.forM deriveQuote).run {}

deriving instance ToExpr for Except
deriving instance ToExpr for ByteArray

private def checkedVector {α : Type u} (length : Nat) (items : Array α)
    (size : items.size = length) : Vector α length := ⟨items, size⟩

instance {α : Type u} [ToLevel.{u}] [ToExpr α] {length : Nat} : ToExpr (Vector α length) where
  toTypeExpr := mkApp2 (mkConst ``Vector [toLevel.{u}]) (toTypeExpr α) (toExpr length)
  toExpr value := mkApp4 (mkConst ``checkedVector [toLevel.{u}]) (toTypeExpr α)
    (toExpr length) (toExpr value.toArray)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr length))

derive_duplicate_prefix_quote Allocation

instance : ToExpr AllocationImage.Imported where
  toTypeExpr := mkConst ``AllocationImage.Imported
  toExpr value := mkApp2 (mkConst ``AllocationImage.Imported.ofSource)
    (toExpr value.source) (toExpr value.initializers)

section
variable [ToExpr ImportDocument]
derive_duplicate_prefix_quote LoweredProgram, RuntimeMetadata, RuntimeMetadataError, FnAbi
section
variable [ToExpr LoweredProgram] [ToExpr RuntimeMetadata]
derive_duplicate_prefix_quote EvalPreparation.Prepared, CompilerGlobalBytes.Prepared
end
end

end DuplicatePrefix.Reflection
