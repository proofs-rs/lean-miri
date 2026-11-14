import Miri.Input.TraitSelection.StructuralAuto

/-! Raw source component checks, not fabricated compiler answers. The neutral
repr is irrelevant to trait constituents; actual wire fidelity has fresh rustc
oracle checks separately. No source type table exists in these cases. -/
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error a, .error b => match decEq a b with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok _, .error _ => .isFalse (by intro same; cases same)
  | .error _, .ok _ => .isFalse (by intro same; cases same)
private def u16 : Term := .atom .type "uint" "u16"
private def nominal (index : Nat) (argument : Term) : Term :=
  .definition .type "adt" ⟨0,index⟩ (.ofArray #[argument])
private def source : StructuralAuto.SourceAdt := fun identity => do
  unless identity.crateIndex == 0 && (#[1,2,3] : Array Nat).contains identity.index do
    throw "component ADT source absent"
  let phantom := identity.index == 2
  let unsafeField := identity.index == 3
  let template : DefinitionTemplate := {
    parameters := #[.type]
    typeExpression := nominal identity.index (.parameter .type 0)
    signatureExpression := none
    fields := if phantom then #[] else #[⟨0,0,.parameter .type 0⟩] }
  let material : AdtDeclaration.Material := {
    representation := {
      integer := none
      alignBytes := none
      packBytes := none
      flagsBits := 0
      scalableElement := none
      fieldShuffleSeed := 0 }
    flagsBits := 4
    nonnullOptimizationGuaranteed := false
    langItem := if phantom then some "phantom_data" else none
    variants := #[⟨identity,none,"Component",.relative 0,if phantom then 0 else 1,0⟩]
    fields := if phantom then #[] else #[⟨0,0,unsafeField,"component_field",⟨identity.crateIndex,identity.index + 1000⟩,none,none,none⟩]
    }
  pure (material,template)
example : StructuralAuto.query source false 50 (nominal 1 u16) = .ok (some #[u16]) := by decide +kernel
example : StructuralAuto.query source true 50 (nominal 3 u16) = .ok none := by decide +kernel
example : StructuralAuto.query source false 50 (nominal 3 u16) = .ok (some #[u16]) := by decide +kernel
example : StructuralAuto.query source false 50 (nominal 2 u16) = .ok (some #[u16]) := by decide +kernel
example : StructuralAuto.query source false 50 (nominal 4 u16) = .error "component ADT source absent" := by decide +kernel
example : StructuralAuto.query source false 50 (.node .type "tuple" "" (.ofArray #[u16,nominal 1 u16])) =
    .ok (some #[u16,nominal 1 u16]) := by decide +kernel
example : StructuralAuto.query source false 50 (.node .type "raw_pointer" "mutable" (.ofArray #[u16])) =
    .ok (some #[u16]) := by decide +kernel
example : StructuralAuto.query source false 50 (.node .type "array" "" (.ofArray #[u16,.atom .constant "value" ""])) =
    .ok (some #[u16]) := by decide +kernel
example : StructuralAuto.query source false 50 (.atom .type "uint" "u16") = .ok (some #[]) := by decide +kernel
example : StructuralAuto.query source false 50 (.atom .type "str" "") =
    .ok (some #[.node .type "slice" "" (.ofArray #[.atom .type "uint" "u8"])]) := by decide +kernel
example : StructuralAuto.query source false 50 (.definition .type "foreign" ⟨0,5⟩ .nil) =
    .error "foreign auto-trait candidate requires default-bound source context" := by decide +kernel
example : StructuralAuto.query source false 50 (.node .type "unsafe_binder" "" .nil) =
    .error "auto-trait unsafe binder requires universe-aware constituent instantiation" := by decide +kernel
