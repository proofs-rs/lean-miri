import Miri.Input.AdtDeclaration

open Miri.Input Miri.Input.GenericSubstitution Miri.Input.AdtDeclaration

private def u8 : Term := .atom .type "uint" "u8"
private def template (fields : Array FieldTemplate) : DefinitionTemplate :=
  {parameters := #[], typeExpression := .definition .type "adt" ⟨0,1⟩ .nil,
   signatureExpression := none, fields}
private def field (variant index : Nat) : FieldTemplate := ⟨variant,index,u8⟩
private def safety (variant index : Nat) (unsafeField : Bool := false) : FieldSafety :=
  ⟨variant,index,unsafeField,"component_field"⟩
private def material (kind : AdtKind) (variants : Nat) (fields : Array FieldSafety)
    (lang : Option String := none) : Material :=
  { kind := kind
    variantCount := variants
    variantNames := Array.replicate variants "ComponentVariant"
    fields := fields
    langItem := lang
    representation := {
      integer := none
      alignBytes := none
      packBytes := none
      flagsBits := 0
      scalableElement := none
      fieldShuffleSeed := 0 } }
private def accepted : Except String Unit → Bool
  | .ok _ => true | .error _ => false
example : accepted ((material .structKind 1 #[safety 0 0]).validate (template #[field 0 0])) = true := by decide +kernel
example : accepted ((material .enumKind 3 #[safety 1 0, safety 2 0 true]).validate
    (template #[field 1 0, field 2 0])) = true := by decide +kernel
example : accepted ((material .enumKind 0 #[]).validate (template #[])) = true := by decide +kernel
example : accepted ((material .unionKind 2 #[]).validate (template #[])) = false := by decide +kernel
example : accepted ((material .structKind 1 #[]).validate (template #[field 0 0])) = false := by decide +kernel
example : accepted ((material .structKind 1 #[safety 0 1]).validate (template #[field 0 0])) = false := by decide +kernel
example : accepted ((material .enumKind 2 #[safety 2 0]).validate (template #[field 2 0])) = false := by decide +kernel
example : accepted ((material .enumKind 2 #[safety 1 0,safety 0 0]).validate (template #[field 1 0,field 0 0])) = false := by decide +kernel
example : accepted ((material .structKind 1 #[safety 0 1]).validate (template #[field 0 1])) = false := by decide +kernel
example : accepted ((material .enumKind 0 #[] (some "phantom_data")).validate (template #[])) = false := by decide +kernel
example : (material .structKind 1 #[] (some "phantom_data")).isPhantomData = true := by decide +kernel
example : (material .structKind 1 #[safety 0 0 true]).hasUnsafeFields = true := by decide +kernel
example : accepted (({ (material .structKind 1 #[]) with variantNames := #[] }).validate
    (template #[])) = false := by decide +kernel
