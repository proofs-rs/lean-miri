import MiriTests.Connected.Proofs.JsonDecidableEq213
import Miri.Input.Model

set_option autoImplicit false
open Lean Miri.Input

namespace TypedValueDecEq207

section
variable [DecidableEq Lean.Json]
deriving instance DecidableEq for UserTypeProjection
deriving instance DecidableEq for TaggedNode
end

private def listForallDec {α : Type} (p : α → Prop)
    (decideP : (x : α) → Decidable (p x)) :
    (xs : List α) → Decidable (∀ x, x ∈ xs → p x)
  | [] => isTrue (by simp)
  | x :: xs =>
    match decideP x with
    | isFalse hX => isFalse (by intro h; exact hX (h x (by simp)))
    | isTrue hX =>
      match listForallDec p decideP xs with
      | isFalse hXs =>
        isFalse (by
          intro h
          apply hXs
          intro y hY
          exact h y (by simp [hY]))
      | isTrue hXs =>
        isTrue (by
          intro y hY
          simp only [List.mem_cons] at hY
          rcases hY with hEq | hMem
          · cases hEq
            exact hX
          · exact hXs y hMem)

private def arrayDecEqWith {α : Type} (left right : Array α)
    (decideElem : (leftElem : α) → leftElem ∈ left →
      (rightElem : α) → rightElem ∈ right → Decidable (leftElem = rightElem)) :
    Decidable (left = right) := by
  by_cases hSize : left.size = right.size
  · let indices := List.finRange left.size
    let rightIndex := fun i : Fin left.size => Fin.cast hSize i
    let allEqual := listForallDec
      (fun i : Fin left.size => left[i] = right[rightIndex i])
      (fun i => decideElem left[i] (Array.getElem_mem i.isLt)
        right[rightIndex i] (Array.getElem_mem (rightIndex i).isLt))
      indices
    cases allEqual with
    | isTrue hAll =>
      apply isTrue
      apply Array.ext hSize
      intro i hLeft hRight
      exact hAll ⟨i, hLeft⟩ (by simp [indices])
    | isFalse hAll =>
      apply isFalse
      intro hArray
      apply hAll
      intro i hMem
      have hGet := (Array.ext_iff.mp hArray).2 i.val i.isLt (by omega)
      simpa [rightIndex] using hGet
  · apply isFalse
    intro hArray
    exact hSize (congrArg Array.size hArray)

private theorem typedArraySize (xs : Array TypedValue) :
    sizeOf (TypedValue.array xs) = sizeOf xs + 1 := by
  cases xs using Array.rec with
  | mk toList =>
    induction toList with
    | nil => rfl
    | cons head tail ih =>
      simp [sizeOf, TypedValue._sizeOf_1, TypedValue.rec_1,
        TypedValue.rec_2, TypedValue.rec_3, Array._sizeOf_1, List._sizeOf_1] at *
      omega

private theorem typedArrayChildLt (xs : Array TypedValue) (value : TypedValue)
    (h : value ∈ xs) : sizeOf value < sizeOf (TypedValue.array xs) := by
  have hMember := Array.sizeOf_lt_of_mem h
  rw [typedArraySize]
  omega

private theorem typedObjectChildLt (xs : Array (String × TypedValue))
    (field : String × TypedValue) (h : field ∈ xs) :
    sizeOf field.2 < sizeOf (TypedValue.object xs) := by
  cases xs using Array.rec with
  | mk values =>
    simp only [Array.mem_def] at h
    induction values with
    | nil => simp at h
    | cons head tail ih =>
      simp only [sizeOf, TypedValue._sizeOf_inst, TypedValue._sizeOf_1,
        Array._sizeOf_1, List._sizeOf_1, TypedValue.rec_4] at *
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst field
        omega
      · have hIH := ih h
        omega

private class MemberChildSize (α : Type) [SizeOf α] where
  child : α → TypedValue
  child_le : ∀ value, sizeOf (child value) ≤ sizeOf value

private instance : MemberChildSize TypedValue where
  child := id
  child_le := by intro value; change sizeOf value ≤ sizeOf value; exact Nat.le_refl _

private instance : MemberChildSize (String × TypedValue) where
  child := Prod.snd
  child_le := by
    intro pair
    cases pair with
    | mk key value =>
      simp [SizeOf.sizeOf, Prod._sizeOf_1]

private theorem arrayMemberChildSizeLt {α : Type} [SizeOf α] [MemberChildSize α]
    (values : Array α) (value : α) (h : value ∈ values) :
    sizeOf (MemberChildSize.child value) < sizeOf values := by
  have hMem := Array.sizeOf_lt_of_mem h
  have hChild := MemberChildSize.child_le value
  omega

section
variable [DecidableEq Lean.Json]

private def typedValueDecEq :
    (left right : TypedValue) → Decidable (left = right)
  | .scalar a, .scalar b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .diagnostic a, .diagnostic b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .typeRef a, .typeRef b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .allocationRef a, .allocationRef b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .instanceRef a, .instanceRef b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .localRef a, .localRef b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .blockRef a, .blockRef b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .sourceSpan a, .sourceSpan b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .sourceInfo a, .sourceInfo b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .binOperator av, .binOperator bv =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)
  | .unOperator av, .unOperator bv =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)
  | .userTypeProjection a, .userTypeProjection b =>

    match (inferInstance : Decidable (a = b)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      isTrue (by cases h0; rfl)

  | .array a, .array b =>
    match arrayDecEqWith a b (fun l hLeft r hRight => typedValueDecEq l r) with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)

  | .object a, .object b =>
    match arrayDecEqWith a b
        (fun leftElem hLeft rightElem hRight =>
          match leftElem, rightElem with
          | (leftKey, leftValue), (rightKey, rightValue) =>
            match (inferInstance : Decidable (leftKey = rightKey)) with
            | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
            | isTrue hKey =>
              match typedValueDecEq leftValue rightValue with
              | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
              | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
        ) with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)

  | .statement av af, .statement bv bf =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      match arrayDecEqWith af bf
          (fun leftElem hLeft rightElem hRight =>
            match leftElem, rightElem with
            | (leftKey, leftValue), (rightKey, rightValue) =>
              match (inferInstance : Decidable (leftKey = rightKey)) with
              | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
              | isTrue hKey =>
                match typedValueDecEq leftValue rightValue with
                | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
                | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
          ) with

      | isFalse hFields => isFalse (by intro hEq; cases hEq; exact hFields rfl)

      | isTrue hFields => isTrue (by cases h0; cases hFields; rfl)
  | .terminator av af, .terminator bv bf =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      match arrayDecEqWith af bf
          (fun leftElem hLeft rightElem hRight =>
            match leftElem, rightElem with
            | (leftKey, leftValue), (rightKey, rightValue) =>
              match (inferInstance : Decidable (leftKey = rightKey)) with
              | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
              | isTrue hKey =>
                match typedValueDecEq leftValue rightValue with
                | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
                | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
          ) with

      | isFalse hFields => isFalse (by intro hEq; cases hEq; exact hFields rfl)

      | isTrue hFields => isTrue (by cases h0; cases hFields; rfl)
  | .rvalue av af, .rvalue bv bf =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      match arrayDecEqWith af bf
          (fun leftElem hLeft rightElem hRight =>
            match leftElem, rightElem with
            | (leftKey, leftValue), (rightKey, rightValue) =>
              match (inferInstance : Decidable (leftKey = rightKey)) with
              | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
              | isTrue hKey =>
                match typedValueDecEq leftValue rightValue with
                | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
                | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
          ) with

      | isFalse hFields => isFalse (by intro hEq; cases hEq; exact hFields rfl)

      | isTrue hFields => isTrue (by cases h0; cases hFields; rfl)
  | .enumTag av atag ac, .enumTag bv btag bc =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      match (inferInstance : Decidable (atag = btag)) with

      | isFalse h1 => isFalse (by intro hEq; cases hEq; exact h1 rfl)

      | isTrue h1 =>

        match arrayDecEqWith ac bc
            (fun leftElem hLeft rightElem hRight =>
              match leftElem, rightElem with
              | (leftKey, leftValue), (rightKey, rightValue) =>
                match (inferInstance : Decidable (leftKey = rightKey)) with
                | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
                | isTrue hKey =>
                  match typedValueDecEq leftValue rightValue with
                  | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
                  | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
            ) with

        | isFalse hFields => isFalse (by intro hEq; cases hEq; exact hFields rfl)

        | isTrue hFields => isTrue (by cases h0; cases h1; cases hFields; rfl)

  | .operand av af, .operand bv bf =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      match arrayDecEqWith af bf
          (fun leftElem hLeft rightElem hRight =>
            match leftElem, rightElem with
            | (leftKey, leftValue), (rightKey, rightValue) =>
              match (inferInstance : Decidable (leftKey = rightKey)) with
              | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
              | isTrue hKey =>
                match typedValueDecEq leftValue rightValue with
                | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
                | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
          ) with

      | isFalse hFields => isFalse (by intro hEq; cases hEq; exact hFields rfl)

      | isTrue hFields => isTrue (by cases h0; cases hFields; rfl)
  | .projection av af, .projection bv bf =>

    match (inferInstance : Decidable (av = bv)) with

    | isFalse h0 => isFalse (by intro hEq; cases hEq; exact h0 rfl)

    | isTrue h0 =>

      match arrayDecEqWith af bf
          (fun leftElem hLeft rightElem hRight =>
            match leftElem, rightElem with
            | (leftKey, leftValue), (rightKey, rightValue) =>
              match (inferInstance : Decidable (leftKey = rightKey)) with
              | isFalse hKey => isFalse (by intro hPair; cases hPair; exact hKey rfl)
              | isTrue hKey =>
                match typedValueDecEq leftValue rightValue with
                | isTrue hValue => isTrue (by cases hKey; cases hValue; rfl)
                | isFalse hValue => isFalse (by intro hPair; cases hPair; exact hValue rfl)
          ) with

      | isFalse hFields => isFalse (by intro hEq; cases hEq; exact hFields rfl)

      | isTrue hFields => isTrue (by cases h0; cases hFields; rfl)

  | .scalar _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .array _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .object _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .scalar _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .array _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .object _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .diagnostic _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .array _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .array _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .array _, .object _ => isFalse (by intro hEq; cases hEq)

  | .array _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .array _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .array _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .array _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .array _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .array _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .array _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .array _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .array _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .array _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .array _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .array _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .array _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .array _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .array _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .array _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .object _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .object _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .object _, .array _ => isFalse (by intro hEq; cases hEq)

  | .object _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .object _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .object _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .object _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .object _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .object _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .object _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .object _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .object _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .object _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .object _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .object _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .object _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .object _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .object _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .object _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .array _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .object _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .typeRef _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .array _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .object _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .allocationRef _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .array _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .object _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .instanceRef _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .array _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .object _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .localRef _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .array _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .object _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .blockRef _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .array _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .object _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceSpan _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .array _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .object _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .sourceInfo _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .array _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .object _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .statement _ _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .array _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .object _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .terminator _ _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .array _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .object _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .rvalue _ _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .array _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .object _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .binOperator _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .array _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .object _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .unOperator _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .array _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .object _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .enumTag _ _ _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .array _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .object _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .operand _ _ => isFalse (by intro hEq; cases hEq)

  | .userTypeProjection _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .array _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .object _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .operand _ _, .projection _ _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .scalar _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .diagnostic _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .array _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .object _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .typeRef _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .allocationRef _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .instanceRef _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .localRef _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .blockRef _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .sourceSpan _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .sourceInfo _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .statement _ _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .terminator _ _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .rvalue _ _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .binOperator _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .unOperator _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .enumTag _ _ _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .userTypeProjection _ => isFalse (by intro hEq; cases hEq)

  | .projection _ _, .operand _ _ => isFalse (by intro hEq; cases hEq)

termination_by left right => sizeOf left + sizeOf right

decreasing_by
  all_goals
    simp_wf
    have hL := arrayMemberChildSizeLt _ _ hLeft
    have hR := arrayMemberChildSizeLt _ _ hRight
    simp [MemberChildSize.child] at hL hR
    omega

def typedValueDecidableEq : DecidableEq TypedValue := typedValueDecEq

end


def nestedEqualProbe : TypedValue :=
  .object #[
    ("array", .array #[.scalar (.bool true), .typeRef 3]),
    ("tail", .object #[("leaf", .scalar (.str "value"))])]

def nestedDifferentProbe : TypedValue :=
  .object #[
    ("array", .array #[.scalar (.bool true), .typeRef 4]),
    ("tail", .object #[("leaf", .scalar (.str "value"))])]

#eval (typedValueDecEq nestedEqualProbe nestedEqualProbe).decide
#eval (typedValueDecEq nestedEqualProbe nestedDifferentProbe).decide
#eval (typedValueDecEq (.array #[nestedEqualProbe]) (.array #[nestedEqualProbe])).decide
#eval (typedValueDecEq (.array #[nestedEqualProbe]) (.array #[nestedDifferentProbe])).decide

theorem typedValueDecEq_reflect (left right : TypedValue) :
    (typedValueDecEq left right).decide = true ↔ left = right := by
  cases h : typedValueDecEq left right with
  | isTrue hEq => simp [h, hEq]
  | isFalse hNe => simp [h, hNe]

#print axioms typedValueDecidableEq
#print axioms typedValueDecEq
#print axioms typedValueDecEq_reflect

end TypedValueDecEq207
