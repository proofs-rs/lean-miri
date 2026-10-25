import MiriTests.Connected.Proofs.ExactJsonTotal218

open Lean
namespace ExactJson213
open ExactJsonTotal218

abbrev ArrayJsonSound (xs : Array Json) : Prop :=
  (∀ i (hi : i < xs.size) right, jsonEq xs[i] right = true → xs[i] = right) ∧
  (∀ ys, arrayLoop xs ys 0 = true → xs = ys)

/-- Array-loop soundness from the recursive JSON proof for each indexed left value. -/
theorem arrayLoopSoundAux
    (xs ys : Array Json) (i : Nat)
    (hpre : ∀ j (hjx : j < xs.size) (hjy : j < ys.size), j < i → xs[j] = ys[j])
    (jsonSound : ∀ i (hi : i < xs.size) right,
      jsonEq xs[i] right = true → xs[i] = right)
    (hloop : arrayLoop xs ys i = true) : xs = ys := by
  unfold arrayLoop at hloop
  split at hloop
  · rename_i hx
    split at hloop
    · rename_i hy
      simp only [Bool.and_eq_true] at hloop
      rcases hloop with ⟨hcurrent, hnext⟩
      have hcurrentEq := jsonSound i hx ys[i] hcurrent
      have hpre' : ∀ j (hjx : j < xs.size) (hjy : j < ys.size), j < i + 1 → xs[j] = ys[j] := by
        intro j hjx hjy hj
        by_cases hji : j < i
        · exact hpre j hjx hjy hji
        · have hEq : j = i := by omega
          subst j
          simpa using hcurrentEq
      exact arrayLoopSoundAux xs ys (i + 1) hpre' jsonSound hnext
    · simp at hloop
  · have hsize : xs.size = ys.size := of_decide_eq_true hloop
    apply Array.ext hsize
    intro j hjx hjy
    have hj : j < i := by omega
    exact hpre j hjx hjy hj
termination_by xs.size - i
decreasing_by omega

theorem arrayLoopSound
    (xs ys : Array Json)
    (jsonSound : ∀ i (hi : i < xs.size) right,
      jsonEq xs[i] right = true → xs[i] = right)
    (hloop : arrayLoop xs ys 0 = true) : xs = ys := by
  apply arrayLoopSoundAux xs ys 0
  · intro j hjx hjy hj
    omega
  · exact jsonSound
  · exact hloop

theorem jsonEqSound : (left : Json) → ∀ right, jsonEq left right = true → left = right :=
  Lean.Json.rec
    (motive_1 := fun left => ∀ right, jsonEq left right = true → left = right)
    (motive_2 := fun xs => ArrayJsonSound xs)
    (motive_3 := fun left => ∀ right : Std.TreeMap.Raw String Json,
      implEq left.inner.inner right.inner.inner = true → left = right)
    (motive_4 := fun values => ∀ value, value ∈ values →
      ∀ right, jsonEq value right = true → value = right)
    (motive_5 := fun left => ∀ right : Std.DTreeMap.Raw String (fun _ => Json) compare,
      implEq left.inner right.inner = true → left = right)
    (motive_6 := fun left => ∀ right : JsonTree,
      implEq left right = true → left = right)
    (by
      intro right h
      cases right <;> simp [jsonEq] at h ⊢)
    (by
      intro value right h
      cases right with
      | bool other =>
          have heq : value = other := by simpa [jsonEq] using h
          cases heq
          rfl
      | _ => simp [jsonEq] at h)
    (by
      intro value right h
      cases right with
      | num other =>
          have heq : value = other := by simpa [jsonEq] using h
          cases heq
          rfl
      | _ => simp [jsonEq] at h)
    (by
      intro value right h
      cases right with
      | str other =>
          have heq : value = other := by simpa [jsonEq] using h
          cases heq
          rfl
      | _ => simp [jsonEq] at h)
    (by
      intro elems ih right h
      cases right with
      | arr other =>
          have harray : arrayLoop elems other 0 = true := by simpa [jsonEq] using h
          have heq := ih.2 other harray
          cases heq
          rfl
      | _ => simp [jsonEq] at h)
    (by
      intro pairs ih right h
      cases right with
      | obj other =>
          have htree : implEq pairs.inner.inner other.inner.inner = true := by
            simpa [jsonEq] using h
          have heq := ih other htree
          cases heq
          rfl
      | _ => simp [jsonEq] at h)
    (by
      intro toList listIH
      let values : Array Json := ⟨toList⟩
      constructor
      · intro i hi other h
        have hmem : values[i] ∈ toList := by
          simpa [values] using (Array.getElem_mem_toList (xs := values) hi)
        exact listIH values[i] hmem other h
      · intro other hloop
        apply arrayLoopSound (xs := values) (ys := other)
        · intro i hi other' h'
          have hmem : values[i] ∈ toList := by
            simpa [values] using (Array.getElem_mem_toList (xs := values) hi)
          exact listIH values[i] hmem other' h'
        · exact hloop)
    (by
      intro raw rawIH right h
      cases right with
      | mk other =>
          have heq := rawIH other h
          cases heq
          rfl)
    (by
      intro value hmem right h
      simp at hmem)
    (by
      intro head tail headIH tailIH value hmem right h
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact headIH right h
      · exact tailIH value htail right h)
    (by
      intro tree treeIH right h
      cases right with
      | mk other =>
          have heq := treeIH other h
          cases heq
          rfl)
    (by
      intro size key value left right valueIH leftIH rightIH other h
      cases other with
      | leaf => simp [implEq] at h
      | inner size' key' value' left' right' =>
          simp only [implEq, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨⟨⟨hSize, hKey⟩, hValue⟩, hLeft⟩, hRight⟩
          subst size'
          subst key'
          have hValueEq := valueIH value' hValue
          have hLeftEq := leftIH left' hLeft
          have hRightEq := rightIH right' hRight
          subst value'
          subst left'
          subst right'
          rfl)
    (by
      intro right h
      cases right <;> simp [implEq] at h ⊢)

theorem arrayLoopSelfAux (xs : Array Json) (i : Nat)
    (child : ∀ j (hj : j < xs.size), jsonEq xs[j] xs[j] = true) :
    arrayLoop xs xs i = true := by
  unfold arrayLoop
  split
  · rename_i hx
    simp only [Bool.and_eq_true]
    constructor
    · exact child i hx
    · exact arrayLoopSelfAux xs (i + 1) child
  · simp
termination_by xs.size - i
decreasing_by omega

theorem jsonEqSelf (left : Json) : jsonEq left left = true :=
  Lean.Json.rec
    (motive_1 := fun left => jsonEq left left = true)
    (motive_2 := fun xs =>
      (∀ i (hi : i < xs.size), jsonEq xs[i] xs[i] = true) ∧
      arrayLoop xs xs 0 = true)
    (motive_3 := fun map => implEq map.inner.inner map.inner.inner = true)
    (motive_4 := fun values =>
      ∀ value, value ∈ values → jsonEq value value = true)
    (motive_5 := fun raw => implEq raw.inner raw.inner = true)
    (motive_6 := fun tree => implEq tree tree = true)
    (by simp [jsonEq])
    (by intro value; simp [jsonEq])
    (by intro value; simp [jsonEq])
    (by intro value; simp [jsonEq])
    (by intro elems ih; simpa [jsonEq] using ih.2)
    (by intro pairs ih; simpa [jsonEq] using ih)
    (by
      intro values listIH
      let xs : Array Json := ⟨values⟩
      constructor
      · intro i hi
        have hmem : xs[i] ∈ values := by
          exact Array.getElem_mem_toList (xs := xs) hi
        exact listIH xs[i] hmem
      · apply arrayLoopSelfAux xs 0
        intro i hi
        have hmem : xs[i] ∈ values := by
          exact Array.getElem_mem_toList (xs := xs) hi
        exact listIH xs[i] hmem)
    (by intro raw ih; exact ih)
    (by intro value hmem; simp at hmem)
    (by
      intro head tail headIH tailIH value hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact headIH
      · exact tailIH value htail)
    (by intro tree ih; exact ih)
    (by
      intro size key value left right valueIH leftIH rightIH
      simp [implEq, valueIH, leftIH, rightIH])
    (by simp [implEq])
    left

def jsonDecEq (left right : Json) : Decidable (left = right) :=
  if h : jsonEq left right = true then
    isTrue (jsonEqSound left right h)
  else
    isFalse (by
      intro hEq
      cases hEq
      exact h (jsonEqSelf left))

instance jsonDecidableEq : DecidableEq Json := jsonDecEq

def decEqBool (left right : Json) : Bool :=
  match jsonDecEq left right with
  | .isTrue _ => true
  | .isFalse _ => false

def sampleJson : Json :=
  .arr #[.null, .bool true, .str "nested", Json.mkObj [("x", .arr #[.bool false])]]

#eval decEqBool sampleJson sampleJson
#eval decEqBool sampleJson .null
#eval decide (sampleJson = sampleJson)
#eval decide (sampleJson = Json.null)
#eval decEqBool (.num (.mk 1 0)) (.num (.mk 1 0))
#eval decEqBool (.num (.mk 1 0)) (.num (.mk 10 1))

#print axioms jsonEqSound
#print axioms jsonEqSelf
#print axioms jsonDecEq
#print axioms jsonDecidableEq
end ExactJson213
