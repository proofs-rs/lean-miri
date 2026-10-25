import Lean

namespace ExactJsonTotal218

open Lean

abbrev JsonTree := Std.DTreeMap.Internal.Impl String (fun _ => Json)
abbrev JsonMap := Std.TreeMap.Raw String Json

theorem jsonMapInnerSize (map : JsonMap) :
    sizeOf map.inner.inner + 2 = sizeOf map := by
  cases map with
  | mk raw =>
    cases raw with
    | mk tree =>
      simp [sizeOf, Std.TreeMap.Raw._sizeOf_1, Std.DTreeMap.Raw._sizeOf_1]
      omega

theorem jsonArrSize (xs : Array Json) :
    sizeOf (Json.arr xs) = sizeOf xs + 1 := by
  cases xs with
  | mk values =>
      induction values with
      | nil =>
          simp [sizeOf, Lean.Json._sizeOf_1, Array._sizeOf_1, List._sizeOf_1]
      | cons head tail ih =>
          have ih' := ih
          simp only [sizeOf, Lean.Json._sizeOf_1,
            Array._sizeOf_1, List._sizeOf_1] at ih'
          simp only [sizeOf, Lean.Json._sizeOf_1,
            Array._sizeOf_1, List._sizeOf_1]
          omega

mutual
  /-- Exact Boolean equality for JSON's raw structural representation. -/
  def jsonEq : Json → Json → Bool
    | .null, .null => true
    | .bool a, .bool b => decide (a = b)
    | .num a, .num b => decide (a = b)
    | .str a, .str b => decide (a = b)
    | .arr xs, .arr ys => arrayLoop xs ys 0
    | .obj xs, .obj ys => implEq xs.inner.inner ys.inner.inner
    | _, _ => false
  termination_by a b => (sizeOf a + sizeOf b, 0)
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals
      first
      | (have hx := jsonArrSize xs; have hy := jsonArrSize ys; omega)
      | (have hx := jsonMapInnerSize xs; have hy := jsonMapInnerSize ys; omega)

  def arrayLoop (xs ys : Array Json) (i : Nat) : Bool :=
    if h : i < xs.size then
      if h' : i < ys.size then
        jsonEq xs[i] ys[i] && arrayLoop xs ys (i + 1)
      else false
    else decide (xs.size = ys.size)
  termination_by (sizeOf xs + sizeOf ys, xs.size - i)
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals
      have hleft := Array.sizeOf_getElem xs i h
      have hright := Array.sizeOf_getElem ys i h'
      omega

  def implEq : JsonTree → JsonTree → Bool
    | .leaf, .leaf => true
    | .inner size key value left right, .inner size' key' value' left' right' =>
      decide (size = size') && decide (key = key') && jsonEq value value' &&
        implEq left left' && implEq right right'
    | _, _ => false
  termination_by a b => (sizeOf a + sizeOf b, 0)
  decreasing_by all_goals simp_wf; omega
end

#print axioms jsonEq
#print axioms arrayLoop
#print axioms implEq

end ExactJsonTotal218
