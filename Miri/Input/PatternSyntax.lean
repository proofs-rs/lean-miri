import Miri.Input.Model
import Miri.Input.GenericSubstitution
/-! Lossless TyKind::Pat syntax from pinned rustc 8144389c895d. Range
endpoints retain TypeConst identities; this bridge does not evaluate them or
substitute layout/validity query answers. -/
namespace Miri.Input
mutual
private def patternDecEq (a b : CompilerPattern) : Decidable (a = b) :=
  match a,b with
  | .range a b,.range c d => decidable_of_iff (a = c ∧ b = d) (by simp)
  | .or a,.or b =>
    haveI : Decidable (a.toList = b.toList) := patternsDecEq a.toList b.toList
    decidable_of_iff (a.toList = b.toList) (by simp)
  | .notNull,.notNull => isTrue rfl
  | .range ..,.or .. | .range ..,.notNull | .or ..,.range .. | .or ..,.notNull
  | .notNull,.range .. | .notNull,.or .. => isFalse (by intro h; cases h)
private def patternsDecEq (a b : List CompilerPattern) : Decidable (a = b) :=
  match a,b with
  | [],[] => isTrue rfl
  | a::as,b::bs =>
    haveI := patternDecEq a b
    haveI := patternsDecEq as bs
    decidable_of_iff (a = b ∧ as = bs) (by simp)
  | [],_::_ | _::_,[] => isFalse (by intro h; cases h)
end
instance : DecidableEq CompilerPattern := patternDecEq
deriving instance Repr for CompilerPattern

namespace CompilerPattern
/-- Every range endpoint remains a constant identity in this World. -/
def constantChildren : CompilerPattern → Array TypeConstantId
  | .range start finish => #[start,finish]
  | .notNull => #[]
  | .or patterns => patterns.foldl (fun result pattern => result ++ constantChildren pattern) #[]

def mapConstants [Monad m] [MonadExceptOf String m]
    (constant : TypeConstantId → m TypeConstantId) : Nat → CompilerPattern → m CompilerPattern
  | 0,_ => throw "pattern source normalization exhausted"
  | _ + 1,.notNull => pure .notNull
  | _ + 1,.range start finish => return .range (← constant start) (← constant finish)
  | fuel + 1,.or patterns => return .or (← patterns.mapM (mapConstants constant fuel))

def write [Monad m] [MonadExceptOf String m]
    (constant : TypeConstantId → m GenericSubstitution.Term) : Nat → CompilerPattern → m GenericSubstitution.Term
  | 0,_ => throw "pattern source reification exhausted"
  | _ + 1,.notNull => pure (.atom .aggregate "pattern_not_null" "")
  | _ + 1,.range start finish => do
    pure (.node .aggregate "pattern_range" "" (.cons (← constant start) (.cons (← constant finish) .nil)))
  | fuel + 1,.or patterns => do
    pure (.node .aggregate "pattern_or" "" (GenericSubstitution.Terms.ofArray (← patterns.mapM (write constant fuel))))

private def arrayOfTerms : GenericSubstitution.Terms → Array GenericSubstitution.Term
  | .nil => #[] | .cons head tail => #[head] ++ arrayOfTerms tail

def read [Monad m] [MonadExceptOf String m]
    (constant : GenericSubstitution.Term → m TypeConstantId) : Nat → GenericSubstitution.Term → m CompilerPattern
  | 0,_ => throw "pattern source construction exhausted"
  | _ + 1,.atom .aggregate "pattern_not_null" "" => pure .notNull
  | _ + 1,.node .aggregate "pattern_range" "" (.cons start (.cons finish .nil)) =>
    return .range (← constant start) (← constant finish)
  | fuel + 1,.node .aggregate "pattern_or" "" children =>
    return .or (← (arrayOfTerms children).mapM (read constant fuel))
  | _ + 1,_ => throw "pattern source constructor is malformed"
end CompilerPattern
end Miri.Input
