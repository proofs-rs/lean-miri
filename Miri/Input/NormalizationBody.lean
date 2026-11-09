import Miri.Input.Model.Types

/-! Normalization evidence refers directly to the immutable body pool. -/
namespace Miri.Input.NormalizationBody
def resolve (id : BodyId) (bodies : Array Body) : Except String Body := do
  let some body := bodies[id]? | throw s!"normalized compiler body ID {id} out of bounds"
  pure body

end Miri.Input.NormalizationBody
