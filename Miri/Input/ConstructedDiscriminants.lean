import Miri.Input.Model.Types

/-! Pinned rustc_middle/ty/sty.rs::discriminant_ty returns u8 for array,
raw-pointer and reference types. They also have no discriminant enumeration
(only enums/coroutines do), independently of their physical layout. -/
namespace Miri.Input.ConstructedDiscriminants

def supported : TypeShape → Bool
  | .array .. | .rawPointer .. | .reference .. => true
  | _ => false

def info (shape : TypeShape) : Option DiscriminantInfo :=
  if supported shape then some ⟨false,none,#[]⟩ else none

end Miri.Input.ConstructedDiscriminants
