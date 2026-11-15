import Miri.Frontend.Foundation
import Miri.MIR.Syntax

/-! Exact pointer identity retained by the finite source parser. Bare legacy
pointer kind strings omit mutability/region and deliberately fail closed. -/
namespace Miri.Frontend.Foundation

structure PointerKindInfo where
  mutability : MIR.Mutability
  region : Option MIR.Region

def pointerKindInfo : String → Except String PointerKindInfo
  | "raw_pointer_const" => pure ⟨.Not, none⟩
  | "raw_pointer_mut" => pure ⟨.Mut, none⟩
  | "reference_erased_const" => pure ⟨.Not, some .Erased⟩
  | "reference_erased_mut" => pure ⟨.Mut, some .Erased⟩
  | "reference_static_const" => pure ⟨.Not, some .Static⟩
  | "reference_static_mut" => pure ⟨.Mut, some .Static⟩
  | _ => throw "pointer identity is missing or has unsupported mutability/region"

end Miri.Frontend.Foundation
