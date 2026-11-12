import Miri.Input.Model.Types

/-! Monomorphic `Ty::is_sized`, pinned rustc
8144389c895da997dbdecaa635e41d6a50be6ffd:
* `rustc_middle/src/ty/sty.rs::has_trivial_sizedness`;
* `rustc_middle/src/ty/adt.rs::sizedness_constraint`;
* `rustc_next_trait_solver/src/solve/assembly/structural_traits.rs`::
  `instantiate_constituent_tys_for_sizedness_trait`.

The callback supplies normalized shapes under fully_monomorphized's empty
parameter environment. Struct field types are instantiated material. For a
well-formed monomorphic struct, Sized depends only on its trailing field;
nontrailing fields are required to be Sized by the Rust definition. The rustc
constraint's early simplification of always-Sized fields is an optimization.
Enums/unions have no sizedness constraint. No layout data is inspected.

Pattern and UnsafeBinder are true in the pinned public query's trivial fast
path, independent of their inner node. `none` denotes an unresolved alias,
never an unsized result. Missing material/fuel exhaustion remain errors. -/
namespace Miri.Input.StructuralSized

def query (shape : TypeId → Except String TypeShape) :
    Nat → TypeId → Except String (Option Bool)
  | 0, _ => .error "structural Sized recursion exhausted"
  | fuel + 1, ty => do
    match ← shape ty with
    | .str | .slice _ | .dynamicTraitObject .. | .foreign _ => pure (some false)
    | .tuple elements =>
      match elements.back? with
      | none => pure (some true)
      | some last => query shape fuel last
    | .adt data =>
      if data.kind != .structKind then return some true
      unless data.variants.size == 1 do throw "Sized struct material requires one variant"
      let some variant := data.variants[0]?
        | throw "Sized struct variant material absent"
      match variant.fields.back? with
      | none => pure (some true)
      | some last => query shape fuel last.typeId
    | .alias .. => pure none
    | _ => pure (some true)

end Miri.Input.StructuralSized
