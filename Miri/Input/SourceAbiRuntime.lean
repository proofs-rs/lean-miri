import Miri.Input.SourceAbi
import Miri.Input.ConcreteTypeQueries

namespace Miri.Input.SourceAbiRuntime
open Miri.ABI

def pointeeInfo (runtime : RuntimeMetadata) (policy : SourceAbiPolicy)
    (layout : TyAndLayout TypeId) (offset : Size) : Except String (Option SourceAbi.PointeeInfo) :=
  go (2 * runtime.source.types.size + 2) layout offset
where
  go (fuel : Nat) (layout : TyAndLayout TypeId) (offset : Size) :
      Except String (Option SourceAbi.PointeeInfo) := do
    let .succ fuel := fuel | throw "recursive source layout in pointee-info calculation"
    let node ← runtime.node layout.ty |>.mapError toString
    match node.shape with
    | .rawPointer .. | .functionPointer .. =>
      if offset.bytes == 0 then return some ⟨Size.ZERO, Align.ONE, none⟩
    | .reference pointee mutability _ =>
      if offset.bytes == 0 then
        let pointee ← runtime.lookup pointee |>.mapError toString
        match mutability with
        | .Not =>
          let frozen ← if policy.optimize then
            ConcreteTypeQueries.boolean runtime pointee.ty "is_freeze" else pure false
          return some ⟨if frozen then pointee.layout.size else Size.ZERO,
            pointee.layout.align.abi, some (.shared frozen)⟩
        | .Mut =>
          let unpin ← if policy.optimize then do
            if !(← ConcreteTypeQueries.boolean runtime pointee.ty "is_unpin") then pure false
            else ConcreteTypeQueries.boolean runtime pointee.ty "is_unsafe_unpin"
            else pure false
          return some ⟨if unpin then pointee.layout.size else Size.ZERO,
            pointee.layout.align.abi, some (.mutable unpin)⟩
    | _ => pure ()
    if offset.bytes == 0 && (← ConcreteTypeQueries.boolean runtime layout.ty "is_box") then
      let some pointeeId ← ConcreteTypeQueries.optionalType runtime layout.ty "boxed_type"
        | throw "compiler query boxed_type returned None"
      let pointee ← runtime.lookup pointeeId |>.mapError toString
      let unpin ← if policy.optimize then do
        if !(← ConcreteTypeQueries.boolean runtime pointeeId "is_unpin") then pure false
        else ConcreteTypeQueries.boolean runtime pointeeId "is_unsafe_unpin"
        else pure false
      return some ⟨if unpin then pointee.layout.size else Size.ZERO,
        pointee.layout.align.abi, some (.box unpin (← ConcreteTypeQueries.boolean runtime layout.ty "is_global_box"))⟩
    let variant ← match layout.layout.variants with
      | .Multiple _ (.Niche untagged _ _ start) field variants =>
        let fieldOffset ← layout.layout.fields.offset field |>.mapError reprStr
        if variants.size == 2 && fieldOffset == offset && start == 0 then
          some <$> (runtime.forVariant layout untagged |>.mapError toString)
        else pure none
      | .Multiple .. => pure none
      | _ => pure (some layout)
    let mut result := none
    if let some variant := variant then
      if !(match variant.layout.fields with | .Union _ => true | _ => false) then
        let pointerEnd := offset.bytes + runtime.target.defaultAddressSpacePointerSpec.pointerSize.bytes
        for index in [:variant.layout.fields.count] do
          let start ← variant.layout.fields.offset index |>.mapError reprStr
          if start.bytes <= offset.bytes then
            let field ← runtime.field variant index |>.mapError toString
            if pointerEnd <= start.bytes + field.layout.size.bytes then
              result ← go fuel field (Size.ofBytes (offset.bytes - start.bytes))
              if result.isSome then break
    if (← ConcreteTypeQueries.boolean runtime layout.ty "is_like_maybe_dangling") then
      result := result.map fun info => {info with safe := none, size := Size.ZERO}
    return result

def thinSelf (runtime : RuntimeMetadata) (layout : TyAndLayout TypeId) :
    Except String (TyAndLayout TypeId) := do
  let pointer ← if layout.layout.isUnsized then do
    let some source := runtime.source.types.find? (fun node =>
      match node.shape with
      | .rawPointer pointee .Mut => pointee == layout.ty
      | _ => false)
      | throw "virtual ABI needs pointer-to-unsized receiver type"
    runtime.lookup source.id |>.mapError toString
  else descend (runtime.source.types.size + 1) layout
  let some unitPointer := runtime.source.types.find? (fun node =>
      match node.shape with
      | .rawPointer pointee .Mut =>
        match runtime.source.types[pointee]? with
        | some {shape := .tuple elements, ..} => elements.isEmpty
        | _ => false
      | _ => false)
    | throw "virtual ABI needs concrete *mut () type"
  let thin ← runtime.lookup unitPointer.id |>.mapError toString
  return ⟨pointer.ty, thin.layout⟩
where
  descend (fuel : Nat) (pointer : TyAndLayout TypeId) : Except String (TyAndLayout TypeId) := do
    let .succ fuel := fuel | throw "virtual receiver wrapper cycle"
    let node ← runtime.node pointer.ty |>.mapError toString
    match node.shape with
    | .rawPointer .. | .reference .. => return pointer
    | _ =>
      let mut selected := none
      for index in [:pointer.layout.fields.count] do
        let field ← runtime.field pointer index |>.mapError toString
        unless field.layout.is1zst do
          if selected.isSome then throw "virtual receiver has multiple non-1-ZST fields"
          selected := some field
      let some field := selected | throw "virtual receiver has no pointer field"
      descend fuel field

def isX87F80 (runtime : RuntimeMetadata) (layout : TyAndLayout TypeId) : Except String Bool :=
  peel (runtime.source.types.size + 1) layout
where
  peel (fuel : Nat) (layout : TyAndLayout TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "transparent source layout cycle in x87 ABI classification"
    let node ← runtime.node layout.ty |>.mapError toString
    let .adt data := node.shape | return false
    unless data.representation.transparent do return node.sourceLayout.isX87F80
    let mut selected := none
    for index in [:layout.layout.fields.count] do
      let field ← runtime.field layout index |>.mapError toString
      unless field.layout.is1zst do
        if selected.isSome then return node.sourceLayout.isX87F80
        selected := some field
    let some field := selected | return node.sourceLayout.isX87F80
    peel fuel field

def queries (runtime : RuntimeMetadata) (policy : SourceAbiPolicy) : SourceAbi.Queries := {
  typeCount := runtime.source.types.size
  lookup := fun ty => runtime.lookup ty |>.mapError toString
  field := fun layout index => runtime.field layout index |>.mapError toString
  variant := fun layout index => runtime.forVariant layout index |>.mapError toString
  pointeeInfo := pointeeInfo runtime policy
  passIndirectlyInNonRusticAbis := fun ty => do
    let node ← runtime.node ty |>.mapError toString
    return match node.shape with
      | .adt data => data.representation.flagsBits &&& 32 != 0
      | _ => false
  thinSelf := thinSelf runtime
  isX87F80 := isX87F80 runtime }

def ofSignature (runtime : RuntimeMetadata) (signature : FunctionSignature)
    (extra : Array TypeId := #[]) : Except String (FnAbi TypeId) := do
  let some material := runtime.source.sourceAbi | throw "missing source ABI material"
  SourceAbi.compute material.policy runtime.target (queries runtime material.policy) signature extra

def ofInstance (runtime : RuntimeMetadata) (instanceId : InstanceId)
    (extra : Array TypeId) : Except String (FnAbi TypeId) := do
  let some material := runtime.source.sourceAbi | throw "missing source ABI material"
  let some definition := material.definitions[instanceId]?.getD none
    | throw "missing concrete instance source ABI signature"
  let some node := runtime.source.instances[instanceId]? | throw "missing ABI instance"
  let item := match node.instanceKind with | .Item _ => true | _ => false
  SourceAbi.compute material.policy runtime.target (queries runtime material.policy)
    definition.signature extra (some definition) item

end Miri.Input.SourceAbiRuntime
