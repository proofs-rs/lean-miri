import Miri.Input.SourceCompilerTypes
import Miri.Input.SourceTypeQueries
import Miri.Input.SourceAggregateLayout

namespace Miri.Input.SourcePhysical
open SourceTypes
private def memory : BackendRepr := ⟨.memory,some true,none,none,none,none,none,none,none⟩
private def base (size align seed : Nat) (fields : FieldShape) (offsets : Array Nat)
    (backend : BackendRepr) (niche : Option NicheLayout) : Layout := {
  maxReprAlignBytes := none, reprC := false, uninhabited := false, largestNiche := niche,
  randomizationSeed := seed, kind := .layout, sizeBytes := some size, abiAlignBytes := some align,
  unadjustedAbiAlignBytes := some align, fieldOffsetsBytes := .explicit offsets,
  fields := some fields, variantsLayout := some ⟨.single,some 0,none,none,none,#[]⟩,
  backendRepresentation := some backend, variantsKind := some .single, backendReprKind := some backend.kind,
  variants := none, backendRepr := none }
private def integerKind : String → Except String MIR.IntegerKind
  | "i8" => pure .i8 | "u8" => pure .u8 | "i16" => pure .i16 | "u16" => pure .u16
  | "i32" => pure .i32 | "u32" => pure .u32 | "i64" => pure .i64 | "u64" => pure .u64
  | "i128" => pure .i128 | "u128" => pure .u128 | "isize" => pure .isize | "usize" => pure .usize
  | _ => throw "Unsupported typed source integer"
private def width (target : ABI.RuntimeTargetDataLayout) (name : String) : Except String Nat := do
  match name with
  | "isize" | "usize" => return target.pointerOffset.bytes.toNat * 8
  | "i8" | "u8" => pure 8 | "i16" | "u16" => pure 16
  | "i32" | "u32" => pure 32 | "i64" | "u64" => pure 64 | "i128" | "u128" => pure 128
  | _ => throw "Unsupported typed source integer width"
private def integerAlign (target : ABI.RuntimeTargetDataLayout) (bits : Nat) : Except String Nat := do
  let align ← match bits with
    | 8 => pure target.i8Align | 16 => pure target.i16Align | 32 => pure target.i32Align
    | 64 => pure target.i64Align | 128 => pure target.i128Align
    | _ => throw "Unsupported typed integer alignment"
  return (← align.bytes.mapError toString).toNat
private def rotate (n : Nat) : UInt64 := UInt64.ofNat ((n % 2^64)/2^16 + (n % 2^16)*2^48)
private def scalar (size align : Nat) (primitive : PrimitiveLayout) (first last code : Nat) : Layout :=
  let value : ScalarLayout := ⟨.initialized,primitive,some (first,last)⟩
  let niche := if first == 0 && last == 2^(size*8)-1 then none else some ⟨0,primitive,(first,last)⟩
  let seed := (UInt64.ofNat size + UInt64.ofNat (code*2^32) + rotate first + rotate last).toNat
  base size align seed ⟨.primitive,0,none,none,#[],#[]⟩ #[]
    ⟨.scalar,none,some value,none,none,none,none,none,none⟩ niche
private def pointerInfo : String → Except String (MIR.Mutability × Option MIR.Region)
  | "raw_pointer_const" => pure (.Not,none) | "raw_pointer_mut" => pure (.Mut,none)
  | "reference_static_const" => pure (.Not,some .Static) | "reference_static_mut" => pure (.Mut,some .Static)
  | "reference_erased_const" => pure (.Not,some .Erased) | "reference_erased_mut" => pure (.Mut,some .Erased)
  | _ => throw "Unsupported typed source pointer kind"
private def sizeAlign (row : Layout) : Except String (Nat × Nat) := do
  let some size := row.sizeBytes | throw "Invalid derived size"
  let some align := row.abiAlignBytes | throw "Invalid derived alignment"
  return (size,align)

/-- Typed finite source target; no host or triple-derived defaults. -/
def target (world : SourceCompilerWorld.World) : Except String ABI.RuntimeTargetDataLayout := do
  let some source := world.canonical.sourceMaterial | throw "Unsupported typed compiler source unavailable"
  -- World.create validates the retained finite source once. Each demand checks
  -- only the target evidence it consumes, rather than rewalking all source rows.
  let some evidence := source.target.runtimeDataLayout | throw "Unsupported complete source target unavailable"
  for space in evidence.addressSpaceInfo do
    let bound ← match space.spec.pointerSizeBytes with
      | 2 => pure (2^15) | 4 => pure (2^31) | 8 => pure (2^61)
      | _ => throw "Unsupported source address-space pointer width"
    unless space.objectSizeBoundBytes == some bound do throw "Invalid source address-space object bound"
  (RuntimeMetadata.importTarget evidence).mapError toString

private def addSeed (a b : Nat) : Nat := (UInt64.ofNat a + UInt64.ofNat b).toNat
private def fieldsAt (offsets : Array Nat) : FieldShape :=
  ⟨.arbitrary,offsets.size,none,none,offsets,(List.range offsets.size).toArray⟩
private def mem : BackendRepr := memory
private def checkRepr (repr : ReprOptions) (allowed : Array Nat) : Except String Unit := do
  unless allowed.contains repr.flagsBits && repr.alignBytes.isNone && repr.packBytes.isNone &&
      repr.integer.isNone && repr.scalableElement.isNone do throw "Unsupported typed source repr options"
/-- Pinned rustc_abi::layout_of_union. ABI forwarding discards field validity
ranges; repr(C) inhibits it. Unsupported vector fields remain explicit. -/
private def unionLayout (target : ABI.RuntimeTargetDataLayout) (repr : ReprOptions)
    (fields : Array Layout) : Except String Layout := do
  unless #[0,1,8,9].contains repr.flagsBits && repr.integer.isNone && repr.scalableElement.isNone do
    throw "Unsupported union representation flags"
  unless !fields.isEmpty do throw "Invalid empty union"
  for alignment in #[repr.alignBytes,repr.packBytes] do
    if let some bytes := alignment then
      unless bytes > 0 && bytes < 2^64 do throw "Invalid union representation alignment width"
      let _ ← (ABI.Align.fromBytes (UInt64.ofNat bytes)).mapError toString
  if repr.alignBytes.isSome && repr.packBytes.isSome then
    throw "Unsupported union combined packed/aligned representation"
  let packed := repr.packBytes
  let align ← (if packed.isSome then target.i8Align else target.aggregateAlign).bytes.mapError toString
  let mut alignment := align.toNat
  let mut maxRepr := repr.alignBytes
  let mut size := 0
  let mut seed := repr.fieldShuffleSeed
  let mut common : Option BackendRepr := none
  let mut mismatch := repr.flagsBits % 2 == 1
  for field in fields do
    let (fieldSize,fieldAlign) ← sizeAlign field
    let some backend := field.backendRepresentation | throw "Invalid union field backend"
    if backend.kind == .memory && backend.sized != some true then
      throw "Unsupported unsized union field"
    alignment := max alignment fieldAlign
    maxRepr := match maxRepr,field.maxReprAlignBytes with
      | none,b => b | a,none => a | some a,some b => some (max a b)
    size := max size fieldSize
    seed := addSeed seed field.randomizationSeed
    if fieldSize == 0 then continue
    if !mismatch then
      let toUnion := fun (scalar : ScalarLayout) => {scalar with kind := .union, validRange := none}
      let backend ← match backend.kind with
        | .memory => pure backend
        | .scalar =>
          let some scalar := backend.scalar | throw "Invalid union scalar"
          pure {backend with scalar := some (toUnion scalar)}
        | .scalarPair =>
          let some first := backend.first | throw "Invalid union first scalar"
          let some second := backend.second | throw "Invalid union second scalar"
          pure {backend with first := some (toUnion first), second := some (toUnion second)}
        | _ => throw "Unsupported union vector ABI"
      if let some previous := common then
        let previousABI ← (RuntimeMetadata.backend target previous).mapError toString
        let nextABI ← (RuntimeMetadata.backend target backend).mapError toString
        if previousABI != nextABI then mismatch := true
      else common := some backend
  if let some pack := packed then alignment := min alignment pack
  let unadjusted := alignment
  if let some requested := repr.alignBytes then alignment := max alignment requested
  let mut backend := memory
  if !mismatch then
    if let some candidate := common then
      let runtime ← (RuntimeMetadata.backend target candidate).mapError toString
      let scalarAlign ← (runtime.scalarPlatformAlign target).mapError reprStr
      if let some scalarAlign := scalarAlign then
        if (← scalarAlign.bytes.mapError toString).toNat == alignment then backend := candidate
      else backend := candidate
  let rounded := (size+alignment-1)/alignment*alignment
  unless rounded < target.base.objSizeBound.toNat do throw "Union exceeds target object size bound"
  let row := base rounded alignment seed ⟨.union,fields.size,some 0,none,#[],#[]⟩
    (Array.replicate fields.size 0) backend none
  return {row with
    maxReprAlignBytes := maxRepr
    reprC := repr.flagsBits % 2 == 1
    unadjustedAbiAlignBytes := some unadjusted}

private def dynMetadata (source : Material) : Except String Unit := do
  let some (.declarations m) := source.dynMetadata | throw "Unsupported dyn metadata declaration source unavailable"
  let role := fun id kind => do
    let some d := source.definitions[id]? | throw "Invalid dyn metadata source definition"
    unless d.kind == kind do throw "Invalid dyn metadata source definition category"
  role m.metadataType "AssocTy"; role m.pointeeTrait "Trait"
  unless m.metadataParent == m.pointeeTrait && m.pointeeParameterCount == 1 && m.metadataParameterCount == 1 do
    throw "Unsupported Pointee metadata declaration shape"
  role m.dynamic.definition "Struct"; checkRepr m.dynamic.representation #[0]
  unless m.dynamic.fieldCount == 2 && m.dynamic.argumentCount == 1 && m.vtableField == 0 && m.phantomField == 1 do
    throw "Unsupported DynMetadata source fields"
  role m.nonnull.definition "Struct"; checkRepr m.nonnull.representation #[4]
  unless m.nonnull.fieldCount == 1 && m.nonnull.argumentCount == 1 && m.nonnullLangItem == "non_null" do
    throw "Unsupported NonNull source fields"
  let .notNullRawForeign false pointee := m.pointer | throw "Unsupported NonNull metadata pointer source"
  role pointee "ForeignTy"
  role m.phantom.definition "Struct"; checkRepr m.phantom.representation #[0]
  unless m.phantom.fieldCount == 0 && m.phantom.argumentCount == 1 && m.phantomLangItem == "phantom_data" &&
      m.phantomParameterIndex == 0 do throw "Unsupported PhantomData source fields"

private def nonnullPair (l : Input.Layout) : Except String Input.Layout := do
  let some b := l.backendRepresentation | throw "pointer backend absent"
  let some a := b.first | throw "nonnull subset requires scalar pair"
  let some z := b.second | throw "pointer metadata absent"
  let w := a.primitive.sizeBytes
  unless b.kind == .scalarPair && a.primitive.kind == .pointer &&
      a.primitive.addressSpace == some 0 && a.validRange == some (0, 2^(w*8)-1) &&
      z.primitive.kind == .pointer && z.validRange == some (1, 2^(w*8)-1) &&
      l.sizeBytes == some (2*w) && b.secondOffsetBytes == some w do
    throw "unsupported nonnull source pattern layout"
  let a := { a with validRange := some (1, 2^(w*8)-1) }
  return { l with
    fields := some (fieldsAt #[0]), fieldOffsetsBytes := (.explicit #[0]),
    backendRepresentation := some { b with first := some a },
    largestNiche := some ⟨0, a.primitive, (1, 2^(w*8)-1)⟩ }

/-- Range patterns clone the scalar layout, replacing validity and niche only.
The pinned rule retains base seed/size and exposes the base as field zero. -/
private def rangeLayout (layout : Layout) (lower upper : Nat) : Except String Layout := do
  let some backend := layout.backendRepresentation | throw "pattern range backend absent"
  let some scalar := backend.scalar | throw "Unsupported non-scalar pattern range"
  unless backend.kind == .scalar && scalar.kind == .initialized && scalar.primitive.kind == .integer do
    throw "Unsupported pattern range scalar representation"
  let bits := scalar.primitive.sizeBytes*8
  unless bits > 0 && lower < 2^bits && upper < 2^bits do throw "Invalid pattern range bound width"
  let signed := fun value => if value < 2^(bits-1) then (Int.ofNat value) else (Int.ofNat value - Int.ofNat (2^bits))
  unless (if scalar.primitive.signed == some true then signed lower ≤ signed upper else lower ≤ upper) do
    throw "Invalid wrapping pattern range"
  return {layout with
    fields := some (fieldsAt #[0])
    fieldOffsetsBytes := .explicit #[0]
    backendRepresentation := some {backend with scalar := some {scalar with validRange := some (lower,upper)}}
    largestNiche := some ⟨0,scalar.primitive,(lower,upper)⟩}

private def wrapperLayout (empty : Input.Layout) (seed : Nat)
    (fs : Array Input.Layout) : Except String Input.Layout := do
  let combined := fs.foldl (fun s f => addSeed s f.randomizationSeed) seed
  if fs.isEmpty then return { empty with randomizationSeed := combined }
  let some first := fs[0]? | throw "missing wrapper field"
  let some backend := first.backendRepresentation | throw "missing wrapper backend"
  let some size := first.sizeBytes | throw "missing wrapper size"
  unless (backend.kind == .scalar || backend.kind == .scalarPair) && size > 0 do throw "unsupported nominal non-ZST field"
  for f in fs.extract 1 fs.size do
    unless f.sizeBytes == some 0 && f.abiAlignBytes == some 1 && !f.uninhabited do
      throw "unsupported nominal trailing field"
  let offsets := #[0] ++ Array.replicate (fs.size-1) size
  return { first with
    fields := some (fieldsAt offsets), fieldOffsetsBytes := (.explicit offsets),
    randomizationSeed := combined }

private def nicheResult (seed : Nat) (ok err : Input.Layout) : Except String Input.Layout := do
  let some b := err.backendRepresentation | throw "missing error backend"
  let some a := b.first | throw "missing error data scalar"
  let some z := b.second | throw "missing error metadata scalar"
  let w := a.primitive.sizeBytes
  let some ob := ok.backendRepresentation | throw "missing success backend"
  let some os := ob.scalar | throw "unsupported success payload"
  unless w > 0 && w ≤ 16 && err.sizeBytes == some (2*w) && err.abiAlignBytes == some w &&
      err.unadjustedAbiAlignBytes == some w && b.kind == .scalarPair &&
      b.secondOffsetBytes == some w && a.primitive.kind == .pointer &&
      a.primitive.addressSpace == some 0 && z.primitive.kind == .pointer &&
      z.primitive.addressSpace == some 0 && z.primitive.sizeBytes == w &&
      a.validRange == some (1, 2^(w*8)-1) && z.validRange == some (1, 2^(w*8)-1) &&
      ok.sizeBytes == some w && ok.abiAlignBytes == some w &&
      ob.kind == .scalar && os.primitive.kind == .integer && os.primitive.signed == some true &&
      os.validRange == some (0, 2^(w*8)-1) && !ok.uninhabited && !err.uninhabited do
    throw "unsupported two-variant niche layout"
  let tag := { a with validRange := some (0, 2^(w*8)-1) }
  let variants : Array Input.LayoutVariant := #[
    ⟨fieldsAt #[w], none, 0, 2*w, mem, #[w], false⟩,
    ⟨fieldsAt #[0], err.largestNiche, 1, 2*w, b, #[0], false⟩]
  let combined := addSeed seed (addSeed (addSeed seed ok.randomizationSeed)
    (addSeed seed err.randomizationSeed))
  return { err with
    fields := some (fieldsAt #[0]), fieldOffsetsBytes := (.explicit #[0]),
    variantsLayout := some ⟨.multiple, none, some tag,
      some ⟨.niche, some 1, some (0,0), some 0⟩, some 0, variants⟩,
    variantsKind := some .multiple, backendRepresentation := some mem,
    backendReprKind := some .memory, largestNiche := none, randomizationSeed := combined }

/-- The pinned direct-tag rule for two variants with one equal-width, fully
valid integer scalar each. The tag grows to the payload alignment and the
common payload occupies the second scalar of the pair. -/
private def directScalarEnum (seed : Nat) (first second : Layout) : Except String Layout := do
  let some a := first.backendRepresentation.bind (·.scalar) | throw "Unsupported direct enum first payload"
  let some b := second.backendRepresentation.bind (·.scalar) | throw "Unsupported direct enum second payload"
  let w := a.primitive.sizeBytes
  unless first.backendReprKind == some .scalar && second.backendReprKind == some .scalar &&
      a.kind == .initialized && b.kind == .initialized &&
      a.primitive.kind == .integer && b.primitive.kind == .integer &&
      a.primitive.integerKind == b.primitive.integerKind && w > 0 && w ≤ 16 &&
      first.sizeBytes == some w && second.sizeBytes == some w &&
      first.abiAlignBytes == some w && second.abiAlignBytes == some w &&
      first.unadjustedAbiAlignBytes == some w && second.unadjustedAbiAlignBytes == some w &&
      a.validRange == some (0, 2^(w*8)-1) && b.validRange == some (0, 2^(w*8)-1) &&
      !first.uninhabited && !second.uninhabited do
    throw "Unsupported direct enum scalar payloads"
  let tagPrimitive := {a.primitive with signed := some false}
  let tag : ScalarLayout := ⟨.initialized,tagPrimitive,some (0,1)⟩
  let pair : BackendRepr := ⟨.scalarPair,none,none,some tag,some a,some w,none,none,none⟩
  let variant : Nat → Input.LayoutVariant := fun i =>
    ⟨fieldsAt #[w],none,i,2*w,pair,#[w],false⟩
  let combined := addSeed seed (addSeed (addSeed seed first.randomizationSeed)
    (addSeed seed second.randomizationSeed))
  let row := base (2*w) w combined (fieldsAt #[0]) #[0] pair
    (some ⟨0,tagPrimitive,(0,1)⟩)
  let variants : VariantsLayout := ⟨.multiple,none,some tag,
    some ⟨.direct,none,none,none⟩,some 0,#[variant 0,variant 1]⟩
  return {row with variantsLayout := some variants, variantsKind := some .multiple}


/-- Pinned FnPtr layout depends only on the instruction pointer specification,
not on invented argument types or erased binder identities. -/
def functionPointerLayout (target : ABI.RuntimeTargetDataLayout) : Except String Layout := do
  let spec ← target.pointerSpecIn target.instructionAddressSpace |>.mapError toString
  let size := spec.pointerSize.bytes.toNat
  let align := (← spec.pointerAlign.bytes.mapError toString).toNat
  scalar size align ⟨.pointer,size,none,none,none,some target.instructionAddressSpace.value.toNat⟩ 1 (2^(size*8)-1) 4 |> pure

def calculate (source : Material) (target : ABI.RuntimeTargetDataLayout) (ty : Concrete) : Except String Layout :=
  go 1024 ty
where
  go (fuel : Nat) (ty : Concrete) : Except String Layout := do
    let .succ fuel := fuel | throw "Unsupported typed physical recursion exhausted"
    match ty with
    | .primitive "str" "" =>
      let row := base 0 (← integerAlign target 8) 0xc1325f37d127be22
        ⟨.array,0,none,some 1,#[],#[]⟩ #[] {memory with sized := some false} none
      return {row with fieldOffsetsBytes := .arrayFormula 1 0}
    | .primitive "never" "" =>
      let align := (← target.i8Align.bytes.mapError toString).toNat
      let row := base 0 align 0 ⟨.primitive,0,none,none,#[],#[]⟩ #[] memory none
      let row := {row with uninhabited := true}
      let row := {row with variantsLayout := some ⟨.empty,none,none,none,none,#[]⟩}
      return {row with variantsKind := some .empty}
    | .primitive kind name =>
      let bits ← if kind == "bool" && name == "" then pure 8 else if kind == "char" && name == "" then pure 32
        else if kind == "int" || kind == "uint" then width target name else throw "Unsupported typed primitive layout"
      let signed := kind == "int"
      let last := if kind == "bool" then 1 else if kind == "char" then 0x10ffff else 2^bits-1
      let tag ← integerKind s!"{if signed then "i" else "u"}{bits}"
      let primitive : PrimitiveLayout := ⟨.integer,bits/8,some (.known tag),some signed,none,none⟩
      return scalar (bits/8) (← integerAlign target bits) primitive 0 last (if signed then 1 else 2)
    | .array element count =>
      unless count < 2^(target.pointerOffset.bytes.toNat*8) do throw "Invalid typed array length exceeds usize"
      let child ← go fuel element
      if child.backendRepresentation.bind (·.sized) == some false then throw "Unsupported unsized array element"
      let (stride,align) ← sizeAlign child
      let size := stride*count
      unless size < target.base.objSizeBound.toNat do throw "Invalid typed array object bound"
      let row := base size align (UInt64.ofNat child.randomizationSeed + UInt64.ofNat count).toNat
        ⟨.array,count,none,some stride,#[],#[]⟩ #[] memory (if count == 0 then none else child.largestNiche)
      return {row with fieldOffsetsBytes := .arrayFormula stride count}
    | .tuple fields => aggregate fuel fields true
    | .closure definition args =>
      let some defn := source.definitions[definition]? | throw "Invalid closure definition reference"
      unless defn.kind == "closure" && args.size ≥ 3 do throw "Invalid closure source definition/arguments"
      let some (.primitive "int" kind) := args[args.size-3]? | throw "Unsupported closure kind source"
      unless #["i8","i16","i32"].contains kind do throw "Invalid closure kind encoding"
      let some (.functionPointer _ _ _ .RustCall false) := args[args.size-2]? | throw "Unsupported closure RustCall signature"
      let some (.tuple fields) := args.back? | throw "Unsupported closure upvar source"
      aggregate fuel fields false
    | .functionPointer .. =>
      functionPointerLayout target
    | .pointer kind pointee =>
      let (_,region) ← pointerInfo kind
      let child ← go fuel pointee
      let spec ← target.pointerSpecIn ABI.AddressSpace.ZERO |>.mapError toString
      let size := spec.pointerSize.bytes.toNat
      let align := (← spec.pointerAlign.bytes.mapError toString).toNat
      let primitive : PrimitiveLayout := ⟨.pointer,size,none,none,none,some 0⟩
      let first := if region.isSome then 1 else 0
      let last := 2^(size*8)-1
      let data : ScalarLayout := ⟨.initialized,primitive,some (first,last)⟩
      if let .dynamicObject _ := pointee then
        dynMetadata source
        unless size == align && (← target.aggregateAlign.bytes.mapError toString).toNat == 1 do
          throw "Unsupported dyn metadata target alignment"
        let metadata : ScalarLayout := ⟨.initialized,primitive,some (1,last)⟩
        return base (2*size) align (2*size) (fieldsAt #[0,size]) #[0,size]
          ⟨.scalarPair,none,none,some data,some metadata,some size,none,none,none⟩
          (some ⟨if first == 1 then 0 else size,primitive,(1,last)⟩)
      if let .primitive "str" "" := pointee then
        let metadataSize := target.pointerOffset.bytes.toNat
        let metadataRow ← go fuel (.primitive "uint" s!"u{metadataSize*8}")
        let some metadata := metadataRow.backendRepresentation.bind (·.scalar) | throw "Invalid str metadata scalar"
        let (_,metadataAlign) ← sizeAlign metadataRow
        let offset := (size+metadataAlign-1)/metadataAlign*metadataAlign
        let totalAlign := max (max align metadataAlign) (← target.aggregateAlign.bytes.mapError toString).toNat
        let totalSize := (offset+metadataSize+totalAlign-1)/totalAlign*totalAlign
        return base totalSize totalAlign (size+metadataSize) (fieldsAt #[0,offset]) #[0,offset]
          ⟨.scalarPair,none,none,some data,some metadata,some offset,none,none,none⟩
          (if first == 0 then none else some ⟨0,primitive,(first,last)⟩)
      if child.backendRepresentation.bind (·.sized) == some false then throw "Unsupported typed wide pointer metadata source"
      return scalar size align primitive first last 4
    | .nominal definition args =>
      let some declaration := source.definitions[definition]? | throw "Invalid nominal source definition"
      let some adt := declaration.adt | throw "Unsupported nominal declaration material unavailable"
      unless args.size == adt.parameters.size && adt.parameters.all (· == .typeParameter) do
        throw "Unsupported nominal non-type/incomplete arguments"
      let mut variants := #[]
      for variant in adt.variants do
        let fields ← variant.fields.mapM fun f => do
          SourceTypes.instantiate source (args.map some) #[] f.typeRef
        variants := variants.push fields
      match adt.kind with
      | .structKind =>
        checkRepr adt.representation #[0,4,8]
        let some fields := variants[0]? | throw "Invalid struct source fields"
        unless variants.size == 1 do throw "Invalid struct source variants"
        let empty ← aggregate fuel #[] false
        let rows ← fields.mapM (go fuel)
        if let some first := rows[0]? then
          unless (empty.abiAlignBytes.getD 0) ≤ first.abiAlignBytes.getD 0 do
            throw "Unsupported nominal aggregate alignment"
        wrapperLayout empty adt.representation.fieldShuffleSeed rows
      | .enumKind =>
        checkRepr adt.representation #[0]
        unless variants.size == 2 do throw "Unsupported enum variant count"
        let mut rows := #[]
        for i in [0:2] do
          let some variant := adt.variants[i]? | throw "Invalid enum source variant"
          unless variant.index == i && variant.discriminant == .relative i do throw "Unsupported enum source discriminants"
          let some fields := variants[i]? | throw "Invalid enum source fields"
          let some field := fields[0]? | throw "Invalid enum source field"
          unless fields.size == 1 do throw "Unsupported enum field count"
          rows := rows.push (← go fuel field)
        let some a := rows[0]? | throw "Invalid enum success field"
        let some b := rows[1]? | throw "Invalid enum error field"
        match directScalarEnum adt.representation.fieldShuffleSeed a b with
        | .ok row => pure row
        | .error _ => nicheResult adt.representation.fieldShuffleSeed a b
      | .unionKind =>
        let some fields := variants[0]? | throw "Invalid union source fields"
        unless variants.size == 1 do throw "Invalid union source variants"
        unionLayout target adt.representation (← fields.mapM (go fuel))
    | .dynamicObject _ =>
      return base 0 (← integerAlign target 8) 0 (fieldsAt #[]) #[] {memory with sized := some false} none
    | .patternNotNull base => nonnullPair (← go fuel base)
    | .patternRange base lower upper => rangeLayout (← go fuel base) lower upper
  aggregate (fuel : Nat) (fields : Array Concrete) (tupleTail : Bool) : Except String Layout := do
    let align := (← target.aggregateAlign.bytes.mapError toString).toNat
    if fields.isEmpty then return base 0 align 0 ⟨.arbitrary,0,none,none,#[],#[]⟩ #[] memory none
    let rows ← fields.mapM (go fuel)
    if rows.size > 1 then SourceLayouts.scalarAggregateLayout target rows tupleTail
    else
      let some child := rows[0]? | throw "Invalid singleton aggregate"
      let (size,childAlign) ← sizeAlign child
      unless align ≤ childAlign && size > 0 do throw "Unsupported singleton aggregate alignment/zero-size"
      let some backend := child.backendRepresentation | throw "Invalid singleton backend"
      unless backend.kind == .scalar || backend.kind == .scalarPair do throw "Unsupported singleton aggregate backend"
      return {child with
        fields := some ⟨.arbitrary,1,none,none,#[0],#[0]⟩
        fieldOffsetsBytes := .explicit #[0]
        variantsLayout := some ⟨.single,some 0,none,none,none,#[]⟩
        variantsKind := some .single
        randomizationSeed := if tupleTail then 0 else child.randomizationSeed }

/-- Demand a physical type in the single canonical World. No private registry,
JSON document or runtime compiler callback is used. -/
def intern (world : SourceCompilerWorld.World) (ty : Concrete) : Except String (SourceCompilerWorld.World × Nat) := do
  let some material := world.canonical.sourceMaterial | throw "Unsupported typed compiler source unavailable"
  let some source := material.physical | throw "Unsupported typed physical source unavailable"
  let target ← target world
  go source target 1024 world ty
where
  go (source : Material) (target : ABI.RuntimeTargetDataLayout) (fuel : Nat)
      (world : SourceCompilerWorld.World) (ty : Concrete) : Except String (SourceCompilerWorld.World × Nat) := do
    let .succ fuel := fuel | throw "Unsupported typed physical interning recursion exhausted"
    let row ← calculate source target ty
    let (world,shape,display) ← match ty with
      | .primitive "bool" "" => pure (world,TypeShape.bool,"bool")
      | .primitive "char" "" => pure (world,TypeShape.char,"char")
      | .primitive "str" "" => pure (world,TypeShape.str,"str")
      | .primitive "never" "" => pure (world,TypeShape.never,"!")
      | .primitive kind name =>
        let tag ← integerKind name
        if kind == "int" then pure (world,.int (.known tag),name)
        else if kind == "uint" then pure (world,.uint (.known tag),name)
        else throw "Unsupported typed primitive identity"
      | .array element count => do
        let (world,element) ← go source target fuel world element
        let (world,usize) ← go source target fuel world (.primitive "uint" "usize")
        let (world,length) ← SourceCompilerWorld.internScalarConstant world usize count target.pointerOffset.bytes.toNat
        pure (world,.array element length ⟨count,true⟩,"source array")
      | .tuple fields => do
        let mut next := world
        let mut ids := #[]
        for t in fields do
          let (updated,id) ← go source target fuel next t
          next := updated
          ids := ids.push id
        pure (next,.tuple ids,"source tuple")
      | .pointer kind pointee => do
        let (world,pointee) ← go source target fuel world pointee
        let (mutable,region) ← pointerInfo kind
        let shape := match region with | none => TypeShape.rawPointer pointee mutable | some region => .reference pointee mutable region
        pure (world,shape,"source pointer")
      | .functionPointer inputs output safety abi variadic => do
        let mut next := world
        let mut ids := #[]
        for t in inputs do
          let (updated,id) ← go source target fuel next t
          next := updated
          ids := ids.push id
        let (finished,output) ← go source target fuel next output
        pure (finished,.functionPointer ⟨ids,output,safety,abi,variadic⟩ #[],"source function pointer")
      | .closure definition arguments => do
        let some declared := source.definitions[definition]? | throw "Invalid closure source declaration"
        let some (.tuple fields) := arguments.back? | throw "Invalid closure source upvars"
        let mut next := world
        let mut ids := #[]
        for t in arguments do
          let (updated,id) ← go source target fuel next t
          next := updated
          ids := ids.push id
        let (finished,definition) ← SourceCompilerWorld.internDefinition next declared.raw
        pure (finished,.closure definition (ids.map MIR.GenericArg.Type) fields.size,declared.path)
      | .patternNotNull base => do
        let (next,id) ← go source target fuel world base
        pure (next,.patternType id .notNull,"source nonnull pattern")
      | .patternRange base lower upper => do
        let (next,id) ← go source target fuel world base
        let some bytes := row.sizeBytes | throw "pattern range scalar size absent"
        let (next,lower) ← SourceCompilerWorld.internScalarConstant next id lower bytes
        let (next,upper) ← SourceCompilerWorld.internScalarConstant next id upper bytes
        pure (next,.patternType id (.range lower upper),"source range pattern")
      | .nominal definition args => do
        let some declared := source.definitions[definition]? | throw "Invalid nominal source declaration"
        let some adt := declared.adt | throw "Unsupported nominal source fields unavailable"
        let mut next := world
        let mut ids := #[]
        for t in args do
          let (updated,id) ← go source target fuel next t
          next := updated
          ids := ids.push id
        let mut variants := #[]
        for variant in adt.variants do
          let mut fields := #[]
          for field in variant.fields do
            let ty ← SourceTypes.instantiate source (args.map some) #[] field.typeRef
            let (updated,id) ← go source target fuel next ty
            next := updated
            fields := fields.push ⟨field.index,field.name,id⟩
          variants := variants.push ⟨variant.index,variant.name,fields⟩
        let (finished,definition) ← SourceCompilerWorld.internDefinition next declared.raw
        pure (finished,.adt ⟨definition,adt.kind,adt.representation,ids.map MIR.GenericArg.Type,variants⟩,declared.path)
      | .dynamicObject object => do
        let mut next := world
        let mut ids := #[]
        let mut principal := none
        if let some definition := object.principal then
          let some declared := source.definitions[definition]? | throw "Invalid dynamic principal declaration"
          unless declared.kind == "Trait" && declared.traitIsAuto == some false do throw "Invalid dynamic principal category"
          let mut args := #[]
          for ty in object.arguments do
            let (updated,id) ← go source target fuel next ty
            next := updated
            args := args.push (.Type id)
          let (updated,definition) ← SourceCompilerWorld.internDefinition next declared.raw
          let predicate : VtablePredicate := ⟨.trait,definition,some declared.path,args,#[],none⟩
          let (updated,id) ← SourceCompilerWorld.internPredicate updated predicate
          next := updated
          ids := ids.push id
          principal := some id
        else
          unless object.arguments.isEmpty && object.projections.isEmpty do throw "Invalid dynamic arguments without principal"
        for projection in object.projections do
          let some parent := source.definitions[projection.parentTrait]? | throw "Invalid dynamic projection parent"
          unless object.principal.isSome && parent.kind == "Trait" do throw "Invalid dynamic projection parent category"
          let some declared := source.definitions[projection.definition]? | throw "Invalid dynamic projection declaration"
          unless declared.kind == "AssocTy" do throw "Invalid dynamic projection category"
          let mut args := #[]
          for ty in projection.arguments do
            let (updated,id) ← go source target fuel next ty
            next := updated
            args := args.push (.Type id)
          let (updated,term) ← go source target fuel next projection.term
          let (updated,definition) ← SourceCompilerWorld.internDefinition updated declared.raw
          let predicate : VtablePredicate := ⟨.projection,definition,some declared.path,args,#[],some term⟩
          let (updated,id) ← SourceCompilerWorld.internPredicate updated predicate
          next := updated
          ids := ids.push id
        for definition in object.autoTraits do
          let some declared := source.definitions[definition]? | throw "Invalid dynamic auto-trait declaration"
          unless declared.kind == "Trait" && declared.traitIsAuto == some true do throw "Invalid dynamic auto-trait category"
          let (updated,definition) ← SourceCompilerWorld.internDefinition next declared.raw
          let predicate : VtablePredicate := ⟨.autoTrait,definition,some declared.path,#[],#[],none⟩
          let (updated,id) ← SourceCompilerWorld.internPredicate updated predicate
          next := updated
          ids := ids.push id
        pure (next,.dynamicTraitObject ids principal object.region,"source dynamic object")
    SourceCompilerWorld.internType world shape row display
end Miri.Input.SourcePhysical
