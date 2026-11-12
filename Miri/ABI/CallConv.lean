import Miri.ABI.Layout

/-! Source-shaped `rustc_target::callconv` argument records and ABI equality.
Equality deliberately ignores attributes that are not calling-convention bits,
as the pinned source does. This does not classify a target's calling convention. -/
namespace Miri.ABI

inductive ArgExtension where
  | None | Zext | Sext
  deriving DecidableEq, Repr
structure ArgAttributes where
  regular : UInt16
  argExt : ArgExtension
  pointeeSize : Size
  pointeeAlign : Option Align
  deriving DecidableEq, Repr
namespace ArgAttributes

def new : ArgAttributes := ⟨0,.None,Size.ZERO,none⟩
def contains (attrs : ArgAttributes) (mask : UInt16) : Bool := attrs.regular &&& mask == mask
def eqAbi (left right : ArgAttributes) : Bool :=
  left.contains 64 == right.contains 64 && left.argExt == right.argExt
end ArgAttributes

structure Uniform where
  unit : Reg
  total : Size
  isConsecutive : Bool
  deriving DecidableEq, Repr
structure CastTarget where
  «prefix» : Array Reg
  restOffset : Option Size
  rest : Uniform
  attrs : ArgAttributes
  deriving DecidableEq, Repr
namespace CastTarget

def eqAbi (left right : CastTarget) : Bool :=
  left.prefix == right.prefix && left.restOffset == right.restOffset &&
  left.rest == right.rest && left.attrs.eqAbi right.attrs
end CastTarget

inductive IndirectMode where
  | Pointer | OnStack | AmdgpuKernelArg
  deriving DecidableEq, Repr
inductive PassMode where
  | Ignore
  | Direct (attrs : ArgAttributes)
  | Pair (first second : ArgAttributes)
  | Cast (padI32Count : UInt8) (cast : CastTarget)
  | Indirect (attrs : ArgAttributes) (addressSpace : Option AddressSpace) (mode : IndirectMode)
  | IndirectUnsized (attrs metaAttrs : ArgAttributes)
  deriving DecidableEq, Repr
namespace PassMode

def eqAbi : PassMode → PassMode → Bool
  | .Ignore,.Ignore => true
  | .Direct a,.Direct b => a.eqAbi b
  | .Pair a b,.Pair c d => a.eqAbi c && b.eqAbi d
  | .Cast pad a,.Cast pad' b => a.eqAbi b && pad == pad'
  | .Indirect a space mode,.Indirect b space' mode' => a.eqAbi b && space == space' && mode == mode'
  | .IndirectUnsized a metadata,.IndirectUnsized b metadata' => a.eqAbi b && metadata.eqAbi metadata'
  | _,_ => false

def isIgnore : PassMode → Bool | .Ignore => true | _ => false
def isDirect : PassMode → Bool | .Direct _ => true | _ => false
def isUnsizedIndirect : PassMode → Bool | .IndirectUnsized .. => true | _ => false
end PassMode

structure ArgAbi (Ty : Type) where
  layout : TyAndLayout Ty
  mode : PassMode
  deriving DecidableEq, Repr
namespace ArgAbi

/-- Pinned `rustc_target::callconv::ArgAbi::new` and `indirect_pass_mode`
(mod.rs:409–446). Scalar attributes are an explicit caller-supplied dependency;
this constructor does not implement target ABI adjustment or infer attributes. -/
def new (layout : TyAndLayout Ty)
    (scalarAttrs : Scalar → Size → ArgAttributes) : ArgAbi Ty :=
  let data := layout.layout
  let indirectAttrs : ArgAttributes :=
    { ArgAttributes.new with
      -- CapturesAddress | NoAlias | NonNull | NoUndef | NoFree.
      regular := 670
      pointeeSize := data.size
      pointeeAlign := some data.align.abi }
  let mode := if data.isZst then PassMode.Ignore else
    match data.backendRepr with
    | .Scalar scalar => .Direct (scalarAttrs scalar Size.ZERO)
    | .ScalarPair (a := a) (b := b) (bOffset := offset) =>
      .Pair (scalarAttrs a Size.ZERO) (scalarAttrs b offset)
    | .SimdVector .. | .SimdScalableVector .. => .Direct ArgAttributes.new
    | .Memory (sized := sized) =>
      if sized then .Indirect indirectAttrs none .Pointer
      else .IndirectUnsized indirectAttrs ArgAttributes.new
  ⟨layout, mode⟩

/-- Pinned `ArgAbi::extend_integer_width_to` (mod.rs:544–559).
Boolean scalars extend even when their primitive representation is already wide
 enough; pointer and float primitives do not carry integer extensions. -/
def extendIntegerWidthTo (arg : ArgAbi Ty) (bits : UInt64) : ArgAbi Ty :=
  match arg.layout.layout.backendRepr, arg.mode with
  | .Scalar scalar, .Direct attrs =>
    match scalar.primitive with
    | .Int integer signed =>
      if integer.size.bytes * 8 < bits || scalar.isBool then
        { arg with mode := .Direct { attrs with argExt := if signed then .Sext else .Zext } }
      else arg
    | _ => arg
  | _, _ => arg

/-- Nonpointer scalar branch of pinned rustc_ty_utils `arg_attrs_for_rust_scalar`
(abi.rs:318–334). Pointer attributes require pointee/type/instance analysis and
are deliberately outside this constructor. -/
def nonPointerScalar (layout : TyAndLayout Ty) (extensionBits : UInt64) :
    Except String (ArgAbi Ty) := do
  let .Scalar scalar := layout.layout.backendRepr
    | throw "scalar ABI recipe requires scalar physical layout"
  match scalar.primitive with
  | .Pointer _ => throw "scalar ABI recipe cannot infer pointer attributes"
  | _ => pure ()
  let result := new layout fun scalar _ =>
    { ArgAttributes.new with regular := if scalar.isUninitValid then 0 else 128 }
  pure (extendIntegerWidthTo result extensionBits)

/-- Pinned `arg_attrs_for_rust_scalar` for a top-level raw pointer or FnPtr.
`pointee_info_at` at offset zero returns safe=None, size=0, align=1 for these
two source constructors (rustc_middle/ty/layout.rs:1062). Their type identity
must be checked by the caller; references and pointer-containing ADTs cannot
use this rule merely because they share a scalar physical layout. -/
def conservativePointerScalar (layout : TyAndLayout Ty) : Except String (ArgAbi Ty) := do
  let .Scalar (.Initialized (value := .Pointer _) (validRange := range)) := layout.layout.backendRepr
    | throw "raw/FnPtr ABI requires an initialized scalar pointer layout"
  pure (new layout fun _ _ =>
    { ArgAttributes.new with regular := 128 ||| (if range.contains 0 then 0 else 16) })

/-- Initial ABI with empty scalar attributes. A transport recipe may use this
only when rustc's final adjusted argument equals this entire initial argument. -/
def initial (layout : TyAndLayout Ty) : ArgAbi Ty :=
  new layout (fun _ _ => ArgAttributes.new)

def eqAbi [DecidableEq Ty] (left right : ArgAbi Ty) : Bool :=
  left.layout.layout.eqAbi right.layout.layout && left.mode.eqAbi right.mode &&
  (if left.mode.isDirect then
    match left.layout.layout.backendRepr with
    | .Memory => left.layout.ty == right.layout.ty
    | _ => true
   else true)

def isIgnore (arg : ArgAbi Ty) : Bool := arg.mode.isIgnore
def isUnsizedIndirect (arg : ArgAbi Ty) : Bool := arg.mode.isUnsizedIndirect
end ArgAbi
end Miri.ABI
