//! Semantic layout and calling-convention data retained until document output.
use rustc_index::Idx;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

#[derive(Serialize)]
pub(super) struct Layout {
    pub size_bytes: u64,
    pub abi_align_bytes: u64,
    pub unadjusted_abi_align_bytes: u64,
    pub max_repr_align_bytes: Option<u64>,
    pub repr_c: bool,
    pub uninhabited: bool,
    pub fields: Fields,
    pub field_offsets_bytes: Vec<u64>,
    pub variants: Variants,
    pub backend_repr: BackendRepr,
    pub largest_niche: Option<Niche>,
    pub randomization_seed: u64,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Fields {
    Primitive {
        field_count: u64,
    },
    Union {
        field_count: u64,
        offset_bytes: u64,
    },
    Array {
        stride_bytes: u64,
        field_count: u64,
    },
    Arbitrary {
        field_count: u64,
        offsets_bytes: Vec<u64>,
        memory_order: Vec<usize>,
    },
}
impl Fields {
    pub fn from_rustc<I: Idx>(fields: &rustc_abi::FieldsShape<I>) -> Self {
        use rustc_abi::FieldsShape as F;
        match fields {
            F::Primitive => Self::Primitive { field_count: 0 },
            F::Union(n) => Self::Union {
                field_count: n.get() as u64,
                offset_bytes: 0,
            },
            F::Array { stride, count } => Self::Array {
                stride_bytes: stride.bytes(),
                field_count: *count,
            },
            F::Arbitrary {
                offsets,
                in_memory_order,
            } => Self::Arbitrary {
                field_count: offsets.len() as u64,
                offsets_bytes: offsets.iter().map(|x| x.bytes()).collect(),
                memory_order: in_memory_order.iter().map(|x| x.index()).collect(),
            },
        }
    }
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Primitive {
    Integer {
        integer_kind: &'static str,
        signed: bool,
        size_bytes: u64,
    },
    Float {
        float_kind: &'static str,
        size_bytes: u64,
    },
    Pointer {
        address_space: u32,
        #[serde(skip_serializing_if = "Option::is_none")]
        size_bytes: Option<u64>,
    },
}
impl Primitive {
    fn new(value: rustc_abi::Primitive, tcx: Option<TyCtxt<'_>>) -> Self {
        use rustc_abi::Primitive as P;
        match value {
            P::Int(i, signed) => Self::Integer {
                integer_kind: i.int_ty_str(),
                signed,
                size_bytes: i.size().bytes(),
            },
            P::Float(f) => Self::Float {
                float_kind: f.ty_str(),
                size_bytes: f.size().bytes(),
            },
            P::Pointer(a) => Self::Pointer {
                address_space: a.0,
                size_bytes: tcx.map(|tcx| value.size(&tcx).bytes()),
            },
        }
    }
}
#[derive(Serialize)]
pub(super) struct ValidRange {
    start: String,
    end: String,
}
impl ValidRange {
    fn new(range: rustc_abi::WrappingRange) -> Self {
        Self {
            start: range.start.to_string(),
            end: range.end.to_string(),
        }
    }
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Scalar {
    Initialized {
        primitive: Primitive,
        valid_range: ValidRange,
    },
    Union {
        primitive: Primitive,
    },
}
impl Scalar {
    fn new(tcx: TyCtxt<'_>, scalar: rustc_abi::Scalar) -> Self {
        match scalar {
            rustc_abi::Scalar::Initialized { value, valid_range } => Self::Initialized {
                primitive: Primitive::new(value, Some(tcx)),
                valid_range: ValidRange::new(valid_range),
            },
            rustc_abi::Scalar::Union { value } => Self::Union {
                primitive: Primitive::new(value, Some(tcx)),
            },
        }
    }
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum BackendRepr {
    Scalar {
        scalar: Scalar,
    },
    ScalarPair {
        first: Scalar,
        second: Scalar,
        second_offset_bytes: u64,
    },
    ScalableSimdVector {
        element: Scalar,
        lane_count: u64,
        vector_count: u64,
    },
    SimdVector {
        element: Scalar,
        lane_count: u64,
    },
    Memory {
        sized: bool,
    },
}
impl BackendRepr {
    fn new(tcx: TyCtxt<'_>, repr: rustc_abi::BackendRepr) -> Self {
        use rustc_abi::BackendRepr as R;
        match repr {
            R::Scalar(s) => Self::Scalar {
                scalar: Scalar::new(tcx, s),
            },
            R::ScalarPair { a, b, b_offset } => Self::ScalarPair {
                first: Scalar::new(tcx, a),
                second: Scalar::new(tcx, b),
                second_offset_bytes: b_offset.bytes(),
            },
            R::SimdScalableVector {
                element,
                count,
                number_of_vectors,
            } => Self::ScalableSimdVector {
                element: Scalar::new(tcx, element),
                lane_count: count.as_u64(),
                vector_count: number_of_vectors.0 as u64,
            },
            R::SimdVector { element, count } => Self::SimdVector {
                element: Scalar::new(tcx, element),
                lane_count: count.as_u64(),
            },
            R::Memory { sized } => Self::Memory { sized },
        }
    }
}
#[derive(Serialize)]
pub(super) struct Niche {
    offset_bytes: u64,
    primitive: Primitive,
    valid_range: ValidRange,
}
impl Niche {
    fn new(tcx: TyCtxt<'_>, n: rustc_abi::Niche) -> Self {
        Self {
            offset_bytes: n.offset.bytes(),
            primitive: Primitive::new(n.value, Some(tcx)),
            valid_range: ValidRange::new(n.valid_range),
        }
    }
}
#[derive(Serialize)]
pub(super) struct IndexRange {
    start: usize,
    end: usize,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum TagEncoding {
    Direct,
    Niche {
        untagged_variant: usize,
        niche_variants: IndexRange,
        niche_start: String,
    },
}
#[derive(Serialize)]
pub(super) struct Variant {
    variant_index: usize,
    size_bytes: u64,
    backend_repr: BackendRepr,
    field_offsets_bytes: Vec<u64>,
    uninhabited: bool,
    fields: Fields,
    largest_niche: Option<Niche>,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Variants {
    Empty,
    Single {
        variant_index: usize,
    },
    Multiple {
        tag: Scalar,
        tag_encoding: TagEncoding,
        tag_field_index: usize,
        variants: Vec<Variant>,
    },
}
impl Layout {
    pub fn new<'tcx>(
        tcx: TyCtxt<'tcx>,
        layout: rustc_abi::TyAndLayout<'tcx, rustc_middle::ty::Ty<'tcx>>,
    ) -> Self {
        use rustc_abi::{TagEncoding as T, Variants as V};
        let variants = match &layout.variants {
            V::Empty => Variants::Empty,
            V::Single { index } => Variants::Single {
                variant_index: index.index(),
            },
            V::Multiple {
                tag,
                tag_encoding,
                tag_field,
                variants,
            } => Variants::Multiple {
                tag: Scalar::new(tcx, *tag),
                tag_field_index: tag_field.index(),
                tag_encoding: match tag_encoding {
                    T::Direct => TagEncoding::Direct,
                    T::Niche {
                        untagged_variant,
                        niche_variants,
                        niche_start,
                    } => TagEncoding::Niche {
                        untagged_variant: untagged_variant.index(),
                        niche_variants: IndexRange {
                            start: niche_variants.start.index(),
                            end: niche_variants.last.index(),
                        },
                        niche_start: niche_start.to_string(),
                    },
                },
                variants: variants
                    .iter_enumerated()
                    .map(|(index, variant)| {
                        let full = rustc_abi::LayoutData::for_variant(&layout, index);
                        Variant {
                            variant_index: index.index(),
                            size_bytes: variant.size.bytes(),
                            backend_repr: BackendRepr::new(tcx, variant.backend_repr),
                            field_offsets_bytes: variant
                                .field_offsets
                                .iter()
                                .map(|x| x.bytes())
                                .collect(),
                            uninhabited: variant.is_uninhabited(),
                            fields: Fields::from_rustc(&full.fields),
                            largest_niche: full.largest_niche.map(|n| Niche::new(tcx, n)),
                        }
                    })
                    .collect(),
            },
        };
        Self {
            size_bytes: layout.size.bytes(),
            abi_align_bytes: layout.align.abi.bytes(),
            unadjusted_abi_align_bytes: layout.unadjusted_abi_align.bytes(),
            max_repr_align_bytes: layout.max_repr_align.map(|x| x.bytes()),
            repr_c: layout.repr_c,
            uninhabited: layout.uninhabited,
            fields: Fields::from_rustc(&layout.fields),
            field_offsets_bytes: (0..layout.fields.count())
                .map(|i| layout.fields.offset(i).bytes())
                .collect(),
            variants,
            backend_repr: BackendRepr::new(tcx, layout.backend_repr),
            largest_niche: layout.largest_niche.map(|n| Niche::new(tcx, n)),
            randomization_seed: layout.randomization_seed.as_u64(),
        }
    }
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum CanonAbi {
    C,
    Rust,
    RustCold,
    RustPreserveNone,
    RustTail,
    Custom,
    Swift,
    Arm { arm_call: &'static str },
    GpuKernel,
    Interrupt { interrupt_kind: &'static str },
    X86 { x86_call: &'static str },
}
impl CanonAbi {
    fn new(abi: rustc_abi::CanonAbi) -> Self {
        use rustc_abi::CanonAbi as A;
        match abi {
            A::C => Self::C,
            A::Rust => Self::Rust,
            A::RustCold => Self::RustCold,
            A::RustPreserveNone => Self::RustPreserveNone,
            A::RustTail => Self::RustTail,
            A::Custom => Self::Custom,
            A::Swift => Self::Swift,
            A::GpuKernel => Self::GpuKernel,
            A::Arm(call) => Self::Arm {
                arm_call: match call {
                    rustc_abi::ArmCall::Aapcs => "aapcs",
                    rustc_abi::ArmCall::CCmseNonSecureCall => "cmse_nonsecure_call",
                    rustc_abi::ArmCall::CCmseNonSecureEntry => "cmse_nonsecure_entry",
                },
            },
            A::Interrupt(kind) => Self::Interrupt {
                interrupt_kind: match kind {
                    rustc_abi::InterruptKind::Avr => "avr",
                    rustc_abi::InterruptKind::AvrNonBlocking => "avr_non_blocking",
                    rustc_abi::InterruptKind::Msp430 => "msp430",
                    rustc_abi::InterruptKind::RiscvMachine => "riscv_machine",
                    rustc_abi::InterruptKind::RiscvSupervisor => "riscv_supervisor",
                    rustc_abi::InterruptKind::X86 => "x86",
                },
            },
            A::X86(call) => Self::X86 {
                x86_call: match call {
                    rustc_abi::X86Call::Fastcall => "fastcall",
                    rustc_abi::X86Call::Stdcall => "stdcall",
                    rustc_abi::X86Call::SysV64 => "sysv64",
                    rustc_abi::X86Call::Thiscall => "thiscall",
                    rustc_abi::X86Call::Vectorcall => "vectorcall",
                    rustc_abi::X86Call::Win64 => "win64",
                },
            },
        }
    }
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Captures {
    None,
    Address,
    ReadOnly,
    Unrestricted,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum ArgExtension {
    None,
    ZeroExtend,
    SignExtend,
}
#[derive(Serialize)]
pub(super) struct ArgAttributes {
    regular_bits: u16,
    captures: Captures,
    no_alias: bool,
    non_null: bool,
    read_only: bool,
    in_register: bool,
    no_undef: bool,
    writable: bool,
    no_free: bool,
    arg_extension: ArgExtension,
    pointee_size_bytes: u64,
    pointee_align_bytes: Option<u64>,
}
impl ArgAttributes {
    fn new(a: rustc_target::callconv::ArgAttributes) -> Self {
        use rustc_target::callconv::{ArgAttribute as A, ArgExtension as E};
        let has = |x| a.regular.contains(x);
        Self {
            regular_bits: a.regular.bits(),
            captures: if has(A::CapturesNone) {
                Captures::None
            } else if has(A::CapturesAddress) {
                Captures::Address
            } else if has(A::CapturesReadOnly) {
                Captures::ReadOnly
            } else {
                Captures::Unrestricted
            },
            no_alias: has(A::NoAlias),
            non_null: has(A::NonNull),
            read_only: has(A::ReadOnly),
            in_register: has(A::InReg),
            no_undef: has(A::NoUndef),
            writable: has(A::Writable),
            no_free: has(A::NoFree),
            arg_extension: match a.arg_ext {
                E::None => ArgExtension::None,
                E::Zext => ArgExtension::ZeroExtend,
                E::Sext => ArgExtension::SignExtend,
            },
            pointee_size_bytes: a.pointee_size.bytes(),
            pointee_align_bytes: a.pointee_align.map(|x| x.bytes()),
        }
    }
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum RegKind {
    Integer,
    Float,
    PpcF128,
    Vector { hint_element: Primitive },
}
#[derive(Serialize)]
pub(super) struct Reg {
    kind: RegKind,
    size_bits: u64,
}
impl Reg {
    fn new(r: rustc_abi::Reg) -> Self {
        use rustc_abi::RegKind as K;
        Self {
            kind: match r.kind {
                K::Integer => RegKind::Integer,
                K::Float => RegKind::Float,
                K::PpcF128 => RegKind::PpcF128,
                K::Vector { hint_vector_elem } => RegKind::Vector {
                    hint_element: Primitive::new(hint_vector_elem, None),
                },
            },
            size_bits: r.size.bits(),
        }
    }
}
#[derive(Serialize)]
pub(super) struct CastTarget {
    prefix_registers: Vec<Reg>,
    rest_offset_bytes: Option<u64>,
    rest_register: Reg,
    rest_total_bytes: u64,
    rest_is_consecutive: bool,
    attributes: ArgAttributes,
}
impl CastTarget {
    fn new(c: &rustc_target::callconv::CastTarget) -> Self {
        Self {
            prefix_registers: c.prefix.iter().copied().map(Reg::new).collect(),
            rest_offset_bytes: c.rest_offset.map(|x| x.bytes()),
            rest_register: Reg::new(c.rest.unit),
            rest_total_bytes: c.rest.total.bytes(),
            rest_is_consecutive: c.rest.is_consecutive,
            attributes: ArgAttributes::new(c.attrs),
        }
    }
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum IndirectMode {
    Pointer,
    OnStack,
    AmdgpuKernelArgument,
}
#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum PassMode {
    Ignore,
    Direct {
        attributes: ArgAttributes,
    },
    Pair {
        first: ArgAttributes,
        second: ArgAttributes,
    },
    Cast {
        pad_i32_count: u8,
        target: CastTarget,
    },
    Indirect {
        attributes: ArgAttributes,
        address_space: Option<u32>,
        mode: IndirectMode,
    },
    IndirectUnsized {
        attributes: ArgAttributes,
        metadata_attributes: ArgAttributes,
    },
}
impl PassMode {
    fn new(p: &rustc_target::callconv::PassMode) -> Self {
        use rustc_target::callconv::{IndirectMode as I, PassMode as P};
        match p {
            P::Ignore => Self::Ignore,
            P::Direct(a) => Self::Direct {
                attributes: ArgAttributes::new(*a),
            },
            P::Pair(a, b) => Self::Pair {
                first: ArgAttributes::new(*a),
                second: ArgAttributes::new(*b),
            },
            P::Cast {
                pad_i32_count,
                cast,
            } => Self::Cast {
                pad_i32_count: *pad_i32_count,
                target: CastTarget::new(cast),
            },
            P::Indirect {
                attrs,
                address_space,
                mode,
            } => Self::Indirect {
                attributes: ArgAttributes::new(*attrs),
                address_space: address_space.map(|x| x.0),
                mode: match mode {
                    I::Pointer => IndirectMode::Pointer,
                    I::OnStack => IndirectMode::OnStack,
                    I::AmdgpuKernelArg => IndirectMode::AmdgpuKernelArgument,
                },
            },
            P::IndirectUnsized { attrs, meta_attrs } => Self::IndirectUnsized {
                attributes: ArgAttributes::new(*attrs),
                metadata_attributes: ArgAttributes::new(*meta_attrs),
            },
        }
    }
}
#[derive(Serialize)]
pub(super) struct ArgAbi {
    #[serde(rename = "type")]
    pub ty: u64,
    pub layout: usize,
    mode: PassMode,
}
#[derive(Serialize)]
pub(super) struct FnAbi {
    calling_convention: CanonAbi,
    c_variadic: bool,
    fixed_count: u32,
    can_unwind: bool,
    #[serde(rename = "return")]
    ret: ArgAbi,
    arguments: Vec<ArgAbi>,
}
impl FnAbi {
    pub fn new<'tcx>(
        context: &mut super::ExportContext<'tcx>,
        tcx: TyCtxt<'tcx>,
        abi: &rustc_target::callconv::FnAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
    ) -> Result<Self, String> {
        fn arg<'tcx>(
            context: &mut super::ExportContext<'tcx>,
            tcx: TyCtxt<'tcx>,
            a: &rustc_target::callconv::ArgAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
        ) -> Result<ArgAbi, String> {
            let ty = super::type_json(context, tcx, a.layout.ty)?;
            let layout = super::layout_value_json(context, tcx, a.layout) as usize;
            Ok(ArgAbi {
                ty,
                layout,
                mode: PassMode::new(&a.mode),
            })
        }
        Ok(Self {
            calling_convention: CanonAbi::new(abi.conv),
            c_variadic: abi.c_variadic,
            fixed_count: abi.fixed_count,
            can_unwind: abi.can_unwind,
            ret: arg(context, tcx, &abi.ret)?,
            arguments: abi
                .args
                .iter()
                .map(|a| arg(context, tcx, a))
                .collect::<Result<_, _>>()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn pointer_layout_and_register_hint_preserve_distinct_width_contracts() {
        assert_eq!(
            serde_json::to_value(Primitive::Pointer {
                address_space: 0,
                size_bytes: Some(8),
            })
            .unwrap(),
            json!({"kind":"pointer", "address_space":0, "size_bytes":8})
        );
        assert_eq!(
            serde_json::to_value(RegKind::Vector {
                hint_element: Primitive::Pointer {
                    address_space: 0,
                    size_bytes: None
                },
            })
            .unwrap(),
            json!({"kind":"vector", "hint_element":{"kind":"pointer", "address_space":0}})
        );
    }

    #[test]
    fn abi_and_pass_mode_keep_consumer_tags() {
        assert_eq!(
            serde_json::to_value(CanonAbi::RustPreserveNone).unwrap(),
            json!({"kind":"rust_preserve_none"})
        );
        assert_eq!(
            serde_json::to_value(PassMode::Ignore).unwrap(),
            json!({"kind":"Ignore"})
        );
    }
}
