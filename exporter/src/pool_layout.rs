//! Semantic layout and calling-convention data retained until document output.
use rustc_index::Idx;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum Layout {
    PrimitiveRecipe { primitive_recipe: &'static str },
    TupleRecipe { tuple_type: u64 },
    Material(FullLayout),
}
#[derive(Serialize)]
pub(super) struct FullLayout {
    pub size_bytes: u64,
    pub abi_align_bytes: u64,
    pub unadjusted_abi_align_bytes: u64,
    pub max_repr_align_bytes: Option<u64>,
    pub repr_c: bool,
    pub uninhabited: bool,
    pub fields: Fields,
    pub field_offsets_bytes: FieldOffsets,
    pub variants: Variants,
    pub backend_repr: BackendRepr,
    pub largest_niche: Option<Niche>,
    pub randomization_seed: u64,
}
#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum FieldOffsets {
    Explicit(Vec<u64>),
    ArrayFormula { kind: &'static str, stride_bytes: u64, field_count: u64 },
}
impl FieldOffsets {
    fn from_rustc<I: Idx>(fields: &rustc_abi::FieldsShape<I>) -> Self {
        match fields {
            rustc_abi::FieldsShape::Array { stride, count } => Self::ArrayFormula {
                kind: "array", stride_bytes: stride.bytes(), field_count: *count,
            },
            _ => Self::Explicit((0..fields.count()).map(|i| fields.offset(i).bytes()).collect()),
        }
    }
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
        let primitive_recipe = match layout.ty.kind() {
            rustc_middle::ty::Bool => Some("bool"),
            rustc_middle::ty::Char => Some("char"),
            rustc_middle::ty::Int(kind) => Some(kind.name_str()),
            rustc_middle::ty::Uint(kind) => Some(kind.name_str()),
            rustc_middle::ty::Float(kind) => Some(kind.name_str()),
            rustc_middle::ty::FnPtr(..) => Some("fn_pointer"),
            rustc_middle::ty::Never => Some("never"),
            _ => None,
        };
        if let Some(primitive_recipe) = primitive_recipe {
            return Self::PrimitiveRecipe { primitive_recipe };
        }
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
        Self::Material(FullLayout {
            size_bytes: layout.size.bytes(),
            abi_align_bytes: layout.align.abi.bytes(),
            unadjusted_abi_align_bytes: layout.unadjusted_abi_align.bytes(),
            max_repr_align_bytes: layout.max_repr_align.map(|x| x.bytes()),
            repr_c: layout.repr_c,
            uninhabited: layout.uninhabited,
            fields: Fields::from_rustc(&layout.fields),
            field_offsets_bytes: FieldOffsets::from_rustc(&layout.fields),
            variants,
            backend_repr: BackendRepr::new(tcx, layout.backend_repr),
            largest_niche: layout.largest_niche.map(|n| Niche::new(tcx, n)),
            randomization_seed: layout.randomization_seed.as_u64(),
        })
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
pub(super) enum ArgExtension {
    None,
    ZeroExtend,
    SignExtend,
}
#[derive(Serialize)]
pub(super) struct ArgAttributes {
    regular_bits: u16,
    arg_extension: ArgExtension,
    pointee_size_bytes: u64,
    pointee_align_bytes: Option<u64>,
}
impl ArgAttributes {
    pub(super) fn new(a: rustc_target::callconv::ArgAttributes) -> Self {
        use rustc_target::callconv::ArgExtension as E;
        Self {
            regular_bits: a.regular.bits(),
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
    Initial,
    ScalarRust,
    ScalarSysvArgument,
    ScalarSysvReturn,
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
    pub mode: PassMode,
}
#[derive(Serialize)]
pub(super) struct UnwindDefinition {
    never_unwind: bool,
    foreign_item: bool,
    drop_glue: bool,
}
#[derive(Serialize)]
pub(super) struct UnwindSeed {
    abi: super::pool_type::ExternAbi,
    definition: Option<UnwindDefinition>,
    panic_unwinds: bool,
    panic_in_drop_unwinds: bool,
    #[serde(skip)]
    reference_can_unwind: bool,
}
impl UnwindSeed {
    pub(super) fn new<'tcx>(tcx: TyCtxt<'tcx>, abi: rustc_abi::ExternAbi,
        instance: Option<rustc_middle::ty::Instance<'tcx>>) -> Self {
        use rustc_middle::ty::{InstanceKind, ShimKind};
        let definition_id = instance.and_then(|instance| match instance.def {
            InstanceKind::Item(did) | InstanceKind::Intrinsic(did)
            | InstanceKind::Shim(ShimKind::DropGlue(did, _)) => Some(did),
            _ => None,
        });
        let definition = definition_id.map(|did| UnwindDefinition {
            never_unwind: tcx.codegen_fn_attrs(did).flags.contains(
                rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NEVER_UNWIND),
            foreign_item: tcx.is_foreign_item(did),
            drop_glue: tcx.is_lang_item(did, rustc_attr_ir::lang_items::LangItem::DropGlue),
        });
        Self { abi: super::extern_abi_json(abi), definition,
            panic_unwinds: tcx.sess.panic_strategy().unwinds(),
            panic_in_drop_unwinds: tcx.sess.opts.unstable_opts.panic_in_drop.unwinds(),
            reference_can_unwind: rustc_middle::ty::layout::fn_can_unwind(tcx, definition_id, abi) }
    }
    pub(super) fn for_instance<'tcx>(tcx: TyCtxt<'tcx>,
        instance: rustc_middle::ty::Instance<'tcx>) -> Result<Self, String> {
        use rustc_middle::ty::{self, InstanceKind, ShimKind};
        let abi = if matches!(instance.def, InstanceKind::Shim(ShimKind::ThreadLocal(..))) {
            rustc_abi::ExternAbi::Rust
        } else {
            let ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
            match ty.kind() {
                ty::FnDef(..) => ty.fn_sig(tcx).skip_binder().abi(),
                ty::Closure(_, args) => args.as_closure().sig().skip_binder().abi(),
                ty::CoroutineClosure(_, args) => args.as_coroutine_closure()
                    .coroutine_closure_sig().skip_binder().fn_sig_kind.abi(),
                ty::Coroutine(..) => rustc_abi::ExternAbi::Rust,
                _ => return Err("FnAbi unwind material requires callable source signature".into()),
            }
        };
        Ok(Self::new(tcx, abi, Some(instance)))
    }
}
#[derive(Serialize)]
pub(super) struct SignatureSeed {
    signature: super::pool_type::FunctionSignature,
    extra_argument_types: Vec<u64>,
    caller_location: Option<u64>,
}
impl SignatureSeed {
    pub(super) fn new<'tcx>(context: &mut super::ExportContext<'tcx>, tcx: TyCtxt<'tcx>,
        signature: rustc_middle::ty::FnSig<'tcx>,
        extra: &'tcx rustc_middle::ty::List<rustc_middle::ty::Ty<'tcx>>,
        caller: Option<rustc_middle::ty::Ty<'tcx>>) -> Result<Option<Self>, String> {
        // Only raw, already concrete primitive/tuple signatures are admitted.
        // Generic, bound-region and instance signature rewrites remain residual.
        fn material(ty: rustc_middle::ty::Ty<'_>) -> bool {
            use rustc_middle::ty;
            match ty.kind() {
                ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => true,
                ty::Tuple(fields) => fields.iter().all(material),
                _ => false,
            }
        }
        if !signature.inputs_and_output.iter().all(material) || !extra.iter().all(material) {
            return Ok(None);
        }
        Ok(Some(Self {
            signature: super::fn_sig_json_inner(context, tcx, signature)?,
            extra_argument_types: extra.iter().map(|ty| super::type_json(context, tcx, ty)).collect::<Result<_,_>>()?,
            caller_location: caller.map(|ty| super::type_json(context, tcx, ty)).transpose()?,
        }))
    }
}
#[derive(Serialize)]
pub(super) struct FnAbi {
    calling_convention: CanonAbi,
    c_variadic: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    fixed_count: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    signature_seed: Option<SignatureSeed>,
    unwind_seed: UnwindSeed,
    #[serde(rename = "return")]
    pub ret: super::shared_json::Shared<ArgAbi>,
    pub arguments: Vec<super::shared_json::Shared<ArgAbi>>,
}
impl FnAbi {
    pub fn new<'tcx>(
        context: &mut super::ExportContext<'tcx>,
        tcx: TyCtxt<'tcx>,
        abi: &rustc_target::callconv::FnAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
        unwind_seed: UnwindSeed,
        signature_seed: Option<SignatureSeed>,
    ) -> Result<Self, String> {
        if unwind_seed.reference_can_unwind != abi.can_unwind {
            return Err("FnAbi unwind material source signature disagrees with rustc final ABI".into());
        }
        if let Some(seed) = &signature_seed {
            let fixed = seed.signature.inputs.len().checked_sub(
                usize::from(seed.signature.abi.kind == "rust_call"));
            if fixed != Some(abi.fixed_count as usize)
                || seed.signature.c_variadic != abi.c_variadic {
                return Err("source signature construction disagrees with rustc fixed-count/variadic result".into());
            }
        }
        fn arg<'tcx>(
            context: &mut super::ExportContext<'tcx>,
            tcx: TyCtxt<'tcx>,
            a: &rustc_target::callconv::ArgAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
            conv: rustc_abi::CanonAbi,
            is_return: bool,
        ) -> Result<super::shared_json::Shared<ArgAbi>, String> {
            let ty = super::type_json(context, tcx, a.layout.ty)?;
            let layout = super::layout_value_json(context, tcx, a.layout) as usize;
            Ok(ArgAbi {
                ty,
                layout,
                mode: {
                    // Pinned ty_utils abi.rs scalar attributes return immediately for
                    // nonpointers. The x86_64 Rust/SysV scalar classifiers then only
                    // extend integers (callconv/mod.rs and x86_64.rs). No pointer
                    // pointee facts, aggregate classification, or deduced indirect
                    // attributes are inferred by this material recipe.
                    let scalar_recipe = match a.layout.backend_repr {
                        rustc_abi::BackendRepr::Scalar(scalar)
                            if !matches!(scalar.primitive(), rustc_abi::Primitive::Pointer(_))
                            && matches!(a.layout.ty.kind(),
                                rustc_middle::ty::Bool | rustc_middle::ty::Char |
                                rustc_middle::ty::Int(_) | rustc_middle::ty::Uint(_) |
                                rustc_middle::ty::Float(_))
                            && tcx.sess.target.arch == rustc_target::spec::Arch::X86_64
                            && tcx.data_layout.pointer_size().bytes() == 8 => {
                                match conv {
                                    rustc_abi::CanonAbi::Rust => Some((PassMode::ScalarRust, 0)),
                                    rustc_abi::CanonAbi::C
                                        if !tcx.sess.target.is_like_windows
                                        && !tcx.sess.target.is_like_darwin =>
                                        Some(if is_return { (PassMode::ScalarSysvReturn, 8) }
                                             else { (PassMode::ScalarSysvArgument, 32) }),
                                    _ => None,
                                }
                            }
                        _ => None,
                    };
                    if let Some((recipe, extension_bits)) = scalar_recipe {
                        let mut reconstructed = rustc_target::callconv::ArgAbi::new(a.layout, |scalar, _| {
                            let mut attrs = rustc_target::callconv::ArgAttributes::new();
                            if !scalar.is_uninit_valid() {
                                attrs.set(rustc_target::callconv::ArgAttribute::NoUndef);
                            }
                            attrs
                        });
                        reconstructed.extend_integer_width_to(extension_bits);
                        if reconstructed.mode != a.mode {
                            return Err("nonpointer scalar ABI source rule disagrees with rustc final mode".into());
                        }
                        recipe
                    } else {
                    // rustc's target adjustment is retained unless its complete mode
                    // equals the source initial constructor with empty scalar attrs.
                    // Lean runs that constructor from the physical layout on demand.
                    let initial = rustc_target::callconv::ArgAbi::new(a.layout, |_, _| {
                        rustc_target::callconv::ArgAttributes::new()
                    });
                    if initial.mode == a.mode { PassMode::Initial }
                    else { PassMode::new(&a.mode) }
                    }
                },
            }.into())
        }
        Ok(Self {
            calling_convention: CanonAbi::new(abi.conv),
            c_variadic: abi.c_variadic,
            fixed_count: signature_seed.is_none().then_some(abi.fixed_count),
            signature_seed,
            unwind_seed,
            ret: arg(context, tcx, &abi.ret, abi.conv, true)?,
            arguments: abi
                .args
                .iter()
                .map(|a| arg(context, tcx, a, abi.conv, false))
                .collect::<Result<_, _>>()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn huge_array_offsets_are_constant_size_and_match_pinned_queries() {
        for (stride, count) in [(1, 1u64 << 50), (4, 1u64 << 48), (0, u64::MAX), (8, 0), (8, 1)] {
            let fields = rustc_abi::FieldsShape::<rustc_abi::FieldIdx>::Array {
                stride: rustc_abi::Size::from_bytes(stride), count,
            };
            let wire = serde_json::to_string(&FieldOffsets::from_rustc(&fields)).unwrap();
            assert!(wire.len() < 128);
            assert_eq!(serde_json::from_str::<serde_json::Value>(&wire).unwrap(),
                json!({"kind":"array", "stride_bytes":stride, "field_count":count}));
            if count != 0 {
                for index in [0, count / 2, count - 1] {
                    assert_eq!(fields.offset(usize::try_from(index).unwrap()).bytes(), stride * index);
                }
            }
        }
    }

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
