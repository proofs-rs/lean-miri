//! Raw generic trees for early substitution. No normalization, trait selection,
//! layout queries or instantiated-result enumeration occurs in this module.
//! Pinned rustc_type_ir::binder::ArgFolder determines binder placement.
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::ty::inherent::IntoKind;

fn quote(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""), '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"), '\r' => out.push_str("\\r"), '\t' => out.push_str("\\t"),
            c if c < ' ' => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"'); out
}
fn array(values: impl IntoIterator<Item=String>) -> String {
    format!("[{}]", values.into_iter().collect::<Vec<_>>().join(","))
}
fn atom(sort: &str, tag: &str, payload: &str) -> String {
    format!("{{\"kind\":\"atom\",\"sort\":{},\"tag\":{},\"payload\":{}}}", quote(sort),quote(tag),quote(payload))
}
fn parameter(sort: &str, index: u32) -> String {
    format!("{{\"kind\":\"parameter\",\"sort\":{},\"index\":{index}}}",quote(sort))
}
fn bound(sort: &str, index: ty::BoundVarIndexKind, variable: u32, identity: &str) -> String {
    let index = match index { ty::BoundVarIndexKind::Bound(d) => format!("{}",d.as_u32()), ty::BoundVarIndexKind::Canonical => "null".into() };
    format!("{{\"kind\":\"bound\",\"sort\":{},\"index\":{index},\"variable\":{variable},\"identity\":{identity}}}",quote(sort))
}
fn definition_identity(def: rustc_hir::def_id::DefId) -> String {
    format!("{{\"crate\":{},\"index\":{}}}",def.krate.as_u32(),def.index.as_u32())
}
fn definition(sort: &str, tag: &str, def: rustc_hir::def_id::DefId, children: Vec<String>) -> String {
    format!("{{\"kind\":\"definition\",\"sort\":{},\"tag\":{},\"definition\":{},\"children\":{}}}",quote(sort),quote(tag),definition_identity(def),array(children))
}
fn bound_region(kind: ty::BoundRegionKind) -> String {
    match kind {
        ty::BoundRegionKind::Anon => "{\"kind\":\"anonymous\"}".into(),
        ty::BoundRegionKind::NamedForPrinting(name) => format!("{{\"kind\":\"named_for_printing\",\"name\":{}}}",quote(name.as_str())),
        ty::BoundRegionKind::Named(def) => format!("{{\"kind\":\"named\",\"definition\":{}}}",definition_identity(def)),
        ty::BoundRegionKind::ClosureEnv => "{\"kind\":\"closure_environment\"}".into(),
    }
}
fn bound_type(kind: ty::BoundTyKind) -> String {
    match kind {
        ty::BoundTyKind::Anon => "{\"kind\":\"anonymous\"}".into(),
        ty::BoundTyKind::Param(def) => format!("{{\"kind\":\"named\",\"definition\":{}}}",definition_identity(def)),
    }
}
pub(super) fn bound_variable(value: ty::BoundVariableKind) -> String {
    match value {
        ty::BoundVariableKind::Ty(kind) => format!("{{\"kind\":\"type\",\"identity\":{}}}",bound_type(kind)),
        ty::BoundVariableKind::Region(kind) => format!("{{\"kind\":\"region\",\"identity\":{}}}",bound_region(kind)),
        ty::BoundVariableKind::Const => "{\"kind\":\"constant\"}".into(),
    }
}
fn node(sort: &str, tag: &str, payload: &str, children: Vec<String>) -> String {
    format!("{{\"kind\":\"node\",\"sort\":{},\"tag\":{},\"payload\":{},\"children\":{}}}",quote(sort),quote(tag),quote(payload),array(children))
}
fn binder(variables: impl IntoIterator<Item=String>, value: String) -> String {
    format!("{{\"kind\":\"binder\",\"variables\":{},\"value\":{value}}}",array(variables))
}
pub fn argument<'tcx>(tcx: TyCtxt<'tcx>, value: ty::GenericArg<'tcx>) -> Result<String,String> {
    match value.kind() {
        ty::GenericArgKind::Type(t) => type_tree(tcx,t),
        ty::GenericArgKind::Lifetime(r) => region_tree(r),
        ty::GenericArgKind::Const(c) => constant_tree(tcx,c),
    }
}
fn arguments<'tcx>(tcx: TyCtxt<'tcx>, values: ty::GenericArgsRef<'tcx>) -> Result<Vec<String>,String> {
    values.iter().map(|v|argument(tcx,v)).collect()
}
fn pattern_tree<'tcx>(tcx: TyCtxt<'tcx>, pattern: ty::Pattern<'tcx>) -> Result<String,String> {
    Ok(match pattern.kind() {
        ty::PatternKind::Range { start, end } => node("aggregate","pattern_range","",vec![constant_tree(tcx,start)?,constant_tree(tcx,end)?]),
        ty::PatternKind::Or(values) => node("aggregate","pattern_or","",values.iter().map(|p|pattern_tree(tcx,p)).collect::<Result<_,_>>()?),
        ty::PatternKind::NotNull => atom("aggregate","pattern_not_null",""),
    })
}
pub(super) fn predicate_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::PolyExistentialPredicate<'tcx>) -> Result<String,String> {
    let body = match value.skip_binder() {
        ty::ExistentialPredicate::Trait(t) => definition("aggregate","trait",t.def_id,arguments(tcx,t.args)?),
        ty::ExistentialPredicate::AutoTrait(d) => definition("aggregate","auto_trait",d,vec![]),
        ty::ExistentialPredicate::Projection(p) => {
            let mut children=arguments(tcx,p.args)?;
            children.push(match p.term.kind() { ty::TermKind::Ty(t)=>type_tree(tcx,t)?, ty::TermKind::Const(c)=>constant_tree(tcx,c)? });
            definition("aggregate","projection",p.def_id,children)
        }
    };
    Ok(binder(value.bound_vars().iter().map(bound_variable),body))
}
pub fn region_tree(value: ty::Region<'_>) -> Result<String,String> {
    Ok(match value.kind() {
        ty::ReEarlyParam(p) => parameter("region",p.index),
        ty::ReBound(index,b) => bound("region",index,b.var.as_u32(),&bound_region(b.kind)),
        ty::ReStatic => atom("region","static",""),
        ty::ReErased => atom("region","erased",""),
        ty::ReLateParam(p) => definition("region","late_parameter",p.scope,vec![match p.kind {
            ty::LateParamRegionKind::Anon(index) => atom("region","anonymous",&index.to_string()),
            ty::LateParamRegionKind::NamedAnon(index,name) => node("region","named_anonymous",&index.to_string(),vec![atom("region","printing_name",name.as_str())]),
            ty::LateParamRegionKind::Named(def) => definition("region","named",def,vec![]),
            ty::LateParamRegionKind::ClosureEnv => atom("region","closure_environment",""),
        }]),
        ty::RePlaceholder(p) => format!("{{\"kind\":\"placeholder\",\"sort\":\"region\",\"universe\":{},\"variable\":{},\"identity\":{}}}",p.universe.index(),p.bound.var.as_u32(),bound_region(p.bound.kind)),
        ty::ReVar(v) => format!("{{\"kind\":\"inference\",\"sort\":\"region\",\"variable\":{}}}",v.as_u32()),
        ty::ReError(_) => return Err("error region in generic material".into()),
    })
}
pub fn constant_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Const<'tcx>) -> Result<String,String> {
    Ok(match value.kind() {
        ty::ConstKind::Param(p) => parameter("constant",p.index),
        ty::ConstKind::Bound(i,b) => bound("constant",i,b.var.as_u32(),"{\"kind\":\"anonymous\"}"),
        ty::ConstKind::Placeholder(p) => format!("{{\"kind\":\"placeholder\",\"sort\":\"constant\",\"universe\":{},\"variable\":{},\"identity\":{{\"kind\":\"anonymous\"}}}}",p.universe.index(),p.bound.var.as_u32()),
        ty::ConstKind::Value(v) => node("constant","value","",vec![type_tree(tcx,v.ty)?,value_tree(tcx,v.valtree)?]),
        ty::ConstKind::Alias(r,a) => {
            let (kind,def)=match a.kind {
                ty::AliasConstKind::Projection {def_id}=>("projection",def_id),
                ty::AliasConstKind::InherentSelf {def_id}=>("inherent_self",def_id),
                ty::AliasConstKind::InherentImpl {def_id}=>("inherent_impl",def_id),
                ty::AliasConstKind::Free {def_id}=>("free",def_id),
                ty::AliasConstKind::Anon {def_id}=>("anonymous",def_id),
            };
            let rigidity=if r==ty::IsRigid::Yes {"rigid"} else {"not_rigid"};
            definition("constant",&format!("alias_{kind}_{rigidity}"),def,arguments(tcx,a.args)?)
        },
        ty::ConstKind::Expr(e) => {
            let (kind,opcode)=match e.kind {
                ty::ExprKind::Binop(op)=>("binary_expression",(op as u8).to_string()),
                ty::ExprKind::UnOp(op)=>("unary_expression",(op as u8).to_string()),
                ty::ExprKind::FunctionCall=>("function_call_expression",String::new()),
                ty::ExprKind::Cast(op)=>("cast_expression",(op as u8).to_string()),
            };
            node("constant",kind,&opcode,arguments(tcx,e.args())?)
        },
        ty::ConstKind::Infer(_) | ty::ConstKind::Error(_) => return Err("inference/error constant in generic material".into()),
    })
}
fn value_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::ValTree<'tcx>) -> Result<String,String> {
    Ok(match &*value {
        ty::ValTreeKind::Leaf(value) => atom("aggregate","scalar",
            &format!("{{\"bytes\":{},\"bits\":{}}}",value.size().bytes(),value.to_bits_unchecked())),
        ty::ValTreeKind::Branch(values) => node("aggregate","valtree_branch","",
            values.iter().map(|v|constant_tree(tcx,v)).collect::<Result<_,_>>()?),
    })
}
pub fn type_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Ty<'tcx>) -> Result<String,String> {
    Ok(match *value.kind() {
        ty::Param(p) => parameter("type",p.index),
        ty::Bound(i,b) => bound("type",i,b.var.as_u32(),&bound_type(b.kind)),
        ty::Placeholder(p) => format!("{{\"kind\":\"placeholder\",\"sort\":\"type\",\"universe\":{},\"variable\":{},\"identity\":{}}}",p.universe.index(),p.bound.var.as_u32(),bound_type(p.bound.kind)),
        ty::Bool => atom("type","bool",""), ty::Char => atom("type","char",""),
        ty::Str => atom("type","str",""), ty::Never => atom("type","never",""),
        ty::Int(k) => atom("type","int",match k {ty::IntTy::I8=>"i8",ty::IntTy::I16=>"i16",ty::IntTy::I32=>"i32",ty::IntTy::I64=>"i64",ty::IntTy::I128=>"i128",ty::IntTy::Isize=>"isize"}),
        ty::Uint(k) => atom("type","uint",match k {ty::UintTy::U8=>"u8",ty::UintTy::U16=>"u16",ty::UintTy::U32=>"u32",ty::UintTy::U64=>"u64",ty::UintTy::U128=>"u128",ty::UintTy::Usize=>"usize"}),
        ty::Float(k) => atom("type","float",match k {ty::FloatTy::F16=>"f16",ty::FloatTy::F32=>"f32",ty::FloatTy::F64=>"f64",ty::FloatTy::F128=>"f128"}),
        ty::Ref(r,t,m) => node("type","reference",if m.is_mut(){"mutable"}else{"immutable"},vec![region_tree(r)?,type_tree(tcx,t)?]),
        ty::RawPtr(t,m) => node("type","raw_pointer",if m.is_mut(){"mutable"}else{"immutable"},vec![type_tree(tcx,t)?]),
        ty::Slice(t) => node("type","slice","",vec![type_tree(tcx,t)?]),
        ty::Array(t,c) => node("type","array","",vec![type_tree(tcx,t)?,constant_tree(tcx,c)?]),
        ty::Pat(t,p) => node("type","pattern","",vec![type_tree(tcx,t)?,pattern_tree(tcx,p)?]),
        ty::Tuple(types) => node("type","tuple","",types.iter().map(|t|type_tree(tcx,t)).collect::<Result<_,_>>()?),
        ty::Adt(def,args) => definition("type","adt",def.did(),arguments(tcx,args)?),
        ty::Alias(r,a) => {
            let (kind,def)=match a.kind {
                ty::AliasTyKind::Projection {def_id}=>("projection",def_id),
                ty::AliasTyKind::Inherent {def_id}=>("inherent",def_id),
                ty::AliasTyKind::Opaque {def_id}=>("opaque",def_id),
                ty::AliasTyKind::Free {def_id}=>("free",def_id),
            };
            let rigidity=if r==ty::IsRigid::Yes {"rigid"} else {"not_rigid"};
            definition("type",&format!("alias_{kind}_{rigidity}"),def,arguments(tcx,a.args)?)
        },
        ty::Foreign(def) => definition("type","foreign",def,vec![]),
        ty::FnDef(def,args) => definition("type","function_definition",def,vec![binder(args.bound_vars().iter().map(bound_variable),node("aggregate","arguments","",arguments(tcx,args.skip_binder())?))]),
        ty::FnPtr(types,header) => {
            let signature=types.with(header);
            node("type","function_pointer","",vec![signature_tree(tcx,signature)?])
        },
        ty::UnsafeBinder(b) => node("type","unsafe_binder","",vec![binder(b.bound_vars().iter().map(bound_variable),type_tree(tcx,b.skip_binder())?)]),
        ty::Dynamic(predicates,region) => {
            let mut children=predicates.iter().map(|p|predicate_tree(tcx,p)).collect::<Result<Vec<_>,_>>()?;
            children.push(region_tree(region)?);
            node("type","dynamic","",children)
        },
        ty::Closure(def,args) => definition("type","closure",def,arguments(tcx,args)?),
        ty::CoroutineClosure(def,args) => definition("type","coroutine_closure",def,arguments(tcx,args)?),
        ty::Coroutine(def,args) => definition("type","coroutine",def,arguments(tcx,args)?),
        ty::CoroutineWitness(def,args) => definition("type","coroutine_witness",def,arguments(tcx,args)?),
        other => return Err(format!("generic material type constructor not implemented: {other:?}")),
    })
}

pub fn signature_tree<'tcx>(tcx: TyCtxt<'tcx>, signature: ty::PolyFnSig<'tcx>) -> Result<String,String> {
    let body=signature.skip_binder();
    let header=format!("{{\"abi_packed\":{},\"safe\":{},\"c_variadic\":{},\"splatted\":{}}}",
        body.abi().as_packed(),body.fn_sig_kind.is_safe(),body.c_variadic(),
        body.splatted().map(|v|v.to_string()).unwrap_or_else(||"null".into()));
    Ok(binder(signature.bound_vars().iter().map(bound_variable),
        node("aggregate","signature",&header,signature.skip_binder().inputs_and_output.iter()
            .map(|t|type_tree(tcx,t)).collect::<Result<_,_>>()?)))
}

/// Capture each source definition once, before any type arguments are applied.
/// Fields contain their declaration EarlyBinder expressions, not concrete field
/// query results. Abstract associated types require separate trait/impl material.
pub fn definition_template<'tcx>(tcx: TyCtxt<'tcx>, def: rustc_hir::def_id::DefId)
    -> Result<Option<String>,String>
{
    use rustc_hir::def::DefKind as D;
    let kind=tcx.def_kind(def);
    if !matches!(kind,D::Fn|D::AssocFn|D::TyAlias|D::AssocTy|D::Struct|D::Enum|D::Union|D::Const|D::AssocConst|D::AnonConst|D::Static{..}) {
        return Ok(None);
    }
    // Abstract trait associated types have no RHS; asking type_of here would
    // fabricate declaration material or trigger a compiler error. Explicit
    // defaults and impl associated values retain their raw EarlyBinder RHS.
    if kind == D::AssocTy {
        let item = tcx.associated_item(def);
        // RPITIT hidden values are inference output, not a declaration RHS.
        if item.is_impl_trait_in_trait() || !item.defaultness(tcx).has_value() {
            return Ok(None);
        }
    }
    let generics=tcx.generics_of(def);
    let parameters=array((0..generics.count()).map(|i|quote(match generics.param_at(i,tcx).kind {
        ty::GenericParamDefKind::Lifetime=>"region",
        ty::GenericParamDefKind::Type{..}=>"type",
        ty::GenericParamDefKind::Const{..}=>"constant",
    })));
    let type_expression=type_tree(tcx,tcx.type_of(def).instantiate_identity().skip_norm_wip())?;
    let signature=if matches!(kind,D::Fn|D::AssocFn) {
        signature_tree(tcx,tcx.fn_sig(def).instantiate_identity().skip_norm_wip())?
    } else { "null".into() };
    let mut fields=Vec::new();
    if matches!(kind,D::Struct|D::Enum|D::Union) {
        for (variant_index,variant) in tcx.adt_def(def).variants().iter().enumerate() {
            for (field_index,field) in variant.fields.iter().enumerate() {
                let expression=type_tree(tcx,tcx.type_of(field.did).instantiate_identity().skip_norm_wip())?;
                fields.push(format!("{{\"variant\":{variant_index},\"field\":{field_index},\"expression\":{expression}}}"));
            }
        }
    }
    Ok(Some(format!("{{\"parameters\":{parameters},\"type_expression\":{type_expression},\"signature_expression\":{signature},\"fields\":{}}}",array(fields))))
}
