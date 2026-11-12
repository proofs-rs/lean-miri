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
    format!("{{\"kind\":\"bound\",\"sort\":{},\"index\":{index},\"variable\":{variable},\"identity\":{}}}",quote(sort),quote(identity))
}
fn node(sort: &str, tag: &str, payload: &str, children: Vec<String>) -> String {
    format!("{{\"kind\":\"node\",\"sort\":{},\"tag\":{},\"payload\":{},\"children\":{}}}",quote(sort),quote(tag),quote(payload),array(children))
}
fn binder(variables: impl IntoIterator<Item=String>, value: String) -> String {
    format!("{{\"kind\":\"binder\",\"variables\":{},\"value\":{value}}}",array(variables.into_iter().map(|s|quote(&s))))
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
fn predicate_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::PolyExistentialPredicate<'tcx>) -> Result<String,String> {
    let body = match value.skip_binder() {
        ty::ExistentialPredicate::Trait(t) => node("aggregate","trait",&format!("{:?}",t.def_id),arguments(tcx,t.args)?),
        ty::ExistentialPredicate::AutoTrait(d) => atom("aggregate","auto_trait",&format!("{d:?}")),
        ty::ExistentialPredicate::Projection(p) => {
            let mut children=arguments(tcx,p.args)?;
            children.push(match p.term.kind() { ty::TermKind::Ty(t)=>type_tree(tcx,t)?, ty::TermKind::Const(c)=>constant_tree(tcx,c)? });
            node("aggregate","projection",&format!("{:?}",p.def_id),children)
        }
    };
    Ok(binder(value.bound_vars().iter().map(|v|format!("{v:?}")),body))
}
pub fn region_tree(value: ty::Region<'_>) -> Result<String,String> {
    Ok(match value.kind() {
        ty::ReEarlyParam(p) => parameter("region",p.index),
        ty::ReBound(index,b) => bound("region",index,b.var.as_u32(),&format!("{:?}",b.kind)),
        ty::ReStatic => atom("region","static",""),
        ty::ReErased => atom("region","erased",""),
        ty::ReLateParam(p) => atom("region","late_parameter",&format!("{p:?}")),
        ty::RePlaceholder(p) => format!("{{\"kind\":\"placeholder\",\"sort\":\"region\",\"universe\":{},\"variable\":{},\"identity\":{}}}",p.universe.index(),p.bound.var.as_u32(),quote(&format!("{:?}",p.bound.kind))),
        ty::ReVar(v) => format!("{{\"kind\":\"inference\",\"sort\":\"region\",\"variable\":{}}}",v.as_u32()),
        ty::ReError(_) => return Err("error region in generic material".into()),
    })
}
pub fn constant_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Const<'tcx>) -> Result<String,String> {
    Ok(match value.kind() {
        ty::ConstKind::Param(p) => parameter("constant",p.index),
        ty::ConstKind::Bound(i,b) => bound("constant",i,b.var.as_u32(),""),
        ty::ConstKind::Placeholder(p) => format!("{{\"kind\":\"placeholder\",\"sort\":\"constant\",\"universe\":{},\"variable\":{},\"identity\":\"\"}}",p.universe.index(),p.bound.var.as_u32()),
        ty::ConstKind::Value(v) => node("constant","value",&format!("{:?}",v.valtree),vec![type_tree(tcx,v.ty)?]),
        ty::ConstKind::Alias(r,a) => node("constant","alias",&format!("{r:?}:{:?}",a.kind),arguments(tcx,a.args)?),
        ty::ConstKind::Expr(e) => node("constant","expression",&format!("{:?}",e.kind),arguments(tcx,e.args())?),
        ty::ConstKind::Infer(_) | ty::ConstKind::Error(_) => return Err("inference/error constant in generic material".into()),
    })
}
pub fn type_tree<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Ty<'tcx>) -> Result<String,String> {
    Ok(match *value.kind() {
        ty::Param(p) => parameter("type",p.index),
        ty::Bound(i,b) => bound("type",i,b.var.as_u32(),&format!("{:?}",b.kind)),
        ty::Placeholder(p) => format!("{{\"kind\":\"placeholder\",\"sort\":\"type\",\"universe\":{},\"variable\":{},\"identity\":{}}}",p.universe.index(),p.bound.var.as_u32(),quote(&format!("{:?}",p.bound.kind))),
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => atom("type","primitive",&format!("{:?}",value.kind())),
        ty::Ref(r,t,m) => node("type","reference",&format!("{m:?}"),vec![region_tree(r)?,type_tree(tcx,t)?]),
        ty::RawPtr(t,m) => node("type","raw_pointer",&format!("{m:?}"),vec![type_tree(tcx,t)?]),
        ty::Slice(t) => node("type","slice","",vec![type_tree(tcx,t)?]),
        ty::Array(t,c) => node("type","array","",vec![type_tree(tcx,t)?,constant_tree(tcx,c)?]),
        ty::Pat(t,p) => node("type","pattern","",vec![type_tree(tcx,t)?,pattern_tree(tcx,p)?]),
        ty::Tuple(types) => node("type","tuple","",types.iter().map(|t|type_tree(tcx,t)).collect::<Result<_,_>>()?),
        ty::Adt(def,args) => node("type","adt",&format!("{:?}",def.did()),arguments(tcx,args)?),
        ty::Alias(kind,a) => node("type","alias",&format!("{kind:?}:{:?}",a.kind),arguments(tcx,a.args)?),
        ty::Foreign(def) => atom("type","foreign",&format!("{def:?}")),
        ty::FnDef(def,args) => node("type","function_definition",&format!("{def:?}"),vec![binder(args.bound_vars().iter().map(|v|format!("{v:?}")),node("aggregate","arguments","",arguments(tcx,args.skip_binder())?))]),
        ty::FnPtr(types,header) => {
            let signature=types.with(header);
            let body=signature.skip_binder();
            node("type","function_pointer",&format!("{:?}",body.fn_sig_kind),vec![binder(signature.bound_vars().iter().map(|v|format!("{v:?}")),node("aggregate","signature","",body.inputs_and_output.iter().map(|t|type_tree(tcx,t)).collect::<Result<_,_>>()?))])
        },
        ty::UnsafeBinder(b) => node("type","unsafe_binder","",vec![binder(b.bound_vars().iter().map(|v|format!("{v:?}")),type_tree(tcx,b.skip_binder())?)]),
        ty::Dynamic(predicates,region) => {
            let mut children=predicates.iter().map(|p|predicate_tree(tcx,p)).collect::<Result<Vec<_>,_>>()?;
            children.push(region_tree(region)?);
            node("type","dynamic","",children)
        },
        ty::Closure(def,args) => node("type","closure",&format!("{def:?}"),arguments(tcx,args)?),
        ty::CoroutineClosure(def,args) => node("type","coroutine_closure",&format!("{def:?}"),arguments(tcx,args)?),
        ty::Coroutine(def,args) => node("type","coroutine",&format!("{def:?}"),arguments(tcx,args)?),
        ty::CoroutineWitness(def,args) => node("type","coroutine_witness",&format!("{def:?}"),arguments(tcx,args)?),
        other => return Err(format!("generic material type constructor not implemented: {other:?}")),
    })
}
