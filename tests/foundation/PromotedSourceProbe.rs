#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_driver::{Callbacks, Compilation};
use rustc_middle::{mir, ty::{self, TyCtxt}};

fn quoted(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""), '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"), '\r' => out.push_str("\\r"), '\t' => out.push_str("\\t"),
            c if c < ' ' => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"'); out
}
struct Probe { result: Option<String> }
impl Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let requested = std::env::var("PROMOTED_SOURCE_OWNER").unwrap_or_else(|_|"std::rt::lang_start_internal".into());
        let mut owners = Vec::new();
        for def in tcx.hir_crate_items(()).definitions() {
            if tcx.def_path_str(def.to_def_id()) == requested { owners.push(def.to_def_id()); }
        }
        if owners.is_empty() {
            let start = tcx.lang_items().start_fn().expect("actual lang_start absent");
            let body = tcx.instance_mir(ty::InstanceKind::Item(start));
            for block in body.basic_blocks.iter() {
                if let mir::TerminatorKind::Call {func:mir::Operand::Constant(c),..} = &block.terminator().kind {
                    if let ty::FnDef(def,_) = *c.const_.ty().kind() {
                        if tcx.def_path_str(def) == requested { owners.push(def); }
                    }
                }
            }
        }
        owners.sort_by_key(|def|(def.krate.as_u32(),def.index.as_u32())); owners.dedup();
        assert_eq!(owners.len(),1,"source owner absent/ambiguous");
        let owner = owners[0];
        let promoted = tcx.promoted_mir(owner);
        let entries = promoted.iter_enumerated().map(|(index, body)| {
            assert_eq!(body.source.instance,ty::InstanceKind::Item(owner));
            assert_eq!(body.source.promoted,Some(index));
            let locals = body.local_decls.iter().map(|local|quoted(&local.ty.to_string())).collect::<Vec<_>>().join(",");
            let statements = body.basic_blocks.iter().map(|block| {
                format!("[{}]",block.statements.iter().map(|s|quoted(&format!("{:?}",s.kind))).collect::<Vec<_>>().join(","))
            }).collect::<Vec<_>>().join(",");
            let terminals = body.basic_blocks.iter().map(|block|quoted(&format!("{:?}",block.terminator().kind))).collect::<Vec<_>>().join(",");
            let required = body.required_consts.as_ref().map(|v|v.len().to_string()).unwrap_or_else(||"null".into());
            let spread = body.spread_arg.map(|v|v.as_u32().to_string()).unwrap_or_else(||"null".into());
            format!("{{\"index\":{},\"argument_count\":{},\"spread_argument\":{},\"required_count\":{},\"phase\":{},\"locals\":[{}],\"statements\":[{}],\"terminators\":[{}],\"raw_mir\":{}}}",
                index.as_u32(),body.arg_count,spread,required,quoted(&format!("{:?}",body.phase)),locals,statements,terminals,quoted(&format!("{body:#?}")))
        }).collect::<Vec<_>>().join(",");
        self.result = Some(format!("{{\"owner_crate\":{},\"owner_index\":{},\"owner_path\":{},\"count\":{},\"entries\":[{}]}}",owner.krate.as_u32(),owner.index.as_u32(),quoted(&tcx.def_path_str(owner)),promoted.len(),entries));
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args = std::env::args().collect::<Vec<_>>();
    let mut probe = Probe {result:None};
    let code = rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut probe));
    if code != std::process::ExitCode::SUCCESS {return code;}
    println!("{}",probe.result.expect("compiler source callback not reached"));
    std::process::ExitCode::SUCCESS
}
