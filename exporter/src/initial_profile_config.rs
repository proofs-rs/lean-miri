//! Explicit feature/profile selection. Prepared and initial allocator worlds
//! are different contracts; neither is a fallback for the other.
use std::env;
#[derive(Debug)]
pub(super) struct Config { pub enabled:bool, pub selected_paths:Vec<String> }
impl Config {
    pub fn read(prepared_allocator_world:bool)->Result<Self,String> {
        let enabled=match env::var("LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT") {
            Ok(value) if value=="1"=>true,
            Ok(value) if value=="0"=>false,
            Ok(_)=>return Err("LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT must be exactly 0 or 1".into()),
            Err(env::VarError::NotPresent)=>false,
            Err(error)=>return Err(error.to_string()),
        };
        let single=env::var("LEAN_MIRI_INITIAL_QUERY_CACHE_ROOT").map(Some)
            .or_else(|e|if e==env::VarError::NotPresent{Ok(None)}else{Err(e)}).map_err(|e|e.to_string())?;
        let many=env::var("LEAN_MIRI_INITIAL_QUERY_CACHE_ROOTS_JSON").map(Some)
            .or_else(|e|if e==env::VarError::NotPresent{Ok(None)}else{Err(e)}).map_err(|e|e.to_string())?;
        if single.is_some() && many.is_some() {return Err("select one initial query-root environment syntax".into())}
        let mut selected_paths=if let Some(paths)=many {serde_json::from_str::<Vec<String>>(&paths).map_err(|e|format!("invalid selected query-root array: {e}"))?} else {single.into_iter().collect()};
        if selected_paths.iter().any(|p|p.is_empty()) {return Err("selected initial query root path is empty".into())}
        selected_paths.sort();
        if selected_paths.windows(2).any(|pair|pair[0]==pair[1]) {return Err("duplicate selected initial query root".into())}
        if !enabled && !selected_paths.is_empty() {return Err("selected query-cache roots require the complete initial profile".into())}
        if enabled && prepared_allocator_world {return Err("initial and prepared allocator profiles are mutually exclusive".into())}
        Ok(Self{enabled,selected_paths})
    }
}
