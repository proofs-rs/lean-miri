//! Optional provenance only: never interns keys or issues compiler queries.
use super::*;

type Pair<'tcx> = (
    ty::Ty<'tcx>,
    &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
);

#[derive(Clone, PartialEq, Eq)]
pub(super) struct BodyOrigin {
    pub role: &'static str,
    pub def_id: rustc_hir::def_id::DefId,
    pub promoted: Option<u32>,
    pub phase: String,
}

#[derive(Clone, PartialEq, Eq)]
struct Origin<'tcx> {
    route: &'static str,
    body: Option<BodyOrigin>,
    parent: Option<Pair<'tcx>>,
    source_alloc_id: Option<u64>,
}

pub(super) struct Trace<'tcx> {
    path: Option<PathBuf>,
    pub body: Option<BodyOrigin>,
    origins: HashMap<Pair<'tcx>, Vec<Origin<'tcx>>>,
    upcasts: HashMap<(ty::Ty<'tcx>, ty::Ty<'tcx>), Vec<Option<BodyOrigin>>>,
    pub probe_allocations: HashSet<AllocId>,
}

impl Default for Trace<'_> {
    fn default() -> Self {
        Self {
            path: env::var_os("LEAN_MIRI_VTABLE_DIAGNOSTICS").map(PathBuf::from),
            body: None,
            origins: HashMap::new(),
            upcasts: HashMap::new(),
            probe_allocations: HashSet::new(),
        }
    }
}

impl<'tcx> Trace<'tcx> {
    pub fn enabled(&self) -> bool {
        self.path.is_some()
    }

    pub fn upcast_site(&mut self, source: ty::Ty<'tcx>, target: ty::Ty<'tcx>) {
        if !self.enabled() {
            return;
        }
        let bodies = self.upcasts.entry((source, target)).or_default();
        if !bodies.contains(&self.body) {
            bodies.push(self.body.clone());
        }
    }

    pub fn upcast_demand(
        &mut self,
        key: Pair<'tcx>,
        parent: Pair<'tcx>,
        source: ty::Ty<'tcx>,
        target: ty::Ty<'tcx>,
    ) {
        if !self.enabled() {
            return;
        }
        let bodies = self
            .upcasts
            .get(&(source, target))
            .cloned()
            .unwrap_or_default();
        let previous = self.body.clone();
        for body in bodies {
            self.body = body;
            self.record(key, "dynamic_upcast", Some(parent), None);
        }
        self.body = previous;
    }

    pub fn record(
        &mut self,
        key: Pair<'tcx>,
        route: &'static str,
        parent: Option<Pair<'tcx>>,
        source_alloc_id: Option<u64>,
    ) {
        if !self.enabled() {
            return;
        }
        let origin = Origin {
            route,
            body: self.body.clone(),
            parent,
            source_alloc_id,
        };
        let origins = self.origins.entry(key).or_default();
        if !origins.contains(&origin) {
            origins.push(origin);
        }
    }

    pub fn report(
        &self,
        context: &ExportContext<'tcx>,
        ids: &HashMap<(u64, Vec<u64>), u64>,
    ) -> Result<Option<(PathBuf, Value)>, String> {
        let Some(path) = &self.path else {
            return Ok(None);
        };
        let identity = |(ty, predicates): Pair<'tcx>| -> Result<(u64, Vec<u64>), String> {
            let type_id = *context
                .type_ids
                .get(&ty)
                .ok_or("diagnostic type key not closed")?;
            let predicates = predicates
                .iter()
                .map(|p| {
                    context
                        .predicate_ids
                        .get(&p)
                        .copied()
                        .ok_or_else(|| "diagnostic predicate key not closed".to_owned())
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok((type_id, predicates))
        };
        let mut rows = Vec::new();
        for (key, origins) in &self.origins {
            let key = identity(*key)?;
            let query_id = ids.get(&key).ok_or("diagnostic query key not closed")?;
            let mut records = Vec::new();
            for origin in origins {
                let parent = origin.parent.map(identity).transpose()?;
                let parent_id = parent
                    .as_ref()
                    .map(|key| {
                        ids.get(key)
                            .copied()
                            .ok_or("diagnostic parent query not closed")
                    })
                    .transpose()?;
                records.push(json!({"route":origin.route,
                    "body":origin.body.as_ref().map(|body| json!({"role":body.role,
                        "def_id":def_json(body.def_id),"promoted":body.promoted,"phase":body.phase})),
                    "parent_query_id":parent_id,"source_alloc_id":origin.source_alloc_id}));
            }
            records.sort_by_key(Value::to_string);
            rows.push(json!({"query_id":query_id,"input_type_id":key.0,
                "input_predicate_ids":key.1,"origins":records}));
        }
        rows.sort_by_key(|row| row["query_id"].as_u64());
        Ok(Some((
            path.clone(),
            json!({"schema":"lean-miri-vtable-origins-v1",
            "rustc_commit":EXPECTED_RUSTC_COMMIT,"queries":rows}),
        )))
    }
}

// Hash the exact compact serialization without retaining another input-sized buffer.
struct Fingerprint {
    hash: u64,
    length: u64,
}
impl Write for Fingerprint {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.length = self
            .length
            .checked_add(bytes.len() as u64)
            .ok_or_else(|| std::io::Error::other("diagnostic snapshot length overflow"))?;
        for byte in bytes {
            self.hash = (self.hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3);
        }
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub(super) fn write_report(
    report: Option<(PathBuf, Value)>,
    document: &Value,
) -> Result<(), String> {
    let Some((path, mut report)) = report else {
        return Ok(());
    };
    let mut fingerprint = Fingerprint {
        hash: 0xcbf29ce484222325,
        length: 0,
    };
    serde_json::to_writer(&mut fingerprint, document).map_err(|e| e.to_string())?;
    report["snapshot_fnv1a64"] = json!(format!("{:016x}", fingerprint.hash));
    report["snapshot_byte_length"] = json!(fingerprint.length);
    // Refuse to replace an earlier diagnostic run or an export input.
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|e| format!("cannot create vtable diagnostics {}: {e}", path.display()))?;
    serde_json::to_writer_pretty(&mut file, &report).map_err(|e| e.to_string())
}
