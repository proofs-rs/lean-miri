//! Optional provenance only: never interns keys or issues compiler queries.
use super::*;

#[derive(serde::Serialize)]
pub(super) struct Report {
    schema: &'static str,
    rustc_commit: &'static str,
    queries: Vec<Query>,
    #[serde(skip_serializing_if = "Option::is_none")]
    snapshot_fnv1a64: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    snapshot_byte_length: Option<u64>,
}
#[derive(serde::Serialize)]
struct Query {
    query_id: u64,
    input_type_id: u64,
    input_predicate_ids: Vec<u64>,
    origins: Vec<OriginRecord>,
}
#[derive(serde::Serialize)]
struct OriginRecord {
    body: Option<BodyRecord>,
    parent_query_id: Option<u64>,
    route: &'static str,
    source_alloc_id: Option<u64>,
}
#[derive(serde::Serialize)]
struct BodyRecord {
    def_id: Definition,
    phase: String,
    promoted: Option<u32>,
    role: &'static str,
}
#[derive(serde::Serialize)]
struct Definition {
    #[serde(rename = "crate")]
    krate: u32,
    index: u32,
}

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
}

impl Default for Trace<'_> {
    fn default() -> Self {
        Self {
            path: env::var_os("LEAN_MIRI_VTABLE_DIAGNOSTICS").map(PathBuf::from),
            body: None,
            origins: HashMap::new(),
            upcasts: HashMap::new(),
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
    ) -> Result<Option<(PathBuf, Report)>, String> {
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
                records.push(OriginRecord {
                    route: origin.route,
                    body: origin.body.as_ref().map(|body| BodyRecord {
                        role: body.role,
                        def_id: Definition {
                            krate: body.def_id.krate.as_u32(),
                            index: body.def_id.index.as_u32(),
                        },
                        promoted: body.promoted,
                        phase: body.phase.clone(),
                    }),
                    parent_query_id: parent_id,
                    source_alloc_id: origin.source_alloc_id,
                });
            }
            // Sorting the small diagnostic records preserves stable evidence order.
            let mut keyed = records
                .into_iter()
                .map(|record| {
                    serde_json::to_string(&record)
                        .map(|key| (key, record))
                        .map_err(|e| e.to_string())
                })
                .collect::<Result<Vec<_>, _>>()?;
            keyed.sort_by(|left, right| left.0.cmp(&right.0));
            rows.push(Query {
                query_id: *query_id,
                input_type_id: key.0,
                input_predicate_ids: key.1,
                origins: keyed.into_iter().map(|(_, record)| record).collect(),
            });
        }
        rows.sort_by_key(|row| row.query_id);
        Ok(Some((
            path.clone(),
            Report {
                schema: "lean-miri-vtable-origins-v1",
                rustc_commit: EXPECTED_RUSTC_COMMIT,
                queries: rows,
                snapshot_fnv1a64: None,
                snapshot_byte_length: None,
            },
        )))
    }
}

pub(super) fn write_report(
    report: Option<(PathBuf, Report)>,
    snapshot: &Path,
) -> Result<(), String> {
    let Some((path, mut report)) = report else {
        return Ok(());
    };
    // Read the committed bytes: serializer field order is not a hash contract.
    let mut file = fs::File::open(snapshot).map_err(|e| e.to_string())?;
    let mut hash = 0xcbf29ce484222325u64;
    let mut length = 0u64;
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = std::io::Read::read(&mut file, &mut buffer).map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        length = length
            .checked_add(count as u64)
            .ok_or("diagnostic snapshot length overflow")?;
        for byte in &buffer[..count] {
            hash = (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3);
        }
    }
    report.snapshot_fnv1a64 = Some(format!("{hash:016x}"));
    report.snapshot_byte_length = Some(length);
    // Refuse to replace an earlier diagnostic run or an export input.
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|e| format!("cannot create vtable diagnostics {}: {e}", path.display()))?;
    serde_json::to_writer_pretty(&mut file, &report).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absent_origin_evidence_stays_null_and_uncomputed_hash_is_omitted() {
        let report = Report {
            schema: "lean-miri-vtable-origins-v1",
            rustc_commit: "pinned",
            queries: vec![Query {
                query_id: 3,
                input_type_id: 7,
                input_predicate_ids: vec![],
                origins: vec![OriginRecord {
                    body: None,
                    parent_query_id: None,
                    route: "allocation",
                    source_alloc_id: None,
                }],
            }],
            snapshot_fnv1a64: None,
            snapshot_byte_length: None,
        };
        let serialized = serde_json::to_string(&report).unwrap();
        assert!(serialized.contains(
            r#""body":null,"parent_query_id":null,"route":"allocation","source_alloc_id":null"#
        ));
        assert!(!serialized.contains("snapshot_fnv1a64"));
        assert!(!serialized.contains("snapshot_byte_length"));
    }
}
