//! Exact virtual-instance candidate index. Only compiler rows collected for
//! that same abstract Instance may contribute query IDs to its dense slot.
use super::*;

fn table(
    instance_count: usize,
    virtuals: impl IntoIterator<Item = usize>,
    rows: &Value,
) -> Result<Value, String> {
    let mut slots = vec![None::<Vec<u64>>; instance_count];
    for id in virtuals {
        let slot = slots
            .get_mut(id)
            .ok_or("virtual instance ID outside the instance table")?;
        *slot = Some(Vec::new());
    }
    for row in rows
        .as_array()
        .ok_or("virtual compiler queries must be an array")?
    {
        let id = row
            .get("original_instance_id")
            .and_then(Value::as_u64)
            .ok_or("virtual query lacks original instance ID")? as usize;
        let ids = slots
            .get_mut(id)
            .and_then(Option::as_mut)
            .ok_or("virtual query refers to a non-virtual or absent instance")?;
        let query = row
            .pointer("/vtable_query/query_id")
            .and_then(Value::as_u64)
            .ok_or("virtual query lacks its reserved vtable query ID")?;
        ids.push(query);
    }
    let slots = slots
        .into_iter()
        .map(|slot| match slot {
            None => Value::Null,
            Some(mut ids) => {
                ids.sort_unstable();
                ids.dedup();
                json!(ids)
            }
        })
        .collect::<Vec<_>>();
    Ok(json!({"schema_version":1,"by_instance":slots}))
}
pub(super) fn export(context: &ExportContext<'_>, rows: &Value) -> Result<Value, String> {
    let virtuals = context.instance_ids.iter().filter_map(|(instance, id)| {
        matches!(instance.def, ty::InstanceKind::Virtual(..)).then_some(*id as usize)
    });
    table(context.next_instance_id as usize, virtuals, rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn dense_slots_distinguish_nonvirtual_empty_and_exact_candidates() {
        let result = table(
            4,
            [1, 3],
            &json!([
                {"original_instance_id":1,"vtable_query":{"query_id":7}},
                {"original_instance_id":1,"vtable_query":{"query_id":2}},
                {"original_instance_id":1,"vtable_query":{"query_id":7}}
            ]),
        )
        .unwrap();
        assert_eq!(result["by_instance"], json!([null, [2, 7], null, []]));
        assert!(table(
            2,
            [1],
            &json!([{"original_instance_id":0,"vtable_query":{"query_id":1}}])
        )
        .is_err());
        assert!(table(2, [1], &json!([{"original_instance_id":1}])).is_err());
        assert!(table(2, [2], &json!([])).is_err());
    }
    #[test]
    fn vtable_ids_are_reserved_once_before_the_final_catalog_exists() {
        let mut context = ExportContext::default();
        assert_eq!(context.reserve_vtable_query_id(8, &[2, 1]), 0);
        assert_eq!(context.reserve_vtable_query_id(3, &[]), 1);
        assert_eq!(context.reserve_vtable_query_id(8, &[2, 1]), 0);
        assert_eq!(context.reserve_vtable_query_id(8, &[1, 2]), 2);
    }
}
