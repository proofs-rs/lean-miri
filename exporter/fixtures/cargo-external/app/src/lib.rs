pub fn external_generic_call(value: u32) -> u32 {
    exporter_helper::wrap(value)
}

pub fn external_std_call(values: &Vec<u32>) -> usize {
    values.len()
}
