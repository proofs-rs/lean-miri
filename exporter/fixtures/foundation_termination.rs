pub fn bound<T: std::process::Termination>(value: T) -> T { value }
pub fn unit_report() -> std::process::ExitCode {
    <() as std::process::Termination>::report(())
}
fn main() {}
