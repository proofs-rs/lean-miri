extern crate mio;
fn main() { match mio::Poll::new() { Ok(poll) => { println!("poll_created"); drop(poll); println!("poll_dropped"); }, Err(e) => { eprintln!("poll_error: {e}"); std::process::exit(1); } } }
