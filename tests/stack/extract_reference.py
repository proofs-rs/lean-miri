#!/usr/bin/env python3
"""Extract unchanged storage_dead and the storage_live replacement tail."""
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parents[2]
relative = 'upstream/rustc-source/compiler/rustc_const_eval/src/interpret/stack.rs'
raw = (root / relative).read_bytes()
lock = {x['path']: x for x in json.loads((root/'upstream/source-lock.json').read_text())['files']}
assert hashlib.sha256(raw).hexdigest() == lock[relative]['sha256']
src = raw.decode()
def body(marker):
    start = src.index('{', src.index(marker))
    depth = 0
    for i in range(start, len(src)):
        depth += (src[i] == '{') - (src[i] == '}')
        if depth == 0: return src[start+1:i]
dead = body('pub fn storage_dead(')
live = body('pub fn storage_live_dyn(')
live = live[live.index('        let old = mem::replace'):]
prelude = '''use std::mem;
macro_rules! trace { ($($t:tt)*) => {} }
fn interp_ok<T>(x:T)->Result<T,()> {Ok(x)}
mod mir { pub const RETURN_PLACE: usize = 0; }
#[derive(Clone,Copy,PartialEq)] enum LocalValue { Dead, Live(bool) }
struct Slot { value: LocalValue }
struct Frame { locals: Vec<Slot> }
struct Cx { frame: Frame, state: usize, fail: bool }
impl Cx {
fn frame_mut(&mut self) -> &mut Frame { &mut self.frame }
fn deallocate_local(&mut self, old: LocalValue) -> Result<(),()> {
 if old == LocalValue::Live(true) { self.state += 1; if self.fail { return Err(()); } } Ok(())
}
'''
main = '''}
fn main(){for index in 0..3 { for fail in [false,true] { for live in [false,true] {
 let old = match index {0=>LocalValue::Dead,1=>LocalValue::Live(false),_=>LocalValue::Live(true)};
 let mut cx = Cx { frame: Frame { locals: vec![Slot{value:LocalValue::Dead},Slot{value:old}]}, state:0, fail };
 let result = if live {cx.live(1)} else {cx.dead(1)};
 let expected = if live {LocalValue::Live(false)} else {LocalValue::Dead};
 println!("{} {} {} {} {} {} true",if live {"L"} else {"D"},index,fail,cx.state,result.is_ok(),cx.frame.locals[1].value==expected);
}}}}
'''
pathlib.Path(sys.argv[1]).write_text(prelude + 'fn dead(&mut self, local:usize)->Result<(),()>{'+dead+'}\nfn live(&mut self,local:usize)->Result<(),()>{ self.state += 10; let local_val = LocalValue::Live(false);'+live+'}\n'+main)
