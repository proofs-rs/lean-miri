#!/usr/bin/env python3
"""Extract all three local FrameState transitions unchanged from pinned source."""
import hashlib,json,pathlib,sys
root=pathlib.Path(__file__).resolve().parents[2]
path='upstream/miri-source/src/concurrency/data_race.rs'
raw=(root/path).read_bytes()
lock={x['path']:x for x in json.loads((root/'upstream/source-lock.json').read_text())['files']}
assert hashlib.sha256(raw).hexdigest()==lock[path]['sha256']
src=raw.decode()
def item(marker):
    start=src.index(marker)
    opening=src.index('{',start)
    depth=0
    for i in range(opening,len(src)):
        depth+=(src[i]=='{')-(src[i]=='}')
        if depth==0:return src[start:i+1]
prelude=r'''
use std::cell::{RefCell,RefMut}; use std::ops::IndexMut;
use std::collections::HashMap as FxHashMap;
mod mir {pub type Local=usize;}
#[derive(Clone,Copy,Debug,Default)] struct Span;
impl Span {fn is_dummy(&self)->bool{true}}
#[derive(Clone,Copy,Debug,Default)] struct VTimestamp {packed:u32,span:Span}
impl VTimestamp {const ZERO:Self=Self{packed:0,span:Span};fn set_read_type(&mut self,_:NaReadType){self.packed&=!1;}}
#[derive(Clone,Copy,Debug)] enum NaWriteType{Allocate,Write}
enum NaReadType{Read}
#[derive(Clone,Debug,Default)] struct VClock(Vec<VTimestamp>);
impl VClock {fn new_with_index(index:usize,time:VTimestamp)->Self{let mut v=vec![VTimestamp::ZERO;index+1];v[index]=time;Self(v)}}
impl std::ops::Index<usize> for VClock {type Output=VTimestamp;fn index(&self,i:usize)->&VTimestamp{&self.0[i]}}
impl std::ops::IndexMut<usize> for VClock {fn index_mut(&mut self,i:usize)->&mut VTimestamp{&mut self.0[i]}}
struct ThreadClocks {clock:VClock}
struct Global {detect:bool,clocks:RefCell<ThreadClocks>}
impl Global {fn race_detecting(&self)->bool{self.detect} fn active_thread_state_mut(&self,_:&())->(usize,RefMut<'_,ThreadClocks>){(0,self.clocks.borrow_mut())}}
struct Handler(Global);
impl Handler {fn as_vclocks_ref(&self)->Option<&Global>{Some(&self.0)}}
struct MiriMachine<'a>{data_race:Handler,threads:(),marker:std::marker::PhantomData<&'a ()>}
impl MiriMachine<'_>{fn current_user_relevant_span(&self)->Span{Span}}
#[derive(Clone)] struct MemoryCellClocks {write:(usize,VTimestamp),write_type:NaWriteType,read:VClock}
struct Ranges(Vec<MemoryCellClocks>);
impl Ranges {fn iter_mut_all(&mut self)->impl Iterator<Item=(usize,&mut MemoryCellClocks)>{self.0.iter_mut().enumerate()}}
struct VClockAlloc {alloc_ranges:RefCell<Ranges>}
fn machine(detect:bool,time:u32)->MiriMachine<'static>{MiriMachine{data_race:Handler(Global{detect,clocks:RefCell::new(ThreadClocks{clock:VClock::new_with_index(0,VTimestamp{packed:time*2,span:Span})})}),threads:(),marker:std::marker::PhantomData}}
fn kind(k:NaWriteType)->&'static str{match k{NaWriteType::Allocate=>"a",NaWriteType::Write=>"w"}}
fn print_local(label:&str,f:&FrameState){let map=f.local_clocks.borrow();if let Some(c)=map.get(&1){println!("{label} {} {} {} {}",map.len(),c.write.packed,kind(c.write_type),c.read.packed)}else{println!("{label} 0 0 a 0")}}
'''
pieces=[prelude,'#[derive(Debug,Default)]'+item('pub struct FrameState {'),'#[derive(Debug)]'+item('struct LocalClocks {'),item('impl Default for LocalClocks {'),item('impl FrameState {')]
main=r'''
fn main(){for detect in [false,true]{for live in [false,true]{
 let frame=FrameState::default();
 frame.local_read(1,&machine(detect,3));
 print_local(&format!("R {detect} {live}"),&frame);
 frame.local_write(1,live,&machine(detect,5));
 print_local(&format!("W {detect} {live}"),&frame);
 let mut allocation=VClockAlloc{alloc_ranges:RefCell::new(Ranges(vec![MemoryCellClocks{write:(0,VTimestamp{packed:18,span:Span}),write_type:NaWriteType::Allocate,read:VClock::default()};2]))};
 frame.local_moved_to_memory(1,&mut allocation,&machine(detect,9));
 let ranges=allocation.alloc_ranges.borrow();let cell=&ranges.0[0];let read=cell.read.0.get(0).copied().unwrap_or(VTimestamp::ZERO);
 println!("M {detect} {live} {} {} {} {}",frame.local_clocks.borrow().len(),cell.write.1.packed,kind(cell.write_type),read.packed);
}}}
'''
pathlib.Path(sys.argv[1]).write_text('\n'.join(pieces)+main)
