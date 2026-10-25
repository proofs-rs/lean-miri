#!/usr/bin/env python3
"""Extract unchanged reborrow loop plus actual vector/race clock methods."""
import hashlib, importlib.util, json, pathlib, sys
root=pathlib.Path(__file__).resolve().parents[2]
lock={x['path']:x for x in json.loads((root/'upstream/source-lock.json').read_text())['files']}
p='upstream/miri-source/src/borrow_tracker/tree_borrows/mod.rs'
raw=(root/p).read_bytes()
assert hashlib.sha256(raw).hexdigest()==lock[p]['sha256']
src=raw.decode()
start=src.index('        for (perm_range, loc_state) in inside_perms.iter_all()')
end=src.index('        interp_ok(Some(new_prov))',start)+len('        interp_ok(Some(new_prov))')
loop=src[start:end]
spec=importlib.util.spec_from_file_location('clockextract',root/'tests/vector_clock/extract_reference.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
generated=module.extract(root/'upstream/miri-source/src/concurrency/vector_clock.rs',root/'tests/vector_clock/reference.rs.in',root/'upstream/miri-source/src/concurrency/data_race.rs')
def block_end(text,start):
    opening=text.index('{',start);depth=0
    for i in range(opening,len(text)):
        depth+=(text[i]=='{')-(text[i]=='}')
        if depth==0:return i+1
    raise ValueError('unclosed block')
a=generated.index('pub fn emit_data_race_cases()');b=block_end(generated,a)
generated=generated[:a]+generated[b:]
generated=generated[:generated.index('fn main()')]
generated=generated.replace('type Size = u64;',r'''
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)] struct Size(u64);
impl Size{fn from_bytes(x:u64)->Self{Self(x)} fn bytes(self)->u64{self.0}}
impl std::ops::Add for Size{type Output=Self;fn add(self,rhs:Self)->Self{Self(self.0+rhs.0)}}
impl std::fmt::Display for Size{fn fmt(&self,f:&mut std::fmt::Formatter<'_>)->std::fmt::Result{std::fmt::Display::fmt(&self.0,f)}}
''')
extra=r'''
use std::cell::RefCell;
use std::rc::Rc;
#[derive(Clone,Copy,PartialEq,Eq)] enum AccessKind{Read,Write}
mod diagnostics{use super::AccessKind;pub enum AccessCause{Reborrow(AccessKind)}}
#[derive(Clone,Copy)] struct AllocRange{start:Size,size:Size}
#[derive(Clone,Copy)] struct LocalState(AccessKind);impl LocalState{fn permission(&self)->Self{*self}fn associated_access(&self)->Option<AccessKind>{Some(self.0)}}
struct Inside(bool);impl Inside{fn iter_all(&self)->impl Iterator<Item=(std::ops::Range<u64>,LocalState)>{if self.0{vec![(0..2,LocalState(AccessKind::Write))]}else{vec![(0..1,LocalState(AccessKind::Read)),(1..2,LocalState(AccessKind::Read))]}.into_iter()}}
struct Mutability(bool);impl Mutability{fn is_not(&self)->bool{self.0}}
struct Machine{borrow_tracker:Option<()>,trace:Rc<RefCell<Vec<String>>>}
impl Machine{fn current_user_relevant_span(&self)->Span{DUMMY_SP}}
struct Cx{machine:Machine,readonly:bool}impl Cx{fn get_alloc_mutability(&self,_:usize)->Option<Mutability>{Some(Mutability(self.readonly))}}
struct Tree{trace:Rc<RefCell<Vec<String>>>,inserted:bool}
impl Tree{
fn perform_access(&mut self,_:(),r:AllocRange,_:AccessKind,_:diagnostics::AccessCause,_:&(),_:usize,_:Span)->Result<(),&'static str>{self.trace.borrow_mut().push(format!("T{}",r.start.0));Ok(())}
fn new_child(&mut self,_:Size,_:(),_:usize,_:Inside,_:(),_:bool,_:Span)->Result<(),&'static str>{self.trace.borrow_mut().push("C".into());self.inserted=true;Ok(())}
}
struct Race{cells:RefCell<Vec<MemoryCellClocks>>,clocks:RefCell<ThreadClockSet>,trace:Rc<RefCell<Vec<String>>>}
impl Race{
fn read_non_atomic(&self,_:usize,r:AllocRange,read_type:NaReadType,_:Option<()>,_:&Machine)->Result<(),&'static str>{
 self.trace.borrow_mut().push(format!("R{}",r.start.0));
 let mut clocks=self.clocks.borrow_mut();let mut cells=self.cells.borrow_mut();
 for i in r.start.0..r.start.0+r.size.0{cells[i as usize].non_atomic_read_detect(&mut clocks,VectorIdx::from(0),read_type,DUMMY_SP).map_err(|_|"race")?;}
 Ok(())}
fn write_non_atomic(&self,_:usize,r:AllocRange,write_type:NaWriteType,_:Option<()>,_:&Machine)->Result<(),&'static str>{
 self.trace.borrow_mut().push(format!("W{}",r.start.0));
 let mut clocks=self.clocks.borrow_mut();let mut cells=self.cells.borrow_mut();
 for i in r.start.0..r.start.0+r.size.0{cells[i as usize].non_atomic_write_detect(&mut clocks,VectorIdx::from(0),write_type,DUMMY_SP).map_err(|_|"race")?;}
 Ok(())}
}
struct Handler(Race);impl Handler{fn as_vclocks_ref(&self)->Option<&Race>{Some(&self.0)}}
struct Extra{data_race:Handler}
struct Layout{ty:()}struct Place{layout:Layout}struct NewPerm{outside_perm:()}
fn interp_ok<T>(x:T)->Result<T,&'static str>{Ok(x)}
macro_rules! throw_ub{($($t:tt)*)=>{return Err("readonly")}}
fn run_loop(this:&Cx,tree_borrows:&mut Tree,alloc_extra:&Extra,write:bool)->Result<Option<()>,&'static str>{
let inside_perms=Inside(write);let alloc_id=1;let base_offset=Size::from_bytes(0);let parent_prov=();let new_tag=2;let protected=false;let new_perm=NewPerm{outside_perm:()};let new_prov=();let place=Place{layout:Layout{ty:()}};
LOOP
}
pub fn emit_retag_effects(){for write in [false,true]{for readonly in [false,true]{for racy in [false,true]{
let trace=Rc::new(RefCell::new(Vec::new()));let i0=VectorIdx::from(0);let i1=VectorIdx::from(1);
let old=make_timestamp(1,NaReadType::Read);let now=make_timestamp(3,NaReadType::Read);let late=make_timestamp(5,NaReadType::Read);
let cells=vec![MemoryCellClocks::new(old,i0),MemoryCellClocks::new(if racy{late}else{old},if racy{i1}else{i0})];
let mut clocks=ThreadClockSet::default();clocks.clock=VClock::new_with_index(i0,now);
let extra=Extra{data_race:Handler(Race{cells:RefCell::new(cells),clocks:RefCell::new(clocks),trace:trace.clone()})};
let this=Cx{machine:Machine{borrow_tracker:Some(()),trace:trace.clone()},readonly};let mut tree=Tree{trace:trace.clone(),inserted:false};
let result=run_loop(&this,&mut tree,&extra,write);
let cells=extra.data_race.0.cells.borrow();
println!("E {write} {readonly} {racy} {} {} {} {} {} {} {} {} {}",result.is_ok(),tree.inserted,
 cells[0].read[i0].time_and_read_type,cells[1].read[i0].time_and_read_type,
 cells[0].write.1.time_and_read_type,cells[1].write.1.time_and_read_type,
 matches!(cells[0].write_type,NaWriteType::Retag),matches!(cells[1].write_type,NaWriteType::Retag),trace.borrow().join(","));
}}}}
'''.replace('LOOP',loop)
closing=block_end(generated,generated.index('mod reference {'))-1
generated=generated[:closing]+extra+generated[closing:]
pathlib.Path(sys.argv[1]).write_text(generated+'\nfn main(){reference::emit_retag_effects()}\n')
