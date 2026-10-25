"""Actual scheduler environment-service prefix; not full scheduling equivalence."""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile,unittest
ROOT=Path(__file__).resolve().parents[2]
PATH='upstream/miri-source/src/concurrency/scheduler.rs'
class SchedulingPrefix(unittest.TestCase):
    def test_extracted_environment_service_prefix(self):
        raw=(ROOT/PATH).read_bytes()
        locked=next(x for x in json.loads((ROOT/'upstream/source-lock.json').read_text())['files'] if x['path']==PATH)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),locked['sha256'])
        source=raw.decode()
        start=source.index('        DelayedReadinessUpdates::process(this)?;')
        end=source.index('        let thread_manager =',start)
        prefix=source[start:end]
        harness=r'''
use std::time::Duration;
struct Machine{communicate:bool}
impl Machine{fn communicate(&self)->bool{self.communicate}}
struct Cx{machine:Machine,events:Vec<u8>,fail:u8}
struct DelayedReadinessUpdates;
impl DelayedReadinessUpdates{fn process(cx:&mut Cx)->Result<(),String>{cx.events.push(1);cx.machine.communicate=true;if cx.fail==1{Err("readiness".into())}else{Ok(())}}}
impl Cx{
fn poll_and_unblock(&mut self,d:Option<Duration>)->Result<(),String>{assert_eq!(d,Some(Duration::ZERO));self.events.push(2);if self.fail==2{Err("poll".into())}else{Ok(())}}
fn unblock_expired_deadlines(&mut self)->Result<Option<Duration>,String>{self.events.push(3);if self.fail==3{Err("deadline".into())}else{Ok(Some(Duration::from_nanos(10)))}}
fn prefix(&mut self)->Result<Option<Duration>,String>{let this=self;
PREFIX
Ok(potential_sleep_time)
}}
fn main(){for fail in 0..4{let mut cx=Cx{machine:Machine{communicate:false},events:vec![],fail};let result=cx.prefix();println!("{:?}|{:?}|{}",result,cx.events,cx.machine.communicate);}}
'''.replace('PREFIX',prefix)
        with tempfile.TemporaryDirectory() as tmp:
            src,exe=Path(tmp)/'prefix.rs',Path(tmp)/'prefix';src.write_text(harness)
            subprocess.run([str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'--edition=2021',str(src),'-o',str(exe)],check=True)
            result=subprocess.check_output([str(exe)],text=True).splitlines()
        self.assertEqual(result,['Ok(Some(10ns))|[1, 2, 3]|true','Err("readiness")|[1]|true','Err("poll")|[1, 2]|true','Err("deadline")|[1, 2, 3]|true'])
        subprocess.run(['.elan/bin/lake','env','lean','MiriTests/Scheduling/Stateful.lean'],cwd=ROOT,env={**os.environ,'ELAN_HOME':str(ROOT/'.elan')},check=True)
if __name__=='__main__':unittest.main()
