#!/usr/bin/env python3
"""Extract the actual pinned FieldsShape::count/offset bodies and compare them."""
import pathlib, subprocess, tempfile, hashlib, json
root = pathlib.Path(__file__).resolve().parents[2]

lock = json.loads((root/'upstream/source-lock.json').read_text())
locked = {entry['path']:entry['sha256'] for entry in lock['files']}
def read_pinned(relative):
    data = (root/relative).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    assert relative in locked, f"source absent from source-lock: {relative}"
    assert actual == locked[relative], f"pinned source hash mismatch: {relative}"
    return data.decode()
source = read_pinned('upstream/rustc-source/compiler/rustc_abi/src/lib.rs')

def method(signature):
    start = source.index(signature, source.index('impl<FieldIdx: Idx> FieldsShape'))
    brace = source.index('{', start)
    depth = 1
    end = brace + 1
    while depth:
        depth += (source[end] == '{') - (source[end] == '}')
        end += 1
    return source[start:end].replace('offsets[FieldIdx::new(i)]', 'offsets[i]')

rust = '''
#[derive(Clone,Copy)] struct Size(u64);
impl Size { const ZERO:Self=Self(0); }
impl std::ops::Mul<u64> for Size {type Output=Self;fn mul(self,n:u64)->Self {Self(self.0.checked_mul(n).unwrap())}}
enum FieldsShape { Primitive, Union(std::num::NonZeroUsize), Array{stride:Size,count:u64}, Arbitrary{offsets:Vec<Size>} }
impl FieldsShape {
''' + method('pub fn count(&self)') + '\n' + method('pub fn offset(&self') + '''
}
fn main(){
println!("primitive_count={}",FieldsShape::Primitive.count());
let shapes=[FieldsShape::Union(std::num::NonZeroUsize::new(3).unwrap()),FieldsShape::Array{stride:Size(4),count:3},FieldsShape::Arbitrary{offsets:vec![Size(8),Size(0),Size(4)]}];
for i in 0..3 {for (name,s) in ["union","array","arbitrary"].iter().zip(shapes.iter()) {println!("{name}_{i}={}",s.offset(i).0);}}
}
'''
with tempfile.TemporaryDirectory() as tmp:
    path = pathlib.Path(tmp)
    (path/'main.rs').write_text(rust)
    subprocess.run([str(root/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'--edition=2021',str(path/'main.rs'),'-o',str(path/'reference')],check=True)
    expected = subprocess.check_output([str(path/'reference')],text=True)
    import os
    env = dict(os.environ, ELAN_HOME=str(root/'.elan'))
    actual = subprocess.check_output([str(root/'.elan/bin/lake'),'env','lean','--run','tests/layout/Layout.lean'],cwd=root,env=env,text=True)
    assert actual == expected, (expected,actual)
    print(f'FieldsShape source-extracted differential passed ({len(actual.splitlines())} cases)')
