#!/usr/bin/env python3
"""Compare all homogeneity results using actual extracted pinned Rust bodies."""
import os, pathlib, subprocess, tempfile, re, hashlib, json
root = pathlib.Path(__file__).resolve().parents[2]

lock = json.loads((root/'upstream/source-lock.json').read_text())
locked = {entry['path']:entry['sha256'] for entry in lock['files']}
def read_pinned(relative):
    data = (root/relative).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    assert relative in locked, f"source absent from source-lock: {relative}"
    assert actual == locked[relative], f"pinned source hash mismatch: {relative}"
    return data.decode()
source = read_pinned('upstream/rustc-source/compiler/rustc_const_eval/src/util/mod.rs')
def extract(name):
    start = source.index('pub fn '+name+'(')
    end = source.index('{', start)+1
    depth = 1
    while depth:
        depth += (source[end]=='{')-(source[end]=='}')
        end += 1
    return source[start:end]
binops = 'Add AddUnchecked AddWithOverflow Sub SubUnchecked SubWithOverflow Mul MulUnchecked MulWithOverflow Div Rem BitXor BitAnd BitOr Shl ShlUnchecked Shr ShrUnchecked Eq Lt Le Ne Ge Gt Cmp Offset'.split()
unops = ['Not','Neg','PtrMetadata']
rust = 'mod mir {#[derive(Clone,Copy)] pub enum BinOp {'+','.join(binops)+'} pub enum UnOp {'+','.join(unops)+'}}\n'
rust += '\n'.join(extract(name) for name in ['binop_left_homogeneous','binop_right_homogeneous','unop_homogeneous'])
rust += '\nfn main(){\n'
for op in binops:
    rust += f'println!("{{}},{{}}",binop_left_homogeneous(mir::BinOp::{op}),binop_right_homogeneous(mir::BinOp::{op}));\n'
for op in unops:
    rust += f'println!("{{}}",unop_homogeneous(mir::UnOp::{op}));\n'
rust += '}\n'
with tempfile.TemporaryDirectory() as temp:
    path = pathlib.Path(temp)
    (path/'main.rs').write_text(rust)
    subprocess.run([str(root/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'--edition=2021',str(path/'main.rs'),'-o',str(path/'reference')],check=True)
    expected = subprocess.check_output([str(path/'reference')],text=True)
    env = dict(os.environ,ELAN_HOME=str(root/'.elan'))
    actual = subprocess.check_output([str(root/'.elan/bin/lake'),'env','lean','--run','MiriTests/Rvalue/Homogeneity.lean'],cwd=root,env=env,text=True)
    assert actual == expected,(expected,actual)
print('All 55 pinned operator homogeneity classifications match')

step = read_pinned('upstream/rustc-source/compiler/rustc_const_eval/src/interpret/step.rs')
start = step.index('pub fn eval_rvalue_into_place(')
end = step.index('    /// Writes the aggregate', start)
body = step[start:end]
expected = ['ThreadLocalRef','Use','CopyForDeref','BinaryOp','UnaryOp','Aggregate','Repeat','Ref','Reborrow','RawPtr','Cast','Discriminant','WrapUnsafeBinder']
branches = re.findall(r'^            ([A-Z][A-Za-z]+)\(',body,re.M)
assert branches == expected, branches
lean = (root/'Miri/Interpreter/Rvalue.lean').read_text()
branches = re.findall(r'^  \| \.([A-Z][A-Za-z]+) ',lean,re.M)
assert branches == expected, branches
print('All 13 dispatcher branches match pinned source order')
