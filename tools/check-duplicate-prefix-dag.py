#!/usr/bin/env python3
"""Kernel-check a snapshot DAG; caches bind source, dependencies, inputs and artifacts.

--seed accepts only a fresh sequential-check output from the same source snapshot.
This explicit bootstrap trusts that run's compiler-success markers and log;
it is not a cryptographic generation-time attestation. Normal --reuse is hash-bound.
Ordinary reuse uses a manifest emitted by this driver. Logs live in scratch/.
--link-reused-artifacts shares only hash-bound successful-manifest artifacts,
which are immutable; fresh compiler outputs always have independent paths.
The default copies artifacts. Never modify a completed output in place.
"""
import argparse
import errno
import concurrent.futures as futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PIN = '046942e2e019ed73961f4232be907cd270bc214a89e7a49d3d1319592a83c397'
MIR = '444638d5f40f4e59df584939ed6479272ecea1ca9244de2f9e5152ab7f459f06'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def hashed(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()

def run(args, **kw):
    return subprocess.run(args, check=True, **kw)

def inputs():
    manifest = ROOT / 'examples/duplicate_prefix/SHA256SUMS'
    run(['sha256sum', '--check', str(manifest)], stdout=subprocess.DEVNULL)
    assert digest(ROOT / 'examples/duplicate_prefix/input.json') == MIR
    return {'manifest': digest(manifest), 'files': {
        line.split(maxsplit=1)[1].lstrip('*'): line.split()[0]
        for line in manifest.read_text().splitlines() if line.strip()}}

def external():
    library_manifest = ROOT / 'examples/duplicate_prefix/LIBRARY-SHA256SUMS'
    if digest(library_manifest) != PIN:
        raise RuntimeError('library manifest hash mismatch')
    run(['sha256sum', '--check', str(library_manifest)], stdout=subprocess.DEVNULL)
    paths = sorted((ROOT / 'Miri').rglob('*.lean'))
    paths += [ROOT / 'lakefile.lean', ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
    paths += sorted((ROOT / '.lake/build/lib/lean').rglob('*.olean'))
    toolchain = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    paths += [toolchain / 'bin/lean']
    paths += sorted((toolchain / 'lib/lean').rglob('*.olean'))
    return {str(p): digest(p) for p in paths}

def graph(source, roots):
    deps = {}
    def visit(name):
        if not re.fullmatch(r'[A-Za-z0-9_]+', name):
            raise ValueError('invalid module ' + name)
        if name in deps:
            return
        text = (source / (name + '.lean')).read_text()
        ds = re.findall(r'^import duplicate_prefix\.([A-Za-z0-9_]+)\s*$', text, re.M)
        deps[name] = ds
        for d in ds:
            visit(d)
    for root in roots:
        visit(root)
    return deps

def install_artifact(origin, target, expected, link=False):
    """Install an immutable cache artifact without overwriting any target."""
    if digest(origin) != expected:
        raise RuntimeError('reuse artifact hash mismatch: ' + str(origin))
    if link:
        try:
            os.link(origin, target)
        except OSError as error:
            if error.errno != errno.EXDEV:
                raise
            with origin.open('rb') as source, target.open('xb') as destination:
                shutil.copyfileobj(source, destination)
    else:
        with origin.open('rb') as source, target.open('xb') as destination:
            shutil.copyfileobj(source, destination)
    if digest(target) != expected or digest(origin) != expected:
        raise RuntimeError('artifact changed while installing ' + str(origin))

def load_reuse(directory):
    # A failed run has no manifest and is never eligible for reuse.
    return json.loads((directory / 'manifest.json').read_text())

def require_fresh_target(target):
    if target.exists() or target.is_symlink():
        raise FileExistsError('refusing to overwrite artifact: ' + str(target))

def parser():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('roots', nargs='*', default=['Check'])
    p.add_argument('--jobs', type=int, default=2)
    p.add_argument('--seed', type=Path)
    p.add_argument('--reuse', type=Path)
    p.add_argument('--link-reused-artifacts', action='store_true',
                   help='link immutable exact successful-manifest reuses; copy on EXDEV only')
    p.add_argument('--seed-log', type=Path, help='required fresh-run bootstrap compiler log')
    return p

def main():
    p = parser()
    a = p.parse_args()
    checker_sha256 = digest(Path(__file__))
    if not 1 <= a.jobs <= 4:
        p.error('--jobs must be 1..4 (each Lean uses -j1)')
    if a.seed and not a.seed_log:
        p.error('--seed requires --seed-log: explicit fresh-run bootstrap trust')
    if a.link_reused_artifacts and not a.reuse:
        p.error('--link-reused-artifacts requires a successful --reuse manifest')
    os.chdir(ROOT)
    os.environ['ELAN_HOME'] = os.environ.get('LEAN_MIRI_ELAN_HOME', str(ROOT / '.elan'))
    os.environ['PATH'] = os.environ['ELAN_HOME'] + '/bin:' + os.environ['PATH']
    os.environ['LEAN_NUM_THREADS'] = '1'
    run(['flock', '--no-fork', '/tmp/lean-miri-lake-build.lock', 'lake', 'build',
         'Miri.Frontend.ImportMIR'])
    start_inputs, start_external = inputs(), external()
    (ROOT / 'scratch').mkdir(exist_ok=True)
    out = Path(tempfile.mkdtemp(prefix='duplicate-prefix-dag.', dir=ROOT / 'scratch'))
    source = out / 'source/duplicate_prefix'
    shutil.copytree(ROOT / 'examples/duplicate_prefix', source)
    shutil.copyfile(source / 'SHA256SUMS', out / 'input-SHA256SUMS')
    artifacts = out / 'duplicate_prefix'
    artifacts.mkdir()
    deps = graph(source, a.roots or ['Check'])
    src = {n: digest(source / (n + '.lean')) for n in deps}
    context = hashed({'input': start_inputs, 'external': start_external, 'pin': PIN})
    (out / 'context.json').write_text(json.dumps({'input': start_inputs,
        'external': start_external, 'pin': PIN}, sort_keys=True, indent=2))
    env = os.environ.copy()
    base = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    env['LEAN_PATH'] = str(out) + ':' + base
    records, reused = {}, 0
    old = load_reuse(a.reuse) if a.reuse else {}
    if old and old['context'] != context:
        old = {}
    seed_deps = graph(a.seed / 'source/duplicate_prefix', [n for n in deps
        if (a.seed / 'source/duplicate_prefix' / (n + '.lean')).is_file()]) if a.seed else {}
    seed_ok = {}
    if a.seed:
        evidence = a.seed_log.read_text()
        if 'Source snapshot: ' + str(a.seed.resolve() / 'source/duplicate_prefix') not in evidence:
            raise RuntimeError('bootstrap log does not identify seed snapshot')
        (out / 'bootstrap-log.txt').write_text(evidence)
        (out / 'bootstrap.json').write_text(json.dumps({
            'seed': str(a.seed.resolve()), 'log_sha256': hashlib.sha256(evidence.encode()).hexdigest(),
            'trust': 'Fresh compiler run and .done success markers; no generation-time hash seal. '
                     'Current library/toolchain assumed unchanged since seed generation.'}, indent=2))
    def seed_valid(n):
        if n in seed_ok:
            return seed_ok[n]
        seed_ok[n] = False
        if (re.search(r'Kernel check [0-9]+/[0-9]+: ' + re.escape(n) + r'$', evidence, re.M) and
            seed_deps.get(n) == deps[n] and
            digest(a.seed / 'source/duplicate_prefix' / (n + '.lean')) == src[n] and
            (a.seed / 'duplicate_prefix' / (n + '.done')).is_file() and
            (a.seed / 'duplicate_prefix' / (n + '.olean')).is_file()):
            seed_ok[n] = all(seed_valid(d) for d in deps[n])
        return seed_ok[n]
    if a.seed and digest(a.seed / 'input-SHA256SUMS') != start_inputs['manifest']:
        raise RuntimeError('seed input manifest mismatch')
    def compile_node(n, binding):
        target = artifacts / (n + '.olean')
        require_fresh_target(target)
        origin = None
        manifest_origin = False
        rec = old.get('modules', {}).get(n)
        if rec and rec['binding'] == binding:
            candidate = a.reuse / 'duplicate_prefix' / (n + '.olean')
            if digest(candidate) == rec['artifact']:
                origin = candidate
                manifest_origin = True
        if (origin is None and a.seed and seed_valid(n) and all(
                digest(a.seed / 'duplicate_prefix' / (d + '.olean')) == records[d]['artifact']
                for d in deps[n])):
            origin = a.seed / 'duplicate_prefix' / (n + '.olean')
        if origin:
            expected = rec['artifact'] if manifest_origin else digest(origin)
            install_artifact(origin, target, expected,
                             link=a.link_reused_artifacts and manifest_origin)
        else:
            with (out / (n + '.log')).open('w') as log:
                run(['lean', '-j1', '--root=' + str(out / 'source'), '-o', str(target),
                     str(source / (n + '.lean'))], env=env, stdout=log, stderr=subprocess.STDOUT)
        return {'binding': binding, 'artifact': digest(target)}, bool(origin)
    print('DAG output: ' + str(out), flush=True)
    pending, active = set(deps), {}
    with futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        while pending or active:
            for n in sorted(pending):
                if len(active) >= a.jobs:
                    break
                if all(d in records for d in deps[n]):
                    binding = hashed({'context': context, 'source': src[n],
                        'dependencies': {d: records[d] for d in deps[n]}})
                    active[pool.submit(compile_node, n, binding)] = n
                    pending.remove(n)
            if not active:
                raise RuntimeError('cyclic module graph')
            done, _ = futures.wait(active, return_when=futures.FIRST_COMPLETED)
            for task in done:
                n = active.pop(task)
                records[n], was_reused = task.result()
                reused += was_reused
                print(f'{len(records)}/{len(deps)} {n} ' + ('reuse' if was_reused else 'fresh'), flush=True)
    audit = out / 'Audit.lean'
    audit.write_text('import Lean\n' + ''.join('import duplicate_prefix.' + n + '\n' for n in (a.roots or ['Check'])) + '''
open Lean Elab Command in
run_cmd do
  let mut theorems : Nat := 0
  let mut owned : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    let theoremDecl := match info with | .thmInfo _ => true | _ => false
    let own := (name.toString.splitOn "DuplicatePrefix.").length != 1
    if theoremDecl then theorems := theorems + 1
    if own then owned := owned + 1
    if theoremDecl || own then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"PASS: audited {theorems} imported theorems and {owned} owned declarations"
''')
    run(['lean', '-j1', str(audit)], env=env)
    if inputs() != start_inputs or external() != start_external:
        raise RuntimeError('input or library changed during check')
    if digest(Path(__file__)) != checker_sha256:
        raise RuntimeError('checker source changed during check')
    for n in deps:
        if digest(ROOT / 'examples/duplicate_prefix' / (n + '.lean')) != src[n]:
            raise RuntimeError('current source changed: ' + n)
        if digest(source / (n + '.lean')) != src[n]:
            raise RuntimeError('snapshot source changed: ' + n)
        if digest(artifacts / (n + '.olean')) != records[n]['artifact']:
            raise RuntimeError('artifact changed: ' + n)
    # Only a fully successful audited closure is promoted as a reusable manifest.
    (out / 'manifest.json').write_text(json.dumps({'context': context,
        'modules': records, 'roots': a.roots or ['Check'], 'reused': reused,
        'checker_sha256': checker_sha256,
        'reused_artifacts': 'immutable-links' if a.link_reused_artifacts else 'copies'}, sort_keys=True, indent=2))
    print(f'PASS: {len(records)} modules, {reused} exact reuses; selected kernel/axiom closure audited', flush=True)

if __name__ == '__main__':
    main()
