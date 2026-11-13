#!/usr/bin/env python3
"""Cargo rustc wrapper for a verified exact host-builder configuration."""
import json,os,sys
from pathlib import Path
from exporter_artifacts import verify_config
config_path=Path(os.environ['LEAN_MIRI_EXPORTER_HOST_CONFIG']);config=json.loads(config_path.read_text());verify_config(config)
args=sys.argv[1:];args+=['--sysroot',config['sysroot']]
if '--crate-name' in args and args[args.index('--crate-name')+1]=='lean_miri_mir_exporter':
    args+=['-Cprefer-dynamic','-L','dependency='+config['dependency'],*config['externs']]
    (config_path.parent/f'exporter-rustc-{os.getpid()}.json').write_text(json.dumps({'argv':[config['rustc'],*args],'artifact_hashes':config['artifact_hashes']},indent=2)+'\n')
env=dict(os.environ);env.update(config['environment'])
os.execve(config['rustc'],[config['rustc'],*args],env)
