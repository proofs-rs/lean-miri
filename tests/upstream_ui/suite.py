"""Pinned upstream UI discovery and strict finite-result comparison.

Never infer success from a process exit status, nor update expectations from Lean.
The prepared reference uses Tree Borrows, precise interior mutability, no implicit
writes and default provenance. Unsupported profiles remain visible in inventory.
"""
from dataclasses import asdict, dataclass, field
from pathlib import Path
import re
import hashlib
import shlex

ROOT = Path(__file__).resolve().parents[2]
SOURCES = ROOT / 'upstream/miri-source/tests'
TARGET = 'x86_64-unknown-linux-gnu'
DIRECTIVE = re.compile(r'^\s*//@\s*(?:\[([^]]+)\])?\s*([\w-]+)(?::\s*(.*))?$')
ANNOTATION = re.compile(r'//(?:\[([^]]+)\])?~(?:\[([^]]+)\])?([\^v|]*)\s*ERROR:\s*(.*)')


RUNTIME_FLAGS = {
    '-Zmiri-tree-borrows', '-Zmiri-disable-stacked-borrows',
    '-Zmiri-tree-borrows-implicit-writes', '-Zmiri-tree-borrows-no-precise-interior-mut',
    '-Zmiri-disable-validation', '-Zmiri-recursive-validation',
    '-Zmiri-disable-alignment-check', '-Zmiri-symbolic-alignment-check',
    '-Zmiri-strict-provenance', '-Zmiri-permissive-provenance',
    '-Zmiri-ignore-leaks', '-Zmiri-fixed-schedule',
    '-Zmiri-disable-data-race-detector', '-Zmiri-deterministic-concurrency',
}


def runtime_profile(flags):
    """Expected independently recorded reference configuration, in flag order."""
    profile = {
        'borrow_tracker': 'tree_borrows',
        'tree_borrows': {'precise_interior_mut': True, 'implicit_writes': False},
        'environment_policy': 'empty', 'num_cpus': 1, 'rng_seed': 0, 'validation': 'Shallow',
        'alignment_check': 'Int', 'provenance_mode': 'Default',
        'data_race_detector': True, 'weak_memory_emulation': True,
        'ignore_leaks': False, 'genmc': False, 'native_libraries': 0,
        'short_fd_operations': True, 'float_nondeterminism': True,
        'cmpxchg_weak_failure_rate': 0.8, 'fixed_scheduling': False,
        'address_reuse_cross_thread_rate': 0.1, 'collect_leak_backtraces': True,
    }
    for flag in flags:
        if flag not in RUNTIME_FLAGS:
            raise ValueError('unsupported runtime setting: ' + flag)
        if flag == '-Zmiri-tree-borrows':
            profile.update(borrow_tracker='tree_borrows', tree_borrows={
                'precise_interior_mut': True, 'implicit_writes': False})
        elif flag == '-Zmiri-disable-stacked-borrows':
            profile.update(borrow_tracker='none', tree_borrows=None)
        elif flag in ('-Zmiri-tree-borrows-implicit-writes', '-Zmiri-tree-borrows-no-precise-interior-mut'):
            if profile['borrow_tracker'] != 'tree_borrows':
                raise ValueError(flag + ' requires Tree Borrows')
            profile['tree_borrows']['implicit_writes' if flag.endswith('implicit-writes') else 'precise_interior_mut'] = flag.endswith('implicit-writes')
        elif flag == '-Zmiri-disable-validation': profile['validation'] = 'No'
        elif flag == '-Zmiri-recursive-validation': profile['validation'] = 'Deep'
        elif flag == '-Zmiri-disable-alignment-check': profile['alignment_check'] = 'None'
        elif flag == '-Zmiri-symbolic-alignment-check': profile['alignment_check'] = 'Symbolic'
        elif flag == '-Zmiri-strict-provenance': profile['provenance_mode'] = 'Strict'
        elif flag == '-Zmiri-permissive-provenance': profile['provenance_mode'] = 'Permissive'
        elif flag == '-Zmiri-ignore-leaks': profile.update(ignore_leaks=True, collect_leak_backtraces=False)
        elif flag == '-Zmiri-fixed-schedule': profile['fixed_scheduling'] = True
        elif flag == '-Zmiri-disable-data-race-detector': profile.update(data_race_detector=False, weak_memory_emulation=False)
        elif flag == '-Zmiri-deterministic-concurrency':
            profile.update(fixed_scheduling=True, address_reuse_cross_thread_rate=0.0,
                           cmpxchg_weak_failure_rate=0.0, weak_memory_emulation=False)
    return profile


@dataclass
class Case:
    path: str
    revision: str = ''
    edition: str = '2021'
    flags: list[str] = field(default_factory=list)
    runtime_flags: list[str] = field(default_factory=list)
    errors: list[tuple[int, str]] = field(default_factory=list)
    reasons: list[str] = field(default_factory=list)

    @property
    def id(self):
        return self.path + (f'@{self.revision}' if self.revision else '')

    @property
    def fail(self):
        return self.path.startswith('fail/')

    def record(self):
        return {'id': self.id, **asdict(self)}


def source_fingerprint():
    """Identity of project interpreter/producer/harness sources, not a proof."""
    paths = [*ROOT.joinpath('Miri').rglob('*.lean'),
             *ROOT.joinpath('exporter/src').rglob('*.rs'),
             *ROOT.joinpath('native').rglob('*.c'),
             ROOT / 'tools/NativeRunner.lean', ROOT / 'tools/check-upstream-ui.py',
             ROOT / 'tools/collect-upstream-ui.py',
             Path(__file__), ROOT / 'lakefile.lean', ROOT / 'lean-toolchain',
             ROOT / 'upstream/source-lock.json', ROOT / 'Miri.lean',
             ROOT / 'exporter/Cargo.toml', ROOT / 'exporter/Cargo.lock', ROOT / 'exporter/build.rs']
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(path.relative_to(ROOT).as_posix().encode() + b'\0')
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def applies(selector, revision):
    return selector is None or revision in selector.split(',')


def matches(pattern, text):
    if pattern.startswith('/') and pattern.endswith('/'):
        return re.search(pattern[1:-1], text) is not None
    return pattern in text


def discover(sources=SOURCES):
    """Enumerate every .rs in pass/fail, expanding all declared revisions."""
    for group in ('pass', 'fail'):
        for path in sorted((sources / group).rglob('*.rs')):
            lines = path.read_text().splitlines()
            directives = []
            for number, line in enumerate(lines, 1):
                match = DIRECTIVE.match(line)
                if match:
                    directives.append((number, *match.groups()))
                elif re.match(r'^\s*//@', line):
                    directives.append((number, None, 'unparsed-directive', line))
            revisions = [r for _, _, key, value in directives if key == 'revisions'
                         for r in (value or '').split()]
            for revision in revisions or ['']:
                case = Case(path.relative_to(sources).as_posix(), revision)
                # ui_test::Comments::for_revision emits base settings first,
                # then revision groups; source line order alone is incorrect.
                active = [(key, (value or '').split(' #', 1)[0].strip())
                          for _, selector, key, value in sorted(directives, key=lambda row: (row[1] is not None, tuple(row[1].split(',')) if row[1] else (), row[0]))
                          if applies(selector, revision)]
                for key, value in active:
                    if key == 'compile-flags':
                        case.flags.extend(shlex.split(value))
                    elif key == 'edition':
                        case.edition = value
                    elif key in ('only-target', 'ignore-target', 'ignore-host'):
                        hit = any(token in TARGET for token in value.split())
                        if (key == 'only-target' and not hit) or (key != 'only-target' and hit):
                            case.reasons.append(f'target condition: {key}: {value}')
                    elif key == 'ignore-bitwidth':
                        if '64' in value.split():
                            case.reasons.append('target condition: ignore-bitwidth 64')
                    elif key not in ('revisions', 'normalize-stderr-test', 'run-native'):
                        case.reasons.append(f'unsupported directive: {key}: {value}')
                # Miri flags configure its interpreter, never rustc. Only the
                # explicit flag exactly matching our shared profile is accepted.
                compiler_flags = []
                for flag in case.flags:
                    if flag in RUNTIME_FLAGS:
                        case.runtime_flags.append(flag)
                        continue
                    if flag.startswith('-Zmiri'):
                        case.reasons.append(f'unsupported runtime setting: {flag}')
                    else:
                        compiler_flags.append(flag)
                case.flags = compiler_flags
                try:
                    runtime_profile(case.runtime_flags)
                except ValueError as error:
                    case.reasons.append(str(error))
                if any(x.startswith('-Zmir-opt-level=') and x != '-Zmir-opt-level=0'
                       for x in case.flags):
                    case.reasons.append('exporter requires MIR opt level 0')
                if 'stacked_borrows' in path.parts or (revision in ('stack', 'stacked')):
                    case.reasons.append('Stacked Borrows specific expectation')
                previous = None
                for number, line in enumerate(lines, 1):
                    match = ANNOTATION.search(line)
                    if not match:
                        continue
                    marker, pattern = match[3], match[4].strip()
                    target = previous if marker == '|' else number - marker.count('^') + marker.count('v')
                    previous = target
                    if not applies(match[1] or match[2], revision):
                        continue
                    if target is None:
                        case.reasons.append('error continuation has no preceding location')
                    else:
                        case.errors.append((target, pattern))
                    previous = target
                stdout = path.with_suffix(f'.{revision}.stdout') if revision else path.with_suffix('.stdout')
                if not stdout.exists():
                    stdout = path.with_suffix('.stdout')
                if stdout.exists() and stdout.read_text().strip():
                    case.reasons.append('stdout snapshot requires guest-output capture')
                if case.fail and any('borrow stack' in pattern for _, pattern in case.errors):
                    case.reasons.append('Stacked Borrows specific error annotation')
                if case.fail:
                    stderr = path.with_suffix(f'.{revision}.stderr') if revision else path.with_suffix('.stderr')
                    if not stderr.exists():
                        stderr = path.with_suffix('.stderr')
                    if stderr.exists() and 'error: Undefined Behavior:' not in stderr.read_text():
                        case.reasons.append('upstream expectation is not a runtime UB diagnostic')
                    if not case.errors:
                        case.reasons.append('no local ERROR annotation for UB site oracle')
                case.reasons = sorted(set(case.reasons))
                yield case


# Each row maps independently specified upstream diagnostics and Lean diagnostics
# to one semantic error class. A missing mapping is an oracle gap, never a pass.
# Access direction is preserved for Tree Borrows; unrelated UB cannot substitute.
CATEGORIES = [
    ('invalid_bool', r'expected a boolean|not a valid bool|invalid 8-bit value as a bool', r'invalidBool|invalid boolean|valid bool representation'),
    ('invalid_char', r'valid unicode|valid Unicode|valid char|invalid 32-bit value as a char', r'invalidChar|invalid character|unicode'),
    ('uninitialized', r'uninitialized', r'invalidUninitBytes|ValidityFailure\.uninitialized|encountered uninitialized (?:memory|bytes)|uninitialized numeric array'),
    ('null_pointer', r'null pointer|null reference|null box', r'nullPointer|null pointer|null reference|DanglingIntPointer.*(?:addr(?:ess)? := 0|pointer 0)|dangling pointer 0|null or maybe-null safe pointer|DanglingIntPointer.*danglingIntegerPointer 0(?:[ ),}\]]|$)'),
    ('use_after_free', r'has been freed|use.after.free|deallocated', r'PointerUseAfterFree|useAfterFree|alreadyDead|alreadyDeallocated|deadAllocation|deallocated|use.after.free'),
    ('bounds', r'out.of.bounds|outside.*allocation|bytes? from the (?:end|beginning)|beyond.*bounds|in.bounds|at or beyond the end|before the beginning', r'outOfBounds|out.of.bounds|pointerOutOfBounds|PointerOutOfBounds|bounds'),
    ('alignment', r'alignment|aligned', r'misaligned|alignment|Misaligned'),
    ('tb_write', r'write access through .* is forbidden', r'Tree Borrows write access:.*(?:ChildAccessForbidden|ProtectedDisabled|NoValidExposedReferences)'),
    ('tb_read', r'read access through .* is forbidden', r'Tree Borrows read access:.*(?:ChildAccessForbidden|ProtectedDisabled|NoValidExposedReferences)'),
    ('tb_deallocate', r'deallocation through .* is forbidden', r'Tree Borrows deallocation:.*(?:ProtectedDealloc|AccessFailure)'),
    ('tb_reborrow', r'reborrow through .* is forbidden', r'Tree Borrows reborrow:.*(?:ChildAccessForbidden|ProtectedDisabled|NoValidExposedReferences)'),
    ('no_provenance', r'no provenance', r'DanglingIntPointer|dangling pointer|has no provenance'),
    ('assume', r'`assume` called with `false`', r'assume called with false'),
    ('float_to_int', r'`float_to_int_unchecked`.*cannot be represented', r'float_to_int_unchecked value cannot be represented'),
    ('different_allocations', r'not both derived from the same allocation', r'ptr_offset_from pointers do not share allocation'),
    ('track_caller', r'track_caller.*(?:declaration|function)', r'caller/callee.*track_caller.*mismatch'),
    ('calling_convention', r'calling convention', r'caller/callee calling convention mismatch'),
    ('extra_arguments', r'more arguments than it expected', r'more arguments than it expected'),
    ('missing_arguments', r'fewer arguments than', r'fewer arguments than'),
    ('vtable_trait', r'wrong trait in wide pointer vtable|using vtable for', r'InvalidVTableTrait'),
    ('nonzero', r'expected something greater or equal', r'validRange|valid range|outside.*range|out.of.range'),
    ('mixed_size_race', r'Race condition detected between.*differently.sized|Race condition detected between.*atomic', r'MixedSize|mixed.size|RaceCondition'),
    ('read_only', r'writing to .*read-only|mutable reference pointing to read-only|atomic.*read-only memory', r'WriteToReadOnly|readOnly|read.only'),
    ('argument_type', r'calling a function whose parameter', r'AbiMismatchArgument'),
    ('return_type', r'calling a function with return type', r'AbiMismatchReturn'),
    ('extern_mutability', r'extern static.*backing static is', r'extern static declaration and backing mutability disagree'),
    ('symbol_not_static', r'exported symbol.*not defined as a static', r'exported symbol.*not defined as a static'),
    ('symbol_not_function', r'exported symbol.*not defined as a function', r'exported symbol.*not defined as a function'),
    ('unwind', r'unwinding past a stack frame that does not allow', r'unwinding past a frame that does not allow'),
    ('variadic_fixed_count', r'C-variadic function with .* fixed arguments', r'CVariadicFixedCountMismatch'),
    ('variadic_signature', r'disagree on whether.*C-variadic|non-variadic function.*c-variadic', r'CVariadicMismatch|variadic.*(?:ABI|signature).*mismatch'),
    ('variadic_type', r'va_arg type mismatch', r'va_arg type mismatch|incompatible C variadic argument type'),
    ('variadic_exhausted', r'more C-variadic arguments read than were passed', r'not enough.*variadic|more.*variadic'),
    ('shim_argument_count', r'ABI mismatch: calling .* arguments', r'argument count|incorrect number of .*arguments?|expected [0-9]+ arguments?'),
    ('target_feature', r'(?:requires unavailable|requires missing) target feature', r'(?:missing|unavailable|required).*target feature|targetFeature'),
    ('allocation_size', r'creating an allocation larger than half', r'creating an allocation larger than half'),
    ('deref_function', r'accessing .* contains a function', r'DerefFunctionPointer'),
    ('nonzero_intrinsic', r'`ct(?:l|t)z_nonzero` called on 0', r'nonzero count intrinsic called on zero'),
    ('exact_division', r'exact_div:.*without remainder', r'exact_div has nonzero remainder'),
    ('fast_float', r'fast` intrinsic.*non-finite', r'fast float intrinsic.*non-finite'),
    ('negative_offset_from', r'ptr_offset_from_unsigned.*smaller address', r'ptr_offset_from_unsigned has negative distance'),
    ('never', r'value of the never type|value of uninhabited type|zero-variant enum|pointing to uninhabited type|uninhabited enum variant', r'never value|uninhabited'),
    ('invalid_vtable', r'expected a vtable pointer', r'InvalidVTablePointer|vtable pointer'),
    ('backtrace_layout', r'miri_resolve_frame.*struct with 5 fields', r'miri_resolve_frame.*struct with 5 fields'),
    ('dead_local', r'accessing a dead local variable', r'localExpectedLive|dead local'),
    ('simd_mask', r'SIMD mask must be all-0-bits or all-1-bits', r'each SIMD mask element must be all-zero or all-one bits'),
    ('simd_float_to_int', r'`simd_cast`.*cannot be represented', r'simd_cast value cannot be represented'),
    ('address_space_end', r'too close to the end of the address space', r'too close to address-space end'),
    ('metadata_size', r'invalid reference metadata:.*bigger than largest supported object', r'SizeTooBig|objectTooBig|sliceTooBig|invalid reference metadata|(?:slice|total size|dynamic layout).*(?:large|big|overflow)'),
    ('data_race', r'Data race', r'DataRace|data race'),
    ('division_zero', r'divis(?:ion|or).*zero|dividing by zero|remainder.*zero', r'divisionByZero|remainderByZero|division by zero|remainder.*zero'),
    ('overflow', r'overflow', r'overflow|Overflow'),
    ('invalid_discriminant', r'discriminant|enum tag|enum value has invalid tag', r'discriminant|Discriminant|enumTag'),
    ('invalid_function', r'function pointer|not pointing to a function', r'functionPointer|function pointer|FunctionPointer'),
    ('unreachable', r'entering unreachable code|unreachable_unchecked', r'unreachable|Unreachable'),
    ('overlap', r'overlap', r'overlap|Overlap'),
]


def category_reference(text):
    # The invalid-value diagnostic can also say 'expected a boolean/character'.
    # The uninitialized-memory cause takes precedence over that expected type.
    if re.search(r'\b(?:encountered uninitialized|uninitialized (?:memory|data|bytes|value)|memory is uninitialized)\b', text, re.I):
        return 'uninitialized'
    for name, reference, _ in CATEGORIES:
        if re.search(reference, text, re.I):
            return name
    return None


def category_lean(text, category):
    return any(name == category and re.search(lean, text, re.I)
               for name, _, lean in CATEGORIES)


def reference_oracle(case, sidecar, diagnostic):
    """Require a real same-TyCtxt reference and its original ERROR/site oracle."""
    ref = sidecar.get('reference', sidecar)
    config = ref.get('config', {})
    if config.get('same_tcx') is not True:
        return 'reference_profile_mismatch', None
    expected_profile = runtime_profile(case.runtime_flags)
    if any(config.get(key) != value for key, value in expected_profile.items()):
        return 'reference_profile_mismatch', None
    kind = ref.get('outcome', {}).get('kind')
    if not case.fail:
        return ('ready', None) if ref.get('status') == 'completed' and kind == 'exit_zero' else ('reference_mismatch', None)
    marker = 'error: Undefined Behavior:'
    if ref.get('status') != 'failed' or kind != 'miri_evaluation_error' or marker not in diagnostic:
        return 'reference_mismatch', None
    primary = marker + diagnostic.split(marker, 1)[1].split('\n\n', 1)[0]
    for line, pattern in case.errors:
        if not matches(pattern, primary):
            return 'reference_annotation_mismatch', None
        if not re.search(re.escape(case.path) + ':' + str(line) + r':\d+', diagnostic):
            return 'reference_site_mismatch', None
    category = category_reference(primary.splitlines()[0])
    return ('ready', category) if category else ('oracle_unsupported', None)


def compare(case, terminal, category):
    if terminal.get('kind') != ('ub' if case.fail else 'exit'):
        return 'lean_' + terminal.get('kind', 'missing_outcome')
    if not case.fail:
        return 'passed' if terminal.get('detail') == '0' else 'lean_nonzero_exit'
    if not category or not category_lean(terminal.get('detail', ''), category):
        return 'ub_kind_mismatch'
    frames = terminal.get('frames', [])
    for line, _ in case.errors:
        if not any(f and case.path in f.get('file', '') and f.get('line') == line
                   for f in frames):
            return 'ub_site_mismatch'
    return 'passed'
