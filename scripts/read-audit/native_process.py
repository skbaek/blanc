"""Optional native-process measurement backend. No default capability or exemption.

Only exact reviewed ELF identities and immutable snapshot scripts are accepted.
Native content reads are out of scope. Unknown, incomplete or ambiguous evidence
is UNKNOWN; the returned subprocess result remains the original command's API.
"""
from __future__ import annotations
import ast, hashlib, json, os, re, signal, subprocess, time, uuid, threading
from pathlib import Path

class Unknown(Exception):
    pass

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def identity(path):
    p=Path(path); resolved=p.resolve(strict=True); st=resolved.stat()
    return {'path':str(p.absolute()),'realpath':str(resolved),'sha256':digest(resolved) if resolved.is_file() else None,
            'device':st.st_dev,'inode':st.st_ino,'size':st.st_size if resolved.is_file() else None}

def snapshot(paths, roles):
    """Explicit finite source/runtime closure supplied by reviewed boundary.

    roles maps exact binary paths to native/python. No basename inference; these roles come only from explicitly pinned capability data.
    ELF binaries outside this closure refuse, even if they appear harmless.
    """
    result={}
    for path in sorted(set(map(str,paths))|set(map(str,roles))):
        item=identity(path); data=Path(item['realpath']).read_bytes()
        item['role']=roles.get(path,'script')
        item['shebang']=data.split(b'\n',1)[0].decode('utf8','strict') if data.startswith(b'#!') else None
        if item['role'] in ('native','python') and not data.startswith(b'\x7fELF'):
            raise Unknown('reviewed executable is not ELF: '+path)
        if item['role']=='script' and item['shebang'] is None:
            # Source payloads may be non-executable; exec classification refuses them.
            item['role']='source'
        result[path]=item
    return result

def unchanged(before):
    for path,item in before.items():
        if identity(path)!={k:v for k,v in item.items() if k not in ('role','shebang')}:
            raise Unknown('source/runtime identity drift: '+path)

def quoted(value):
    try:
        result=ast.literal_eval('b'+value).decode('utf8','strict')
    except (ValueError,SyntaxError,UnicodeError) as error:
        raise Unknown('invalid collector string') from error
    if not isinstance(result,str): raise Unknown('non-string collector value')
    return result

# Exact supported emitted C string/argv grammar. Truncated strings/argv refuse.
Q=r'"(?:[^"\\]|\\.)*"'
EXEC=re.compile(r'^execve\(('+Q+r'), (\[(?:'+Q+r'(?:, '+Q+r')*)?\]), (?:0x[0-9a-f]+|NULL) /\* \d+ vars? \*/\) += (.*)$')
LINE=re.compile(r'^(\d+\.\d+) (.*)$')

def parse_trace(directory, manifest, cwd, root_command, collector_exit, directories):
    """Strictly parse one fresh -ff directory; match real Python S/E by PID.

    -ttt preserves cross-PID order for fork cwd inheritance. Threads/shared FS,
    pid namespaces, non-leader exec, execveat and fchdir are unsupported.
    Signals and nonzero child exits are ordinary outcomes, not missing coverage.
    """
    directory=Path(directory); files=sorted(directory.glob('trace.*'))
    if not files: raise Unknown('absent collector trace')
    events=[]; pids=set(); integrity={}
    for path in files:
        try: pid=int(path.name.split('.')[-1])
        except ValueError: raise Unknown('unrecognized trace filename')
        if pid in pids: raise Unknown('duplicate PID trace')
        pids.add(pid); raw=path.read_bytes();integrity[path.name]=hashlib.sha256(raw).hexdigest()
        if not raw or not raw.endswith(b'\n'): raise Unknown('empty/truncated trace')
        pending=None
        for line_no,line in enumerate(raw.decode('utf8','strict').splitlines(),1):
            m=LINE.fullmatch(line)
            if not m: raise Unknown('unframed collector line: '+line)
            stamp,body=m.groups()
            if '<unfinished ...>' in body:
                if pending is not None: raise Unknown('nested unfinished syscall')
                pending=(float(stamp),body.split('<unfinished ...>')[0],line_no)
                continue
            resumed=re.fullmatch(r'<\.\.\. (\w+) resumed>(.*)',body)
            if resumed:
                if pending is None or not pending[1].startswith(resumed[1]+'('): raise Unknown('unmatched resumed syscall')
                original,first,first_line=pending;pending=None
                events.append((original,pid,first_line,first+resumed[2]))
                continue
            if pending is not None and not body.startswith('--- '): raise Unknown('unfinished syscall not resumed')
            events.append((float(stamp),pid,line_no,body))
        if pending is not None: raise Unknown('truncated unfinished syscall')
    # PID uniqueness is a required bounded-capture condition; repeated lifecycle
    # or events after terminal are rejected rather than merged as PID reuse.
    states={};parents={};execs=[];failed=[]
    ordered=sorted(events)
    # The one trace root is the process absent from every successful fork edge.
    edges=[]
    for _,pid,_,body in ordered:
        if re.match(r'^(?:clone3?|fork|vfork)\(',body):
            match=re.search(r'\) += (\d+)$',body)
            if match: edges.append((pid,int(match[1])))
    children={c for _,c in edges}; roots=pids-children
    if len(roots)!=1: raise Unknown('ambiguous/missing trace root')
    root=roots.pop();states[root]={'cwd':str(Path(cwd).resolve()),'terminal':None,'execs':[],'inherited':None,'exit_request':None}
    def resolve(path,where):
        candidate=path if os.path.isabs(path) else os.path.join(where,path)
        item=manifest.get(candidate)
        if item is None:
            # Alias is accepted only by an already bound exact realpath.
            resolved=canonical(candidate,directories)
            matches=[v for v in manifest.values() if v['realpath']==resolved]
            if not matches: raise Unknown('unbound executable/source: '+candidate)
            item=matches[0]
        return item
    def image(path,where):
        chain=[];item=resolve(path,where)
        while item['role']=='script':
            if item['realpath'] in [v['realpath'] for v in chain]: raise Unknown('cyclic shebang')
            chain.append(item);first=item['shebang']
            if first in ('#!/usr/bin/env bash','#!/usr/bin/env python3'):
                # Kernel runs env; its next real successful exec must identify
                # the interpreter. We do not infer PATH or trust a basename.
                item=resolve('/usr/bin/env',where)
            elif re.fullmatch(r'#!/[^\s]+',first or ''):
                item=resolve(first[2:],where)
            else: raise Unknown('unsupported shebang chain: '+str(first))
        if item['role'] not in ('native','python'): raise Unknown('non-executable source')
        return item,chain
    for stamp,pid,line_no,body in ordered:
        if pid not in states: raise Unknown('child event precedes known creation or lost parent: '+str(pid))
        state=states[pid]
        if state['terminal'] is not None: raise Unknown('event after terminal/PID reuse')
        if re.match(r'^(?:clone3?|fork|vfork)\(',body):
            match=re.search(r'\) += (\d+)$',body)
            if match:
                child=int(match[1])
                if child in states or child not in pids: raise Unknown('duplicate/missing descendant trace')
                if any(flag in body for flag in ('CLONE_THREAD','CLONE_FS','CLONE_NEW','CLONE_UNTRACED','CLONE_PARENT')): raise Unknown('unsupported clone identity/sharing flags')
                inherited=state['execs'][-1]['role'] if state['execs'] else state['inherited']
                states[child]={'cwd':state['cwd'],'terminal':None,'execs':[],'inherited':inherited,'exit_request':None}
                parents[child]=pid
            elif not re.search(r'= -1 [A-Z0-9_]+ ',body): raise Unknown('unresolved creation result')
        elif body.startswith('execve('):
            match=EXEC.fullmatch(body)
            if not match: raise Unknown('unsupported/truncated exec grammar: '+body)
            path,argv,result=match.groups();path=quoted(path);argv=[quoted(m.group()) for m in re.finditer(Q,argv)]
            if result.startswith('-1 '):
                failed.append({'pid':pid,'path':path,'result':result});continue
            if result!='0': raise Unknown('unresolved exec result')
            item,chain=image(path,state['cwd'])
            event={'pid':pid,'generation':len(state['execs']),'path':path,'argv':argv,'cwd':state['cwd'],
                   'role':item['role'],'image':item['realpath'],'image_sha256':item['sha256'],
                   'shebang_chain':[v['realpath'] for v in chain],'stamp':stamp}
            state['execs'].append(event);execs.append(event)
        elif body.startswith('execveat('): raise Unknown('execveat unsupported; no identity guess')
        elif body.startswith('chdir('):
            match=re.fullmatch(r'chdir\(('+Q+r')\) += (.*)',body)
            if not match: raise Unknown('unresolved chdir')
            if match[2]=='0':
                dest=quoted(match[1]); destination=canonical(dest if os.path.isabs(dest) else os.path.join(state['cwd'],dest),directories)
                if destination not in {v['realpath'] for v in directories.values()}: raise Unknown('unbound cwd directory')
                state['cwd']=destination
            elif not match[2].startswith('-1 '): raise Unknown('unresolved chdir result')
        elif body.startswith('fchdir('): raise Unknown('fchdir unsupported')
        elif body.startswith('+++ exited with '):
            match=re.fullmatch(r'\+\+\+ exited with (\d+) \+\+\+',body)
            if not match: raise Unknown('invalid exit')
            state['terminal']=int(match[1])
            if state['exit_request'] is not None and state['terminal']!=(state['exit_request'] & 255):
                raise Unknown('exit syscall/terminal status mismatch')
        elif body.startswith('+++ killed by '):
            match=re.fullmatch(r'\+\+\+ killed by (SIG[A-Z0-9]+)(?: \(core dumped\))? \+\+\+',body)
            if not match or not hasattr(signal,match[1]): raise Unknown('invalid signal terminal')
            state['terminal']=-int(getattr(signal,match[1]))
        elif re.fullmatch(r'kill\(-?\d+, SIG[A-Z0-9]+\) += (?:0|-1 [A-Z0-9_]+ \(.*\))',body):
            pass  # signal delivery creates no descendant; terminal still required
        elif body.startswith('wait4('):
            status=r'(?:NULL|0x[0-9a-f]+|\[\{(?:WIFEXITED\(s\) && WEXITSTATUS\(s\) == \d+|WIFSIGNALED\(s\) && WTERMSIG\(s\) == SIG[A-Z0-9_]+(?: && WCOREDUMP\(s\))?|WIFSTOPPED\(s\) && WSTOPSIG\(s\) == SIG[A-Z0-9_]+|WIFCONTINUED\(s\))\}\])'
            flags=r'(?:0|(?:WNOHANG|WUNTRACED|WCONTINUED)(?:\|(?:WNOHANG|WUNTRACED|WCONTINUED))*)'
            outcome=r'(?:\d+|-1 [A-Z0-9_]+ \([^\n]*\))'
            if not re.fullmatch(r'wait4\(-?\d+, '+status+r', '+flags+r', NULL\) += '+outcome,body):
                raise Unknown('unsupported/malformed wait4 record')
        elif body.startswith('waitid('):
            raise Unknown('waitid grammar not supported')
        elif body.startswith(('exit(','exit_group(')):
            match=re.fullmatch(r'(?:exit|exit_group)\((-?\d+)\) += \?',body)
            if not match: raise Unknown('malformed exit syscall record')
            if state['exit_request'] is not None: raise Unknown('duplicate exit request')
            state['exit_request']=int(match[1])
        elif body.startswith('--- '):
            match=re.fullmatch(r'--- (SIG[A-Z0-9_]+) \{si_signo=\1(?:, [^{}\n]+)?\} ---',body)
            if not match or not hasattr(signal,match[1]): raise Unknown('unsupported/malformed signal record')
        else: raise Unknown('unsupported collector event: '+body)
    for pid,state in states.items():
        if state['terminal'] is None: raise Unknown('missing terminal lifecycle: '+str(pid))
        if not state['execs'] and state['inherited']=='python': raise Unknown('fork-only Python child lacks independent startup: '+str(pid))
        if any(e['role']=='python' for e in state['execs'][:-1]): raise Unknown('Python exec replacement without completion-generation proof')
    if not states[root]['execs'] or states[root]['execs'][0]['argv']!=list(root_command): raise Unknown('root handoff command mismatch')
    root_exit=states[root]['terminal']
    if collector_exit not in (root_exit,128-root_exit if root_exit<0 else root_exit): raise Unknown('collector/root exit mismatch')
    return {'root_pid':root,'processes':len(states),'execs':execs,'failed_execs':failed,
            'parents':{str(k):v for k,v in parents.items()},
            'trace_sha256':integrity,'terminals':{str(k):v['terminal'] for k,v in states.items()}}

PROTOCOL = 'native-shell-v1'
HERE = Path(__file__).resolve().parent
SOURCE_FILES = ('native_process.py', 'launcher.py', 'bootstrap.py', 'sitecustomize.py', 'launch.sh')


def canonical(path, directories):
    """Resolve captured directory aliases before '..'; never query deleted fixtures."""
    if not os.path.isabs(path):
        raise Unknown('absolute resolution required')
    current = Path('/')
    for component in Path(path).parts[1:]:
        if component == '..':
            current = current.parent
        elif component != '.':
            current = current / component
            if str(current) in directories:
                current = Path(directories[str(current)]['realpath'])
    return str(current)


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def write_json(path, value):
    # Capture directories are private/fresh and no writer other than this
    # adapter is admitted. Hashes bind evidence; they are not signatures.
    path = Path(path)
    data = json_bytes(value)
    with path.open('xb') as stream:
        if stream.write(data) != len(data):
            raise Unknown('short capture write')
    return hashlib.sha256(data).hexdigest()


def load_capability(path, expected_sha256):
    if not isinstance(expected_sha256, str) or not re.fullmatch('[0-9a-f]{64}', expected_sha256):
        raise Unknown('explicit capability digest required')
    raw = Path(path).read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise Unknown('capability origin digest mismatch')
    data = json.loads(raw)
    if data.get('schema') != PROTOCOL or data.get('backend') != 'linux-strace-6.19-pidfd':
        raise Unknown('unsupported native capability contract')
    if not sys_linux() or not hasattr(os, 'pidfd_open') or not hasattr(signal, 'pidfd_send_signal'):
        raise Unknown('native pidfd backend unavailable')
    command = data.get('invocation')
    if not isinstance(command, list) or len(command) != 4 or command[1] != '--library-path' or not all(isinstance(v, str) for v in command):
        raise Unknown('unsupported collector loader vector')
    if any(not os.path.isabs(command[i]) for i in (0, 2, 3)):
        raise Unknown('collector paths must be absolute')
    for section in ('tools', 'roles', 'boundaries', 'observer_sources'):
        if not isinstance(data.get(section), dict) or not data[section]:
            raise Unknown('missing explicit capability ' + section)
    for name in SOURCE_FILES:
        if data['observer_sources'].get(name) != digest(HERE / name):
            raise Unknown('observer/backend capability identity drift: ' + name)
    expected_tools = data['tools']
    if command[0] not in expected_tools or command[3] not in expected_tools:
        raise Unknown('unbound loader/collector')
    for given, expected in expected_tools.items():
        if not os.path.isabs(given) or digest(given) != expected:
            raise Unknown('backend file identity drift: ' + given)
    for given, role in data['roles'].items():
        if not os.path.isabs(given) or role.get('kind') not in ('native', 'python') or digest(given) != role.get('sha256') or str(Path(given).resolve()) != role.get('realpath'):
            raise Unknown('native/Python role identity drift: ' + given)
    return data


def sys_linux():
    import sys
    return sys.platform.startswith('linux')


def boundary_expected(capability, boundary):
    """Validate the actual bounded producer; no temporary-name exemption."""
    if not isinstance(boundary, dict) or set(boundary) != {'id', 'root'}:
        raise Unknown('invalid source-owned boundary request')
    spec = capability['boundaries'].get(boundary['id'])
    if not isinstance(spec, dict):
        raise Unknown('boundary not in pinned capability')
    root = Path(boundary['root']).resolve()
    expected = {}
    producers = {}
    if spec.get('kind') == 'drip-routing-v1':
        producer = Path(spec['producer'])
        if digest(producer) != spec['producer_sha256']:
            raise Unknown('DRIP fixture producer identity drift')
        producers[str(producer)] = identity(producer)
        tree = ast.parse(producer.read_text())
        cls = next(node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == 'DripGateCoordination')
        setup = next(node for node in cls.body if isinstance(node, ast.FunctionDef) and node.name == 'setUp')
        calls = [node for node in ast.walk(setup) if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id == 'self' and node.func.attr == 'command']
        if len(calls) != 2:
            raise Unknown('unsupported DRIP command generator shape')
        bodies = [ast.literal_eval(node.args[1]) for node in calls]
        if not all(isinstance(body, str) for body in bodies):
            raise Unknown('nonliteral DRIP stub body')
        # Generator code identity is pinned above. Derive actual bodies from
        # that source rather than accepting fixture-provided role assertions.
        for rel, body in zip(('bin/python3', 'creme/.semaphore/semaphore'), bodies):
            expected[str(root / rel)] = hashlib.sha256(('#!/usr/bin/env bash\nset -eu\n' + body).encode()).hexdigest()
        for name, item in spec['copied'].items():
            origin = Path(item['source'])
            if digest(origin) != item['sha256']:
                raise Unknown('copied fixture source drift: ' + name)
            producers[str(origin)] = identity(origin)
            expected[str(root / 'scripts' / name)] = item['sha256']
    elif spec.get('kind') == 'static-synthetic-v1':
        # Used only by the explicitly pinned disposable control capability.
        # No static-synthetic boundary is proposed in the adoption packet.
        if str(root) != spec['root']:
            raise Unknown('static fixture root mismatch')
        expected = dict(spec['files'])
    else:
        raise Unknown('unsupported boundary producer')
    return expected, producers, root


def boundary_manifest(capability, boundary, cwd):
    expected, producers, root = boundary_expected(capability, boundary)
    for path, expected_hash in expected.items():
        if digest(path) != expected_hash:
            raise Unknown('actual dynamic fixture source drift: ' + path)
    roles = {path: value['kind'] for path, value in capability['roles'].items()}
    manifest = snapshot(expected, roles)
    directories = {}
    for path in [Path(cwd), root, *(Path(p).parent for p in expected), *(Path(p).parent for p in roles)]:
        for directory in [path, *path.parents]:
            if directory.is_dir():
                directories[str(directory)] = identity(directory)
    return {'files': manifest, 'directories': directories, 'producers': producers,
            'expected_fixture_sha256': expected, 'boundary': boundary}


def pid_start(pid):
    text = Path('/proc') / str(pid) / 'stat'
    raw = text.read_text()
    return int(raw.rsplit(')', 1)[1].split()[19])


class OwnedRootMonitor:
    """Read only the owned collector's direct children; no host process scan."""
    def __init__(self, pid, start):
        self.pid, self.start = pid, start
        self.stop = threading.Event()
        self.observed = {}
        self.errors = []
        self.thread = threading.Thread(target=self.run, daemon=True)
        self.thread.start()

    def run(self):
        while not self.stop.is_set():
            try:
                if pid_start(self.pid) != self.start:
                    self.errors.append('owned collector lifetime changed')
                    return
                children = Path('/proc') / str(self.pid) / 'task' / str(self.pid) / 'children'
                for raw in children.read_text().split():
                    pid = int(raw)
                    try:
                        fields = (Path('/proc') / raw / 'stat').read_text().rsplit(')', 1)[1].split()
                    except FileNotFoundError:
                        continue  # cannot credit a disappeared/too-fast root
                    item = {'pid': pid, 'ppid': int(fields[1]), 'start': int(fields[19])}
                    if item['ppid'] != self.pid:
                        self.errors.append('owned root parent identity ambiguous')
                        return
                    before = self.observed.get(pid)
                    if before is not None and before != item:
                        self.errors.append('owned root PID lifetime changed')
                        return
                    self.observed[pid] = item
            except (FileNotFoundError, ProcessLookupError):
                return  # final caller still requires positive root evidence
            except (OSError, ValueError, IndexError) as error:
                self.errors.append(type(error).__name__ + ': ' + str(error))
                return
            self.stop.wait(.001)

    def close(self):
        self.stop.set()
        self.thread.join(timeout=1)
        if self.thread.is_alive():
            raise Unknown('owned root monitor did not stop')


def verify_snapshot(bundle):
    for key in ('files', 'directories', 'producers'):
        unchanged(bundle[key])


class ShellAdapter:
    def __init__(self, log, emit, transport):
        self.log, self.emit, self.transport = str(log), emit, transport

    def __call__(self, command, *, _read_audit_boundary=None, **kwargs):
        original = command
        nonce = uuid.uuid4().hex
        base = Path(self.log + '.native')
        capture = base / nonce
        base.mkdir(parents=True, exist_ok=True)
        capture.mkdir(mode=0o700)
        descriptor = Path(self.log + '.native-capability.json')
        started = {'schema': PROTOCOL, 'nonce': nonce, 'parent_pid': os.getpid(),
                   'parent_start': pid_start(os.getpid()), 'original': command,
                   'cwd': str(Path(kwargs.get('cwd') or os.getcwd()).resolve()),
                   'capture': str(capture), 'boundary': _read_audit_boundary}
        self.emit('H', json.dumps(started, sort_keys=True))
        proc = None
        pidfd = None
        monitor = None
        completion = {'schema': PROTOCOL, 'nonce': nonce, 'status': 'UNKNOWN'}
        try:
            if isinstance(command, (str, bytes)) or not isinstance(command, (tuple, list)) or not command or not all(isinstance(x, str) for x in command):
                raise Unknown('explicit string argv required')
            unsupported = set(kwargs) - {'env', 'cwd', 'capture_output', 'text', 'encoding', 'errors', 'check'}
            if unsupported or kwargs.get('capture_output') is not True:
                raise Unknown('unsupported native kwargs or uncaptured diagnostics')
            carried = json.loads(descriptor.read_text())
            cap_sha = carried['sha256']
            cap = load_capability(carried['origin'], cap_sha)
            if carried['data'] != cap:
                raise Unknown('capability sidecar differs from pinned origin')
            bundle = boundary_manifest(cap, _read_audit_boundary, started['cwd'])
            source_seal = write_json(capture / 'sources.json', bundle)
            tools = {path: identity(path) for path in cap['tools']}
            observer = {str(HERE / name): identity(HERE / name) for name in SOURCE_FILES}
            backend_seal = write_json(capture / 'authority.json', {'capability_sha256': cap_sha, 'tools': tools, 'observer': observer})
            env = dict(kwargs.get('env') if kwargs.get('env') is not None else os.environ)
            env_sha = hashlib.sha256(json.dumps(env, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            argv = [*cap['invocation'], '--kill-on-exit', '-ff', '-ttt', '-s', '65535', '-o', str(capture / 'trace'), '-e', 'trace=%process,chdir,fchdir', '--', *command]
            launch = {'schema': PROTOCOL, 'nonce': nonce, 'parent_pid': os.getpid(),
                      'command': argv, 'original': command, 'cwd': started['cwd'],
                      'environment_sha256': env_sha, 'capability_sha256': cap_sha,
                      'source_sha256': source_seal, 'authority_sha256': backend_seal}
            # J is emitted by the ordinary audit hook for this exact current-
            # thread Popen constructor; it is not synthesized by this adapter.
            self.transport.pending = {'nonce': nonce, 'command': tuple(argv), 'used': False}
            run_kwargs = dict(kwargs)
            check = run_kwargs.pop('check', False)
            run_kwargs.pop('capture_output')
            try:
                proc = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **run_kwargs)
            finally:
                self.transport.pending = None
            pidfd = os.pidfd_open(proc.pid)
            collector_start = pid_start(proc.pid)
            completion.update({'collector_pid': proc.pid, 'collector_start': collector_start})
            monitor = OwnedRootMonitor(proc.pid, collector_start)
            self.emit('I', json.dumps(launch | {'collector_pid': proc.pid, 'collector_start': collector_start}, sort_keys=True))
            stdout, stderr = proc.communicate()
            monitor.close()
            result = subprocess.CompletedProcess(original, proc.returncode, stdout, stderr)
            verify_snapshot(bundle)
            unchanged(tools); unchanged(observer)
            if digest(carried['origin']) != cap_sha:
                raise Unknown('capability origin changed during native execution')
            diagnostic = stderr.encode() if isinstance(stderr, str) else stderr
            if b'strace:' in diagnostic or b'/strace:' in diagnostic:
                raise Unknown('collector diagnostic; no coverage inferred')
            evidence = parse_trace(capture, bundle['files'], started['cwd'], list(command), result.returncode, bundle['directories'])
            root_identity = monitor.observed.get(evidence['root_pid'])
            if monitor.errors or root_identity is None:
                raise Unknown('native root has no unambiguous live owned-parent identity')
            evidence['root_identity'] = root_identity
            evidence.update({'schema': PROTOCOL, 'nonce': nonce, 'collector_pid': proc.pid,
                             'collector_start': collector_start, 'capability_sha256': cap_sha,
                             'source_sha256': source_seal, 'authority_sha256': backend_seal,
                             'command': argv, 'original': command, 'cwd': started['cwd'], 'exit': result.returncode})
            evidence_seal = write_json(capture / 'evidence.json', evidence)
            completion.update({'status': 'observed', 'evidence_sha256': evidence_seal,
                               'collector_pid': proc.pid, 'collector_start': collector_start,
                               'root_pid': evidence['root_pid'], 'root_identity': root_identity, 'exit': result.returncode})
            self.emit('K', json.dumps(completion, sort_keys=True))
            if check and result.returncode:
                raise subprocess.CalledProcessError(result.returncode, original, output=stdout, stderr=stderr)
            return result
        except subprocess.CalledProcessError:
            raise
        except BaseException as error:
            if proc is not None:
                # Never signal a numeric PID or host group. The owned pidfd
                # names this exact collector lifetime; EXITKILL closes its tree.
                if proc.poll() is None:
                    if pidfd is None:
                        pidfd = os.pidfd_open(proc.pid)
                    signal.pidfd_send_signal(pidfd, signal.SIGKILL)
                    proc.wait()
                completion['collector_pid'] = proc.pid
            completion['reason'] = type(error).__name__ + ': ' + str(error)
            self.emit('K', json.dumps(completion, sort_keys=True))
            self.emit('U', 'native shell observation unavailable: ' + completion['reason'])
            if not isinstance(error, Exception):
                raise
            if proc is None:
                # Preserve original ordinary behavior while refusing coverage;
                # this handoff's opaque U is never waived.
                return subprocess.run(original, **kwargs)
            if 'result' in locals():
                if kwargs.get('check') and result.returncode:
                    raise subprocess.CalledProcessError(result.returncode, original, output=result.stdout, stderr=result.stderr)
                return result
            raise
        finally:
            if monitor is not None:
                monitor.close()
            if pidfd is not None:
                os.close(pidfd)


def validate_records(records, trusted, starts, ends, log):
    """Add native obligations; never consume U or replace Python validation.

    `trusted` originates in the auditor's explicit command-line pinned input.
    Neither sidecars nor an evidence file can choose the accepted capability.
    """
    errors = set()
    accepted = []
    buckets = {kind: {} for kind in ('H', 'I', 'J', 'K')}
    for kind, item in records:
        try:
            if not isinstance(item, dict) or item.get('schema') != PROTOCOL:
                raise Unknown('invalid native protocol version/object')
            nonce = item.get('nonce')
            if not isinstance(nonce, str) or not re.fullmatch('[0-9a-f]{32}', nonce) or nonce in buckets[kind]:
                raise Unknown('duplicate/invalid native nonce')
            buckets[kind][nonce] = item
        except (Unknown, KeyError, TypeError, ValueError) as error:
            errors.add('invalid native receipt: ' + str(error))
    if not records:
        return errors, accepted
    if trusted is None:
        return errors | {'native observation has no explicitly pinned auditor capability'}, accepted
    try:
        capability = load_capability(trusted['origin'], trusted['sha256'])
        if capability != trusted['data']:
            raise Unknown('native capability differs from auditor startup binding')
        for bucket in buckets.values():
            if set(bucket) != set(buckets['H']):
                raise Unknown('native start/transport/owned-launch/completion nonces do not match')
    except (Unknown, KeyError, OSError, ValueError, TypeError) as error:
        return errors | {'unverified native protocol: ' + str(error)}, accepted
    for nonce, begin in buckets['H'].items():
        try:
            launch, transport, complete = (buckets[kind][nonce] for kind in ('I', 'J', 'K'))
            if complete.get('status') != 'observed':
                raise Unknown('native collector did not establish coverage')
            parent = begin['parent_pid']
            if type(parent) is not int or parent not in starts or parent not in ends:
                raise Unknown('native callback has no completed observed parent')
            if type(begin.get('parent_start')) is not int or starts[parent].get('process_start') != begin['parent_start']:
                raise Unknown('native callback parent lifetime mismatch')
            if launch.get('parent_pid') != parent or transport.get('parent_pid') != parent:
                raise Unknown('native parent association mismatch')
            if launch.get('capability_sha256') != trusted['sha256']:
                raise Unknown('native capture capability is not auditor-authorized')
            capture = Path(str(log) + '.native') / nonce
            if begin.get('capture') != str(capture):
                raise Unknown('native capture path/nonce mismatch')
            raw_sources = (capture / 'sources.json').read_bytes()
            raw_authority = (capture / 'authority.json').read_bytes()
            raw_evidence = (capture / 'evidence.json').read_bytes()
            for raw, expected in ((raw_sources, launch.get('source_sha256')), (raw_authority, launch.get('authority_sha256')), (raw_evidence, complete.get('evidence_sha256'))):
                if hashlib.sha256(raw).hexdigest() != expected:
                    raise Unknown('native immutable capture inventory hash mismatch')
            source, authority, evidence = map(json.loads, (raw_sources, raw_authority, raw_evidence))
            expected, producers, root = boundary_expected(capability, begin['boundary'])
            if source.get('expected_fixture_sha256') != expected or source.get('boundary') != begin['boundary'] or source.get('producers') != producers:
                raise Unknown('native dynamic source producer mismatch')
            wanted = set(expected) | set(capability['roles'])
            if set(source['files']) != wanted:
                raise Unknown('native source/role population mismatch')
            for name, item in source['files'].items():
                role = capability['roles'].get(name)
                if role:
                    if item['role'] != role['kind'] or item['sha256'] != role['sha256'] or item['realpath'] != role['realpath']:
                        raise Unknown('native capture tried to grant an unapproved role')
                elif item['sha256'] != expected[name] or item['role'] not in ('script', 'source'):
                    raise Unknown('native dynamic script identity mismatch')
            if authority.get('capability_sha256') != trusted['sha256'] or set(authority.get('tools', {})) != set(capability['tools']):
                raise Unknown('native backend authority population mismatch')
            for name, item in authority['tools'].items():
                if item != identity(name) or item['sha256'] != capability['tools'][name]:
                    raise Unknown('native backend authority drift')
            if set(authority.get('observer', {})) != {str(HERE / name) for name in SOURCE_FILES}:
                raise Unknown('native observer authority population mismatch')
            for name, item in authority['observer'].items():
                if item != identity(name) or item['sha256'] != capability['observer_sources'][Path(name).name]:
                    raise Unknown('native observer authority drift')
            if (launch.get('original') != begin.get('original') or launch.get('cwd') != begin.get('cwd')
                    or transport.get('cwd') != begin.get('cwd') or transport.get('environment_sha256') != launch.get('environment_sha256')):
                raise Unknown('native target command/cwd/environment association mismatch')
            command = [*capability['invocation'], '--kill-on-exit', '-ff', '-ttt', '-s', '65535', '-o', str(capture / 'trace'), '-e', 'trace=%process,chdir,fchdir', '--', *begin['original']]
            if launch.get('command') != command or transport.get('command') != command:
                raise Unknown('native collector transport command mismatch')
            for field in ('collector_pid', 'collector_start'):
                if type(launch.get(field)) is not int or launch[field] <= 0 or complete.get(field) != launch[field] or evidence.get(field) != launch[field]:
                    raise Unknown('native owned collector identity mismatch')
            if (evidence.get('schema') != PROTOCOL or evidence.get('nonce') != nonce
                    or evidence.get('source_sha256') != launch.get('source_sha256')
                    or evidence.get('authority_sha256') != launch.get('authority_sha256')
                    or evidence.get('capability_sha256') != trusted['sha256']
                    or evidence.get('command') != command or evidence.get('original') != begin['original']
                    or evidence.get('cwd') != begin['cwd'] or evidence.get('exit') != complete.get('exit')):
                raise Unknown('native capture launch/evidence association mismatch')
            # Reparse the immutable real logs using the captured directory
            # identities before fixture cleanup; no dead temporary path lookup.
            parsed = parse_trace(capture, source['files'], begin['cwd'], begin['original'], complete['exit'], source['directories'])
            for field, value in parsed.items():
                if evidence.get(field) != value:
                    raise Unknown('native parsed evidence differs: ' + field)
            if complete.get('root_pid') != parsed['root_pid']:
                raise Unknown('native root PID mismatch')
            root_identity = evidence.get('root_identity')
            if (not isinstance(root_identity, dict) or root_identity != complete.get('root_identity')
                    or root_identity.get('pid') != parsed['root_pid']
                    or root_identity.get('ppid') != launch['collector_pid']
                    or type(root_identity.get('start')) is not int or root_identity['start'] <= 0):
                raise Unknown('native root owned-parent/start identity mismatch')
            allowed_names = {'sources.json', 'authority.json', 'evidence.json', *parsed['trace_sha256']}
            if {p.name for p in capture.iterdir()} != allowed_names:
                raise Unknown('native capture inventory has extra/missing files')
            matches = []
            for event in parsed['execs']:
                if event['role'] != 'python':
                    continue
                pid = event['pid']
                receipt = starts.get(pid)
                ppid = parsed['parents'].get(str(pid), launch['collector_pid'])
                if receipt is None or pid not in ends or receipt.get('ppid') != ppid or receipt.get('orig_argv') != event['argv']:
                    raise Unknown('native Python exec has no matching completed observer generation')
                image = identity(receipt['executable'])
                if image['realpath'] != event['image'] or image['sha256'] != event['image_sha256']:
                    raise Unknown('native Python executable identity mismatch')
                matches.append({'pid': pid, 'generation': event['generation'], 'ppid': ppid})
            accepted.append({'nonce': nonce, 'root_pid': parsed['root_pid'], 'collector_pid': launch['collector_pid'],
                             'collector_start': launch['collector_start'], 'execs': parsed['execs'],
                             'python_generations': matches, 'trace_sha256': parsed['trace_sha256']})
        except (Unknown, KeyError, OSError, ValueError, TypeError, StopIteration) as error:
            errors.add('unverified native handoff ' + nonce + ': ' + str(error))
    return errors, accepted
