#!/usr/bin/env python3
"""The state of the collection, from the registry, the hubs' catalogs and the repositories on disk.

    python3 scripts/status.py check            # the registry and the catalogs, and every repository
                                               # in the workspace: versions against the train, the
                                               # libraries of the hubs above it that it requires,
                                               # module names that two repositories share, sources
                                               # formalized twice
    python3 scripts/status.py readme --write   # regenerate the tables of this README and of every
                                               # hub's README found in the workspace
    python3 scripts/status.py readme --check   # fail if one is out of date (--repo NAME: only that one)
    python3 scripts/status.py next             # the papers to start next, hub by hub

`check` exits with status 1 on errors: a bad registry or catalog, or a repository of a catalog, the
root or a hub that breaks the conventions (a module outside its root and its Palomar submissions, a
submission named as another repository's root or another paper, a module another repository has, off
the train, a library of a hub above it that it does not require).
Problems of the older repositories are warnings. `check` and `next` read the private overlay;
`readme` never does, since the READMEs are public.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

import collection as col

LEAN_PATHS = ['*.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']


# ---------------------------------------------------------------------------------------------
# Repositories on disk


def lake_config(repo: Path) -> dict | None:
    f = repo / 'lakefile.toml'
    return tomllib.loads(f.read_text()) if f.is_file() else None


def modules(repo: Path, conf: dict) -> tuple[dict[str, dict], set[str]]:
    """The module names of a Lake package, each with the `lean_lib` it is in: every `.lean` file
    under the root of each library; and the names that two source directories both provide."""
    src = repo / conf.get('srcDir', '.')
    found: dict[str, dict] = {}
    where: dict[str, Path] = {}
    twice: set[str] = set()

    def add(name: str, lib: dict, lib_src: Path) -> None:
        found.setdefault(name, lib)
        if where.setdefault(name, lib_src.resolve()) != lib_src.resolve():
            twice.add(name)

    for lib in conf.get('lean_lib', []):
        lib_src = src / lib.get('srcDir', '.')
        for pat in patterns(lib):
            base = re.sub(r'\.[+*]$', '', pat)
            rel = Path(*base.split('.'))
            if (lib_src / rel).with_suffix('.lean').is_file():
                add(base, lib, lib_src)
            if (lib_src / rel).is_dir():
                for dirpath, dirnames, filenames in os.walk(lib_src / rel):  # does not follow links
                    dirnames[:] = [d for d in dirnames if not d.startswith('.')]
                    for fn in filenames:
                        if fn.endswith('.lean'):
                            path = Path(dirpath, fn).relative_to(lib_src).with_suffix('')
                            add('.'.join(path.parts), lib, lib_src)
    return found, twice


def as_list(value) -> list[str]:
    """A Lake option that takes one string or an array of them."""
    return [value] if isinstance(value, str) else list(value or [])


def lib_roots(lib: dict) -> list[str]:
    return as_list(lib.get('roots')) or [lib.get('name', '')]


def patterns(lib: dict) -> list[str]:
    """A library's globs; by default, its roots (Lake's `LeanLibConfig`)."""
    return as_list(lib.get('globs')) or lib_roots(lib)


def glob_matches(glob: str, m: str) -> bool:
    """Whether a module name matches a Lake glob: `X.+` matches the submodules of X, `X.*` X and its
    submodules, and any other glob the module of that name."""
    if glob.endswith('.+'):
        return m.startswith(glob[:-1])
    if glob.endswith('.*'):
        return m == glob[:-2] or m.startswith(glob[:-1])
    return m == glob


def buildable(lib: dict, m: str) -> bool:
    """Whether a library's patterns match a module (Lake's `LeanLibConfig.isBuildableModule`): one
    of its globs, or one of its roots that a glob matches, as a prefix."""
    globs = patterns(lib)
    return any(glob_matches(g, m) for g in globs) or any(
        (m == r or m.startswith(r + '.')) and any(glob_matches(g, r) for g in globs) for r in lib_roots(lib))


def late_libraries(conf: dict, mods: dict[str, dict]) -> list[tuple[str, list[str]]]:
    """The libraries declared after a Palomar library whose patterns match one of its modules, each
    with those modules. Lake gives a module to the last library whose patterns match it, so the
    Palomar library must come after them (docs/CONVENTIONS.md, Section 3)."""
    libs = conf.get('lean_lib', [])
    found = []
    for i, lib in enumerate(libs):
        if not is_palomar(lib):
            continue
        own = [m for m, owner in mods.items() if owner is lib]
        for later in libs[i + 1:]:
            hit = sorted(m for m in own if buildable(later, m))
            if hit:
                found.append((later.get('name', '?'), hit))
    return found


def is_palomar(lib: dict) -> bool:
    """Whether a `lean_lib` is the Palomar library: the source directory `palomar/`."""
    return os.path.normpath(lib.get('srcDir', '.')) == 'palomar'


def submissions(mods: dict[str, dict]) -> tuple[dict[str, set[str]], set[str]]:
    """The Palomar submissions of a package (each name `<P>` with its modules `<P>.Challenge` and
    `<P>.Solution`), and the modules of its Palomar library that are neither."""
    subs: dict[str, set[str]] = {}
    other = set()
    for m, lib in mods.items():
        if not is_palomar(lib):
            continue
        parts = m.split('.')
        if len(parts) == 2 and parts[1] in ('Challenge', 'Solution'):
            subs.setdefault(parts[0], set()).add(m)
        else:
            other.add(m)
    return subs, other


def deprecated(repo: Path, m: str) -> bool:
    """Whether the module `m` of the package at `repo` is deprecated: its file, under the package's
    source directory, has a `deprecated_module` command."""
    conf = lake_config(repo) or {}
    f = (repo / conf.get('srcDir', '.') / Path(*m.split('.'))).with_suffix('.lean')
    return f.is_file() and any(line.startswith('deprecated_module') for line in f.read_text().splitlines())


def git(repo: Path, *args: str) -> tuple[int, str]:
    r = subprocess.run(['git', '-C', str(repo), *args], text=True, capture_output=True)
    return r.returncode, r.stdout.strip()


def scan(path: Path) -> dict | None:
    conf = lake_config(path)
    if conf is None:
        return None
    mods, twice = modules(path, conf)
    subs, other = submissions(mods)
    info = {'path': path, 'package': conf.get('name', '?'), 'modules': set(mods), 'twice': twice,
            'submissions': subs, 'palomar_other': other, 'late': late_libraries(conf, mods)}
    tc = path / 'lean-toolchain'
    info['toolchain'] = tc.read_text().strip() if tc.is_file() else ''
    pins = {}
    mf = path / 'lake-manifest.json'
    if mf.is_file():
        for e in json.loads(mf.read_text()).get('packages', []):
            pins[e['name']] = e.get('inputRev') if e['name'] == 'mathlib' else e.get('rev')
    info['pins'] = pins
    info['requires'] = {r.get('name') for r in conf.get('require', [])}
    info['head'] = git(path, 'rev-parse', 'HEAD')[1]
    info['dirty'] = bool(git(path, 'status', '--porcelain', '--untracked-files=no')[1])
    info['ahead'] = git(path, 'rev-list', '--count', '@{u}..HEAD')[1] or '-'
    return info


def check(c: col.Collection) -> int:
    errors = [f'catalog: {e}' for e in c.validate()]
    warnings: list[str] = []
    pins = c.train.get('pins', {})
    # The repositories to look at: the registry's, and those of the catalogs' papers, each with its
    # entries (several when its papers share it: formalize-math-paper, references/multi-paper.md).
    targets: dict[str, list[col.Paper]] = {r['name']: [] for r in c.repos if r.get('role') != 'tool'}
    for p in c.papers:
        targets.setdefault(p.repo, []).append(p)
    scanned: dict[str, dict] = {}
    for name, entries in targets.items():
        path = c.path(name)
        if not path.is_dir():
            if not entries or any(p.status == 'in-progress' or (p.status == 'formalized' and p.commit)
                                  for p in entries):
                warnings.append(f'{name}: not found at {path}')
            continue
        if path.resolve() != c.home(name).resolve():
            warnings.append(f'{name}: at {path.relative_to(col.WORKSPACE)}, its place is '
                            f'{c.home(name).relative_to(col.WORKSPACE)}: move it, and relink its private files')
        info = scan(path)
        if info is None:
            warnings.append(f'{name}: no lakefile.toml; not scanned')
            continue
        scanned[name] = info
        listed = c.repo(name)
        new = bool(entries) and (listed is None or listed.get('role') not in ('paper', 'background'))
        complain = errors.append if (new or (listed and listed.get('role') in ('root', 'hub', 'library'))) else warnings.append
        # Each entry's status is its own. A paper of a shared repository has joined it when its
        # directories exist; one that has not is still to do.
        root = entries[0].root if entries else ''
        joined = {p.id: len(entries) == 1
                  or any((path / d).is_dir() for d in (f'{p.root}/{p.paper}', f'palomar/{p.paper}'))
                  for p in entries}
        for p in entries:
            if p.status in ('todo', 'partial') and joined[p.id]:
                warnings.append(f'{name}: exists, but its catalog says {p.id} is {p.status}')
        if info['toolchain'] != c.train['lean']:
            complain(f'{name}: off the train: {info["toolchain"]} (train: {c.train["lean"]})')
        if 'mathlib' in info['pins'] and info['pins']['mathlib'] != c.train['mathlib']:
            complain(f'{name}: Mathlib {info["pins"]["mathlib"]} (train: {c.train["mathlib"]})')
        for pkg, rev in pins.items():
            have = info['pins'].get(pkg)
            if have and have != rev:
                complain(f'{name}: requires {pkg} at {have[:7]} (train: {rev[:7]})')
        # The libraries of the root and of the hubs above it (docs/CONVENTIONS.md, Section 1).
        if listed and listed.get('role') == 'root':
            need = []
        else:
            hub = (listed or {}).get('parent', '') if listed or not entries else entries[0].hub
            need = ['Phylogenetics'] + [h['package'] for h in c.hubs_above(hub)]
        missing = [pkg for pkg in need if pkg not in info['requires']]
        if missing:
            complain(f'{name}: does not require {", ".join(missing)}, the libraries of the root and of '
                     'the hubs above it (docs/CONVENTIONS.md, Section 1)')
        if listed and listed.get('lean') and not info['toolchain'].endswith(':' + listed['lean']):
            warnings.append(f'{name}: the registry says Lean {listed["lean"]}, the repository has {info["toolchain"]}')
        info['complain'] = complain
        if info['twice']:
            complain(f'{name}: modules that two source directories provide: '
                     + ', '.join(sorted(info['twice'])[:8]))
        for lib, hit in info['late']:
            complain(f'{name}: the library {lib} is declared after Palomar and its patterns match '
                     f'{", ".join(hit[:4])}: Lake gives them to it; declare Palomar last '
                     '(docs/CONVENTIONS.md, Section 3)')
        if new:
            # Every module is under the root, but the Palomar submissions <P>.Challenge and
            # <P>.Solution in palomar/, and, in the older layout, <Root>Challenge and <Root>Solution.
            allowed = {f'{root}Challenge', f'{root}Solution'} | set().union(*info['submissions'].values())
            outside = sorted(m for m in info['modules'] - info['palomar_other']
                             if m.split('.')[0] != root and m not in allowed)
            if outside:
                errors.append(f'{name}: modules outside the root {root}/: {", ".join(outside[:8])}')
            if info['palomar_other']:
                errors.append(f'{name}: modules of palomar/ that are not a Challenge or a Solution: '
                              + ', '.join(sorted(info['palomar_other'])[:8]))
            if info['package'] != root:
                errors.append(f'{name}: package {info["package"]!r}, catalog root {root!r}')
            for p in entries:
                started = p.status in ('in-progress', 'formalized') or joined[p.id]
                if info['submissions'] and started and p.paper not in info['submissions']:
                    warnings.append(f'{name}: palomar/ has no submission {p.paper}, the name of {p.id} '
                                    + ('(its `paper`)' if p.paper_given else '(its root)'))

    # Each library of the tree against the train's pin: commits that change no Lean file are fine.
    for r in c.library_repos():
        info = scanned.get(r['name'])
        rev = pins.get(r.get('package', ''))
        if not info or not rev:
            continue
        code, _ = git(info['path'], 'diff', '--quiet', rev, 'HEAD', '--', *LEAN_PATHS)
        if code != 0:
            warnings.append(f'{r["name"]}: its Lean files have changed since the train\'s pin {rev[:7]} '
                            '(move the train: docs/WORKFLOW.md, Section 7)')

    # The Palomar submissions: the root of their modules may be the repository's own root, but no
    # other repository's root or module root, and no other paper's name (`paper`).
    roots = {p.root: p.repo for p in c.papers}
    roots.update({r['package']: r['name'] for r in c.repos if r.get('package')})
    names = {p.paper: p.repo for p in c.papers if p.paper_given}
    for name, info in scanned.items():
        for sub in sorted(info['submissions']):
            if roots.get(sub, name) != name:
                info['complain'](f'{name}: its Palomar submission {sub} has the name of the root of {roots[sub]}')
            others = sorted(o for o, x in scanned.items()
                            if o != name and sub in {m.split('.')[0] for m in x['modules']})
            if others:
                info['complain'](f'{name}: its Palomar submission {sub} has the name of a module root of '
                                 + ', '.join(others))
            if names.get(sub, name) != name:
                info['complain'](f'{name}: its Palomar submission {sub} has the name of the paper of {names[sub]}')

    # Module names and cited sources that two repositories share.
    owners: dict[str, list[str]] = {}
    sources: dict[str, set[str]] = {}
    for name, info in scanned.items():
        for m in info['modules']:
            owners.setdefault(m, []).append(name)
            parts = m.split('.')
            # A deprecated module (`deprecated_module`) that imports the source's new home does not
            # formalize it again.
            if 'External' in parts[:-1] and not deprecated(info['path'], m):
                sources.setdefault(parts[parts.index('External') + 1], set()).add(name)
    old = {r['name'] for r in c.repos if r.get('role') in ('paper', 'background')}
    for m, names in sorted(owners.items()):
        if len(names) > 1:
            (warnings if set(names) <= old else errors).append(
                f'module {m} is in {", ".join(sorted(names))}: they cannot be required together')
    for src, names in sorted(sources.items()):
        if len(names) > 1:
            warnings.append(f'cited source {src} is formalized in {", ".join(sorted(names))}: require one '
                            'from the other, or move it to the lowest hub above both')

    warnings += col.near_duplicates(c)

    print(f'Train: {c.train["lean"]}, Mathlib {c.train["mathlib"]}; '
          + ', '.join(f'{k} {v[:7]}' for k, v in pins.items()) + '\n')
    rows = [('Repository', 'Package', 'Lean', 'Phylogenetics', 'HEAD', 'State')]
    for name, info in sorted(scanned.items()):
        state = ('modified' if info['dirty'] else 'clean') + (
            f', {info["ahead"]} unpushed' if info['ahead'] not in ('0', '-') else '')
        rows.append((name, info['package'], info['toolchain'].split(':')[-1],
                     (info['pins'].get('Phylogenetics') or '-')[:7], info['head'][:7] or '-', state))
    widths = [max(len(r[i]) for r in rows) for i in range(len(rows[0]))]
    for i, r in enumerate(rows):
        print('  '.join(x.ljust(w) for x, w in zip(r, widths)).rstrip())
        if i == 0:
            print('  '.join('-' * w for w in widths))
    for hub in c.hubs:
        ps = [p for p in c.papers if p.hub == hub['name']]
        if ps:
            counts = {s: sum(p.status == s for p in ps) for s in col.STATUSES}
            print(f'\n{hub["name"]}: {len(ps)} papers: ' + ', '.join(f'{n} {s}' for s, n in counts.items() if n))
    for title, items in (('Errors', errors), ('Warnings', warnings)):
        if items:
            print(f'\n{title}:')
            for x in items:
                print(f'  - {x}')
    if not errors:
        print('\nNo errors.')
    return 1 if errors else 0


# ---------------------------------------------------------------------------------------------
# READMEs


def cell(text: str) -> str:
    return text.replace('|', '\\|').replace('\n', ' ')


def anchor(fid: int, title: str) -> str:
    return '#' + re.sub(r'[^\w\- ]', '', f'{fid}. {title}'.lower()).replace(' ', '-')


def block_summary(c: col.Collection, hub: str) -> str:
    fams = sorted(f for (h, f) in c.families if h == hub)
    head = ('| Family | Papers | Formalized | In progress | Partly covered | To do |\n'
            '| --- | ---: | ---: | ---: | ---: | ---: |')
    rows, total = [], {s: 0 for s in col.STATUSES}
    for fid in fams:
        fam = c.families[(hub, fid)]
        ps = c.in_family(hub, fid)
        n = {s: sum(p.status == s for p in ps) for s in col.STATUSES}
        for s in total:
            total[s] += n[s]
        rows.append(f'| [{fid}. {fam["title"]}]({anchor(fid, fam["title"])}) | {len(ps)} | {n["formalized"]} | '
                    f'{n["in-progress"]} | {n["partial"]} | {n["todo"]} |')
    count = sum(total.values())
    rows.append(f'| **All** | **{count}** | **{total["formalized"]}** | **{total["in-progress"]}** | '
                f'**{total["partial"]}** | **{total["todo"]}** |')
    return head + '\n' + '\n'.join(rows)


def block_papers(c: col.Collection, hub: str) -> str:
    """The checklist of the hub's papers, family by family: a paper is checked once formalized, and
    a starred paper, on the shorter route through the field, has a star."""
    out = []
    fams = sorted(f for (h, f) in c.families if h == hub)
    if any(p.starred for p in c.papers if p.hub == hub):
        out.append('The starred papers (★) are a shorter route through the field.\n')
    for fid in fams:
        fam = c.families[(hub, fid)]
        if len(fams) > 1:
            out.append(f'### {fid}. {fam["title"]}\n')
        for p in c.in_family(hub, fid):
            item = (f'- [{"x" if p.status == "formalized" else " "}] {"★ " if p.starred else ""}{p.authors} '
                    f'({p.year}), [{p.title}]({p.url})')
            repo = f'[{p.repo}]({p.github})' if p.commit else ''
            if p.status == 'formalized':
                item += f': {repo}' + ('' if c.on_train(p.repo) else ' (off the train)')
            elif p.status == 'in-progress':
                item += ', in progress' + (f': {repo}' if repo else '')
            elif p.status == 'partial':
                item += ', partly covered by ' + ', '.join(sorted({x['repo'] for x in p.covered_by}))
            out.append(item)
        out.append('')
    return '\n'.join(out).rstrip()


def block_tree(c: col.Collection) -> str:
    rows = ['| Node | Repository | Its library | Holds |', '| --- | --- | --- | --- |']
    for r in c.library_repos():
        if r['role'] == 'root':
            node = 'root'
        elif r['role'] == 'library':
            node = f'library under {r.get("parent", "")}: {r.get("title", "")}'
        elif c.depth(r) == 0:
            node = f'hub of {c.kind(r)}: {r.get("title", "")}'
        else:
            node = f'sub-hub of {r.get("parent", "")}: {r.get("title", "")}'
        rows.append(f'| {cell(node)} | [{r["name"]}]({r["url"]}) | `{r["package"]}` | {cell(r.get("summary", ""))} |')
    return '\n'.join(rows)


def block_repositories(c: col.Collection) -> str:
    words = {'always': 'always', 'when-needed': 'when needed', 'no': 'no'}
    rows = ['| Repository | Role | Under | Lean | Required by new repositories | Holds |',
            '| --- | --- | --- | --- | --- | --- |']
    for r in c.repos:
        if r['role'] in ('paper', 'background'):
            continue  # the papers are in the hubs' checklists
        req = words.get(r.get('require', ''), r.get('require', '-'))
        if r.get('note'):
            req += f'. {r["note"]}'
        rows.append(f'| [{r["name"]}]({r["url"]}) | {r["role"]} | {r.get("parent", "-")} | {r.get("lean", "-")} | '
                    f'{cell(req)} | {cell(r.get("summary", ""))} |')
    return '\n'.join(rows)


def block_foundations(c: col.Collection) -> str:
    rows = ['| Foundation | Status | Home | Where | Families |', '| --- | --- | --- | --- | --- |']
    order = {'available': 0, 'partial': 1, 'missing': 2}
    for f in sorted(c.foundations, key=lambda f: order[f['status']]):
        rows.append(f'| {cell(f["name"])} | {f["status"]} | {f["home"]} | {cell(f.get("where") or "-")} | '
                    f'{cell(", ".join(f.get("needed_by", [])))} |')
    return '\n'.join(rows)


def block_train(c: col.Collection) -> str:
    rows = ['| | Version or commit |', '| --- | --- |', f'| Lean | `{c.train["lean"]}` |',
            f'| Mathlib | `{c.train["mathlib"]}` |']
    by_package = {r.get('package'): r for r in c.library_repos()}
    for pkg, rev in c.train['pins'].items():
        r = by_package.get(pkg)
        link = f'[`{rev[:7]}`]({r["url"]}/commit/{rev})' if r else f'`{rev[:7]}`'
        rows.append(f'| {pkg} | {link} |')
    return '\n'.join(rows)


ROOT_BLOCKS = {'collection:tree': block_tree, 'collection:train': block_train,
               'collection:repositories': block_repositories, 'collection:foundations': block_foundations}
HUB_BLOCKS = {'catalog:summary': block_summary, 'catalog:papers': block_papers}


def render(text: str, blocks: dict, *args) -> str:
    for name, fn in blocks.items():
        begin, end = f'<!-- BEGIN {name} -->', f'<!-- END {name} -->'
        pattern = re.compile(re.escape(begin) + r'.*?' + re.escape(end), re.S)
        if not pattern.search(text):
            continue
        body = (f'{begin}\n<!-- Generated by lean4-phylogenetics/scripts/status.py readme --write. Do not edit. -->\n\n'
                f'{fn(*args)}\n\n{end}')
        text = pattern.sub(lambda m: body, text)
    return text


def readme(c: col.Collection, write: bool, check_only: bool, only: list[str]) -> int:
    targets = [(col.ROOT / 'README.md', ROOT_BLOCKS, (c,), 'lean4-phylogenetics')]
    for hub in c.hubs:
        if hub['name'] in c.catalogs:
            targets.append((c.path(hub['name']) / 'README.md', HUB_BLOCKS, (c, hub['name']), hub['name']))
    status = 0
    for path, blocks, args, name in targets:
        if only and name not in only:
            continue
        old = path.read_text()
        new = render(old, blocks, *args)
        if check_only:
            if new != old:
                print(f'{path} is out of date: run python3 scripts/status.py readme --write')
                status = 1
            else:
                print(f'{path} is up to date.')
        elif write:
            path.write_text(new)
            print(f'{path} written.' if new != old else f'{path} was up to date.')
        else:
            sys.stdout.write(new)
    return status


def next_papers(c: col.Collection) -> int:
    print('Papers to start, hub by hub; "ready" means every paper it builds on is formalized.\n')
    for hub in c.hubs:
        for (h, fid), fam in sorted(c.families.items()):
            if h != hub['name']:
                continue
            open_ = [p for p in c.in_family(h, fid) if p.status in ('todo', 'partial', 'in-progress')]
            if not open_:
                continue
            print(f'{h}, {fid}. {fam["title"]}')
            for p in open_:
                waits = [d for d in p.builds_on if c.paper(d).status != 'formalized']
                state = 'in progress' if p.status == 'in-progress' else (
                    'ready' if not waits else 'waits on ' + ', '.join(waits))
                print(f'  {p.id:30} {state}{" (partly covered)" if p.status == "partial" else ""}')
            print()
    return 0


def fetch_hubs() -> None:
    """Clone, shallowly, every hub and library of the registry that is not in the workspace."""
    c = col.load(private=False)
    for hub in c.hubs + c.libraries:
        path = col.repo_path(hub['name'], hub['role'])
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['git', 'clone', '--quiet', '--depth', '1', hub['url'], str(path)], check=True)
            print(f'cloned {hub["name"]}')


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    sub = ap.add_subparsers(dest='cmd')
    sub.add_parser('check', help='check the registry, the catalogs and the repositories on disk')
    r = sub.add_parser('readme', help='regenerate the READMEs\' tables')
    g = r.add_mutually_exclusive_group()
    g.add_argument('--write', action='store_true')
    g.add_argument('--check', action='store_true')
    r.add_argument('--repo', action='append', default=[], help='only this repository\'s README (repeatable)')
    r.add_argument('--fetch-hubs', action='store_true',
                   help='clone the hubs that are not in the workspace (in CI, where only one is checked out): '
                        'a hub\'s papers may build on papers of another hub')
    sub.add_parser('next', help='the papers to start next')
    args = ap.parse_args()
    if args.cmd == 'readme':
        if args.fetch_hubs:
            fetch_hubs()
        sys.exit(readme(col.load(private=False), args.write, args.check, args.repo))
    c = col.load(private=True)
    sys.exit(next_papers(c) if args.cmd == 'next' else check(c))


if __name__ == '__main__':
    main()
