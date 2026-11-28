"""The collection of Lean formalizations rooted at lean4-phylogenetics.

The collection is a tree of repositories. Its root, lean4-phylogenetics, holds the library that
everything shares, the registry of the repositories (collection/repos.toml), the shared foundations
(collection/foundations.toml), the conventions and the tools. Each hub holds a library of what its
papers share, and a catalog of its papers (catalog/papers.toml). A hub's parent is the root or another
hub, of which it is a sub-hub. A library is a repository under a hub, with a library and no catalog:
what some papers of that hub share and the rest do not, which they require through `uses`
(lean4-phylo-tree-of-blobs, under lean4-phylo-network). The repositories are in one directory, the
workspace: this one and the private repository at its top, the hubs and the libraries in hubs/, the
repositories of papers in papers/<hub>/ (`repo_path`). The private files of each repository are kept at
the same place in the private repository (docs/CONVENTIONS.md, Section 7).

Imported by scripts/status.py and scripts/new_paper.py. Python 3.11 or later.
"""

from __future__ import annotations

import re
import tomllib
import unicodedata
import urllib.parse
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent      # this repository
COLLECTION = ROOT / 'collection'
WORKSPACE = ROOT.parent
GITHUB_OWNER = 'formal-phylogenetics'

STATUSES = ('formalized', 'in-progress', 'partial', 'todo')
KINDS = ('theory', 'theory+algorithm', 'method', 'evaluation', 'method+evaluation', 'theory+evaluation',
         'theory+method')
ROLES = ('root', 'hub', 'library', 'paper', 'background', 'tool')
HUB_KINDS = ('inference', 'theory')   # of a hub under the root (docs/CONVENTIONS.md, Section 1)
# Generic module roots that older repositories use and that no new repository may use: Lean module
# names are global, and the repositories of the collection import one another.
RESERVED_ROOTS = {'Basic', 'External', 'Challenge', 'Solution', 'MainResults', 'Main', 'Defs'}


@dataclass
class Paper:
    id: str
    family: int
    order: int
    authors: str
    year: str
    title: str
    url: str
    kind: str
    root: str
    status: str
    hub: str = ''
    paper: str = ''         # the paper's name, if not its root (docs/CONVENTIONS.md, Section 2)
    short: str = ''
    repo: str = ''
    commit: str = ''
    uses: list[str] = field(default_factory=list)
    builds_on: list[str] = field(default_factory=list)
    covered_by: list[dict] = field(default_factory=list)
    note: str = ''
    landmark: bool = False  # a landmark of the field, on the shorter route through it

    def __post_init__(self):
        if not self.repo:
            self.repo = f'lean4-{self.id}'
        self.paper_given = bool(self.paper)   # whether the entry states `paper`
        if not self.paper:
            self.paper = self.root

    @property
    def path(self) -> Path:
        return repo_path(self.repo, 'paper', self.hub)

    @property
    def github(self) -> str:
        return f'https://github.com/{GITHUB_OWNER}/{self.repo}'

    @property
    def cite(self) -> str:
        base = f'{self.authors} {self.year}'
        return f'{self.short} ({base})' if self.short else base


@dataclass
class Collection:
    train: dict
    repos: list[dict]
    foundations: list[dict]
    families: dict[tuple[str, int], dict] = field(default_factory=dict)
    papers: list[Paper] = field(default_factory=list)
    catalogs: dict[str, Path] = field(default_factory=dict)   # hub -> its catalog, if on disk
    subhubs: dict[str, list[dict]] = field(default_factory=dict)   # hub -> the [[subhub]] of its catalog

    @property
    def by_id(self) -> dict[str, Paper]:
        return {p.id: p for p in self.papers}

    @property
    def hubs(self) -> list[dict]:
        return [r for r in self.repos if r.get('role') == 'hub']

    @property
    def libraries(self) -> list[dict]:
        """The repositories of role `library`: a library under a hub, with no catalog."""
        return [r for r in self.repos if r.get('role') == 'library']

    def paper(self, pid: str) -> Paper:
        try:
            return self.by_id[pid]
        except KeyError:
            raise SystemExit(f'no paper {pid!r} in the catalogs of the hubs') from None

    def repo(self, name: str) -> dict | None:
        return next((r for r in self.repos if r['name'] == name), None)

    def place(self, name: str) -> tuple[str, str]:
        """The role of the repository `name` and the hub it is under, from the registry or the catalogs."""
        r = self.repo(name)
        hub = next((p.hub for p in self.papers if p.repo == name), '')
        if r:
            parent = self.repo(r.get('parent', ''))
            return r.get('role', ''), hub or (parent['name'] if parent and parent.get('role') == 'hub' else '')
        return ('paper', hub) if hub else ('', '')

    def path(self, name: str) -> Path:
        """Where the repository `name` is, or goes, in the workspace (`repo_path`)."""
        return repo_path(name, *self.place(name))

    def home(self, name: str) -> Path:
        """Where the repository `name` belongs in the workspace (`repo_home`)."""
        return repo_home(name, *self.place(name))

    def in_family(self, hub: str, fid: int) -> list[Paper]:
        return sorted((p for p in self.papers if p.hub == hub and p.family == fid), key=lambda p: p.order)

    def lean_version(self) -> str:
        return self.train['lean'].split(':', 1)[1]

    def on_train(self, repo: str) -> bool:
        r = self.repo(repo)
        return r is None or r.get('lean', self.lean_version()) == self.lean_version()

    def library_repos(self) -> list[dict]:
        """The root, the hubs and the libraries: the nodes of the tree that hold a library, in the
        order of the tree (each hub, and each library, after the hub above it)."""
        out: list[dict] = []

        def visit(parent: str) -> None:
            for r in self.repos:
                if r.get('role') in ('hub', 'library') and r.get('parent') == parent and r not in out:
                    out.append(r)
                    visit(r['name'])

        for r in self.repos:
            if r.get('role') == 'root':
                out.append(r)
                visit(r['name'])
        return out + [r for r in self.repos if r.get('role') in ('root', 'hub', 'library') and r not in out]

    def hubs_above(self, name: str) -> list[dict]:
        """The hubs above a hub or a paper's hub, from the top of the tree down to `name` itself if it
        is a hub: the libraries that a repository under `name` requires besides the root's."""
        chain: list[dict] = []
        r = self.repo(name)
        while r is not None and r.get('role') == 'hub' and r not in chain:
            chain.append(r)
            r = self.repo(r.get('parent', ''))
        return chain[::-1]

    def kind(self, hub: dict) -> str:
        """"inference" or "theory": the kind of the hub under the root that `hub` is, or is under."""
        return (self.hubs_above(hub['name'])[0] if self.hubs_above(hub['name']) else hub).get('kind', '')

    def depth(self, hub: dict) -> int:
        """0 for a hub under the root, 1 for its sub-hubs, and so on."""
        return len(self.hubs_above(hub['name'])) - 1

    def validate(self) -> list[str]:
        errors = []
        names = [r['name'] for r in self.repos]
        for r in self.repos:
            where = f"repository {r.get('name')!r}"
            if r.get('role') not in ROLES:
                errors.append(f"{where}: role {r.get('role')!r} is not one of {ROLES}")
            if r.get('role') in ('hub', 'library', 'paper', 'background') and r.get('parent') not in names:
                errors.append(f"{where}: its parent {r.get('parent')!r} is not in the registry")
            if r.get('role') == 'hub':
                above = self.repo(r.get('parent', ''))
                if above is not None and above.get('role') not in ('root', 'hub'):
                    errors.append(f"{where}: the parent of a hub is the root or a hub, not {above['name']}")
                seen_up, up = set(), r
                while up is not None and up.get('role') == 'hub':
                    if up['name'] in seen_up:
                        errors.append(f"{where}: the parents of the hubs form a cycle")
                        break
                    seen_up.add(up['name'])
                    up = self.repo(up.get('parent', ''))
            if r.get('role') == 'hub':
                under_root = (self.repo(r.get('parent', '')) or {}).get('role') == 'root'
                if under_root and r.get('kind') not in HUB_KINDS:
                    errors.append(f"{where}: a hub under the root has a `kind`, one of {HUB_KINDS}")
                if not under_root and 'kind' in r:
                    errors.append(f"{where}: a sub-hub is of its hub's kind and states none")
            if r.get('role') == 'library':
                above = self.repo(r.get('parent', ''))
                if above is not None and above.get('role') != 'hub':
                    errors.append(f"{where}: the parent of a library is a hub, not {above['name']}")
                if 'kind' in r:
                    errors.append(f"{where}: a library is of its hub's kind and states none")
            if r.get('role') in ('root', 'hub', 'library') and r.get('package') not in self.train.get('pins', {}):
                errors.append(f"{where}: [train.pins] has no commit of its library {r.get('package')!r}")
        if len(set(names)) != len(names):
            errors.append('the registry lists a repository twice')
        hubs = {h['name'] for h in self.hubs}
        usable = hubs | {r['name'] for r in self.libraries}
        # The roots of the repositories, by owner: each package of the registry, and each paper's.
        # Papers that share a repository share its root.
        packages = {r['package']: r['name'] for r in self.repos if r.get('package')}
        roots = {p.root: p.repo for p in self.papers} | packages
        seen_id: dict[str, str] = {}
        seen_root: dict[str, str] = {}            # root -> repository
        seen_paper: dict[str, Paper] = {}         # an explicit `paper` -> its entry
        for p in self.papers:
            where = f'paper {p.id!r} ({p.hub})'
            if not re.fullmatch(r'[a-z0-9]+(-[a-z0-9]+)*', p.id):
                errors.append(f'{where}: an id is lower case letters, digits and hyphens')
            # The root, and the paper's name when the entry states one; by default it is the root.
            for key in ('root', 'paper') if p.paper_given else ('root',):
                value = getattr(p, key)
                if not re.fullmatch(r'[A-Z][A-Za-z0-9]*', value):
                    errors.append(f'{where}: {key} {value!r} is not a capitalized ASCII Lean identifier')
                if value in RESERVED_ROOTS:
                    errors.append(f'{where}: {key} {value!r} is reserved')
            if packages.get(p.root, p.repo) != p.repo:
                errors.append(f'{where}: root {p.root!r} is the package of {packages[p.root]}')
            # The Palomar library's modules are <paper>.Challenge and <paper>.Solution: they may be
            # under the repository's own root, never under another's.
            if roots.get(p.paper, p.repo) != p.repo:
                errors.append(f'{where}: paper {p.paper!r} is the root of {roots[p.paper]}')
            if p.id in seen_id:
                errors.append(f'{where}: id {p.id!r} is also that of a paper of {seen_id[p.id]}')
            seen_id[p.id] = p.hub
            if seen_root.setdefault(p.root, p.repo) != p.repo:
                errors.append(f'{where}: root {p.root!r} is also that of {seen_root[p.root]}')
            if p.paper_given:
                other = seen_paper.setdefault(p.paper, p)
                if other.repo != p.repo:   # within a repository, the check below reports it
                    errors.append(f'{where}: paper {p.paper!r} is also that of {other.id!r}')
            if not isinstance(p.landmark, bool):
                errors.append(f'{where}: landmark is true or false')
            if p.status not in STATUSES:
                errors.append(f'{where}: status {p.status!r} is not one of {STATUSES}')
            if p.kind not in KINDS:
                errors.append(f'{where}: kind {p.kind!r} is not one of {KINDS}')
            if (p.hub, p.family) not in self.families:
                errors.append(f'{where}: no family {p.family} in its hub')
            if p.status == 'formalized' and not re.fullmatch(r'[0-9a-f]{40}', p.commit):
                errors.append(f'{where}: a formalized paper needs the full hash of its commit')
            if p.status == 'partial' and not p.covered_by:
                errors.append(f'{where}: a partial paper says what covers it (covered_by)')
            for h in p.uses:
                if h not in usable:
                    errors.append(f'{where}: uses {h!r}, which is not a hub or a library')
            for dep in p.builds_on:
                if dep not in self.by_id:
                    errors.append(f'{where}: builds_on names an unknown paper {dep!r}')
            for cov in p.covered_by:
                if set(cov) != {'repo', 'what'}:
                    errors.append(f'{where}: each covered_by entry has exactly `repo` and `what`')
        # A repository with several papers (formalize-math-paper, references/multi-paper.md): one
        # root, and a name of its own for each paper, at most one of them the default, the root.
        by_repo: dict[str, list[Paper]] = {}
        for p in self.papers:
            by_repo.setdefault(p.repo, []).append(p)
        for repo, ps in by_repo.items():
            if len({q.root for q in ps}) > 1:
                errors.append(f'repository {repo}: its papers share its root, but their entries give '
                              + ', '.join(f'{q.root!r} ({q.id})' for q in ps))
            names: dict[str, str] = {}
            for q in ps:
                if q.paper in names:
                    errors.append(f'repository {repo}: papers {names[q.paper]!r} and {q.id!r} have the '
                                  f'same name {q.paper!r}; each paper of a repository has its own `paper` '
                                  '(at most one leaves it to the root)')
                names.setdefault(q.paper, q.id)
        # A hub's catalog lists its sub-hubs, which the registry places under it.
        for hub, listed in self.subhubs.items():
            names_listed = {x.get('repo') for x in listed}
            below = {h['name'] for h in self.hubs if h.get('parent') == hub}
            for x in sorted(names_listed - below):
                errors.append(f'catalog of {hub}: lists the sub-hub {x!r}, whose parent in the registry is not {hub}')
            for x in sorted(below - names_listed):
                errors.append(f'catalog of {hub}: does not list its sub-hub {x!r} ([[subhub]])')
        # A paper has one entry in all the catalogs: no two entries share a DOI, an arXiv, PubMed or
        # PubMed Central identifier, or a title and a first author.
        seen_link: dict[tuple[str, str], Paper] = {}
        seen_title: dict[tuple[str, str], Paper] = {}
        for p in self.papers:
            for key, seen, what in ((link_key(p.url), seen_link, 'link'),
                                    ((first_author(p.authors), fold(p.title)), seen_title, 'title and first author')):
                other = seen.setdefault(key, p)
                if other is not p:
                    errors.append(f'paper {p.id!r} ({p.hub}) has the {what} of {other.id!r} ({other.hub}): '
                                  'a paper has one entry in all the catalogs')
        cycle = find_cycle({p.id: p.builds_on for p in self.papers})
        if cycle:
            errors.append('builds_on has a cycle: ' + ' -> '.join(cycle))
        for f in self.foundations:
            if f.get('status') not in ('available', 'partial', 'missing'):
                errors.append(f"foundation {f.get('id')!r}: bad status {f.get('status')!r}")
        for key in ('lean', 'mathlib', 'pins'):
            if key not in self.train:
                errors.append(f'[train] has no {key!r}')
        return errors


def paper_folder(hub: str) -> str:
    """The folder of papers/ that holds the repositories of the papers of `hub`: the hub's name without
    `lean4-phylo-` (network, tree-of-blobs, ...), or background for a paper under no hub."""
    return hub.removeprefix('lean4-phylo-') if hub.startswith('lean4-phylo-') else 'background'


def repo_home(name: str, role: str = '', hub: str = '') -> Path:
    """Where the repository `name` belongs in the workspace: a hub or a library in hubs/, a paper's
    repository in papers/<the folder of its hub>/, the root and the others at the top."""
    if role in ('hub', 'library'):
        return WORKSPACE / 'hubs' / name
    if role in ('paper', 'background'):
        return WORKSPACE / 'papers' / paper_folder(hub) / name
    return WORKSPACE / name


def repo_path(name: str, role: str = '', hub: str = '') -> Path:
    """Where the repository `name` is in the workspace: at its home (`repo_home`), or found in hubs/,
    in a folder of papers/ or at the top, as in CI, where a hub is checked out beside the root. One that
    is nowhere goes to its home."""
    home = repo_home(name, role, hub)
    found = [home, WORKSPACE / 'hubs' / name, *sorted((WORKSPACE / 'papers').glob(f'*/{name}')), WORKSPACE / name]
    return next((path for path in found if path.exists()), home)


def fold(text: str) -> str:
    """Lower case ASCII words: titles and names compared up to case, accents and punctuation."""
    text = unicodedata.normalize('NFKD', text).encode('ascii', 'ignore').decode().lower()
    return ' '.join(re.sub(r'[^a-z0-9]+', ' ', text).split())


def first_author(authors: str) -> str:
    return fold(re.split(r',| et al\.', authors)[0])


def link_key(url: str) -> tuple[str, str]:
    """What identifies the publication that a catalog's link points to: its DOI, arXiv, PubMed or
    PubMed Central identifier, or else the link itself."""
    u = urllib.parse.unquote(url).strip()
    for kind, pattern in (('doi', r'doi\.org/(10\..+)'), ('arxiv', r'arxiv\.org/(?:abs|pdf)/([^?#]+?)(?:v\d+)?(?:\.pdf)?/?$'),
                          ('pmid', r'pubmed\.ncbi\.nlm\.nih\.gov/(\d+)'), ('pmc', r'/articles/(PMC\d+)')):
        m = re.search(pattern, u, flags=re.I)
        if m:
            return kind, m.group(1).rstrip('/').lower()
    return 'url', re.sub(r'^https?://(www\.)?', '', u).rstrip('/').lower()


def near_duplicates(c: Collection, ratio: float = 0.9) -> list[str]:
    """Entries by one first author whose titles are nearly the same: often a preprint, a proceedings
    paper and a journal paper, which are one paper unless their results differ. Entries of which one
    builds on the other are not reported."""
    from difflib import SequenceMatcher
    by_author: dict[str, list[Paper]] = {}
    for p in c.papers:
        by_author.setdefault(first_author(p.authors), []).append(p)
    out = []
    for ps in by_author.values():
        for i, p in enumerate(ps):
            for q in ps[i + 1:]:
                a, b = fold(p.title), fold(q.title)
                # One that builds on the other is known to be another paper.
                if q.id in p.builds_on or p.id in q.builds_on:
                    continue
                if a != b and SequenceMatcher(None, a, b).ratio() >= ratio:
                    out.append(f'papers {p.id!r} ({p.hub}) and {q.id!r} ({q.hub}) have nearly the same title and '
                               'first author: one paper, unless their results differ')
    return out


def find_cycle(graph: dict[str, list[str]]) -> list[str]:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(n):
        state[n] = 1
        stack.append(n)
        for m in graph.get(n, []):
            if state.get(m) == 1:
                return stack[stack.index(m):] + [m]
            if m in graph and state.get(m) is None:
                found = visit(m)
                if found:
                    return found
        stack.pop()
        state[n] = 2
        return []

    for n in graph:
        if state.get(n) is None:
            found = visit(n)
            if found:
                return found
    return []


def _toml(path: Path) -> dict:
    with open(path, 'rb') as f:
        return tomllib.load(f)


def private_folder() -> Path | None:
    """This repository's private folder, where its gitignored `notes` link points; None without it."""
    link = ROOT / 'notes'
    return link.resolve().parent if link.is_symlink() else None


def load(private: bool = False, hubs_from: Path | None = None) -> Collection:
    """The registry, the foundations, and the catalog of every hub found in the workspace. With
    `private`, the private overlay (catalog-private.toml in the private folder) is merged in: it
    holds what the public files must not say. READMEs are rendered without it."""
    reg = _toml(COLLECTION / 'repos.toml')
    c = Collection(train=reg.get('train', {}), repos=reg.get('repo', []),
                   foundations=_toml(COLLECTION / 'foundations.toml').get('foundation', []))
    overlay = {}
    folder = private_folder()
    if private and folder and (folder / 'catalog-private.toml').exists():
        overlay = _toml(folder / 'catalog-private.toml')
        c.repos += overlay.get('repo', [])
    for hub in c.hubs:
        path = (hubs_from / hub['name'] if hubs_from else repo_path(hub['name'], 'hub')) / 'catalog' / 'papers.toml'
        if not path.exists():
            continue
        c.catalogs[hub['name']] = path
        data = _toml(path)
        for f in data.get('family', []):
            c.families[(hub['name'], f['id'])] = f
        c.subhubs[hub['name']] = data.get('subhub', [])
        for p in data.get('paper', []):
            c.papers.append(Paper(hub=hub['name'], **p))
    for o in overlay.get('paper', []):
        p = c.by_id.get(o['id'])
        if p:
            for k, v in o.items():
                setattr(p, k, v)
            if 'paper' in o:
                p.paper_given = True
            elif not p.paper_given:
                p.paper = p.root
    return c


def set_field(c: Collection, pid: str, key: str, value: str, after: str = 'root') -> None:
    """Set one string field of a paper in its hub's catalog, leaving the rest of the file as it is:
    its line is replaced, or, if the entry has none, added after the line of `after`."""
    p = c.paper(pid)
    path = c.catalogs[p.hub]
    lines = path.read_text().splitlines(keepends=True)
    start = next((i for i, l in enumerate(lines) if l.strip() == f'id = "{pid}"'), None)
    if start is None:
        raise SystemExit(f'no paper {pid!r} in {path}')
    end = next((i for i in range(start + 1, len(lines)) if lines[i].startswith('[[')), len(lines))
    line = f'{key} = "{value}"\n'
    for i in range(start + 1, end):
        if re.match(rf'{key}\s*=', lines[i]):
            lines[i] = line
            break
    else:
        at = next((i for i in range(start + 1, end) if re.match(rf'{after}\s*=', lines[i])), None)
        if at is None:
            raise SystemExit(f'paper {pid!r} has no {key} line and no {after} line in {path}')
        lines.insert(at + 1, line)
    path.write_text(''.join(lines))
    setattr(p, key, value)


def set_status(c: Collection, pid: str, status: str) -> None:
    """Change one paper's `status` line in its hub's catalog, leaving the rest of the file as it is."""
    assert status in STATUSES
    set_field(c, pid, 'status', status)
