#!/usr/bin/env python3
"""Exact Python replica of WedgeCover.Node.check, run on a generated
WedgeCoverData.lean: an independent check of the view cover (which the
verifier evaluates natively).

Usage: python3 scripts/check_wedge_cover.py Noperthedron/PentagonalHexecontahedron/WedgeCoverData.lean"""
import re, sys
from fractions import Fraction as F
sys.setrecursionlimit(100000)
s = open(sys.argv[1]).read()
def rat(t):
    t = t.strip().strip('()').replace(': ℚ', '').strip()
    if '/' in t:
        a, b = t.split('/'); return F(int(a.strip().strip('()')), int(b))
    return F(int(t.strip('()')))
def vec(t):  # "![a, b, c]"
    inner = t.strip()[2:-1]
    return [rat(x) for x in re.split(r',(?![^()]*\))', inner)]
i = s.index('def codeTriangles'); j = s.index(']\n', s.index('#[', i))
tris = []
for line in s[s.index('#[', i) + 2:j].split('\n'):
    line = line.strip().rstrip(',')
    if not line: continue
    parts = re.findall(r'!\[[^\[\]]*\]', line)
    tris.append([vec(p) for p in parts])
base = [vec(p) for p in re.findall(r'!\[[^\[\]]*\]', re.search(r'def baseTriangle : Tri := (.*)', s).group(1))]
nodes = {}
for m in re.finditer(r'def (node_\d+) : Node := (.*)', s):
    nodes[m.group(1)] = m.group(2)
def dot(a, b): return sum(x * y for x, y in zip(a, b))
def cross(a, b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
def det(a, b, c): return dot(a, cross(b, c))
def edgeFn(t, i):
    o = 1 if det(*t) > 0 else -1
    return [o * x for x in cross(t[(i+1) % 3], t[(i+2) % 3])]
def combo(cs, lam):
    r = [F(0)] * 3
    for a, l in zip(cs, lam):
        r = [r[k] + l * a[k] for k in range(3)]
    return r
def qlist(t): return [rat(x) for x in re.split(r',(?![^()]*\))', t.strip()[1:-1])] if t.strip() != '[]' else []
bad = []
def check(name, cs, depth=0):
    d = nodes[name]
    if d.startswith('.split'):
        m = re.match(r'\.split (!\[.*?\]) (node_\d+) (node_\d+)$', d)
        n = vec(m.group(1))
        return check(m.group(2), cs + [n]) and check(m.group(3), cs + [[-x for x in n]])
    if d.startswith('.leaf'):
        m = re.match(r'\.leaf (\d+) \[(.*)\]$', d)
        t = int(m.group(1)); tri = tris[t]
        if det(*tri) == 0 or any(sum(c) != 1 for c in tri): bad.append((name, 'tri')); return False
        certs = re.findall(r'\((\[.*?\]), ((?:\(-?\d+(?: / \d+)? : ℚ\))|-?\d+)\)', m.group(2))
        if len(certs) < 3: bad.append((name, 'ncerts %d' % len(certs))); return False
        for i in range(3):
            mu = qlist(certs[i][0]); k = rat(certs[i][1])
            if len(mu) != len(cs) or any(x < 0 for x in mu) or k < 0:
                bad.append((name, 'cert shape', i, len(mu), len(cs))); return False
            rhs = combo(cs, mu); rhs = [rhs[c] + k for c in range(3)]
            if edgeFn(tri, i) != rhs: bad.append((name, 'cert eq', i)); return False
        return True
    bad.append((name, 'kind')); return False
cs0 = [edgeFn(base, i) for i in range(3)]
ok = check('node_1', cs0)
print("tris", len(tris), "nodes", len(nodes), "check", ok, bad[:5])
