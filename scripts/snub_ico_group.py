#!/usr/bin/env python3
"""Generate Noperthedron/Nopert231/IcoGroupData.lean: the icosahedral rotation
group I in the snub dodecahedron's 5-fold frame, exactly over
K = Q(sqrt5, s), s = sin 72 deg (IcoField.lean; nopert229/notes/S.md §2.2).

The group is the closure of three generators, computed in exact arithmetic:
  Rz(72 deg), Rx(180 deg) = diag(1, -1, -1), and the rotation by 72 deg about
  the 5-fold axis at polar cos 1/sqrt5 and azimuth 54 deg.
Elements are numbered in breadth-first order from the identity (element 0).

Emitted, besides the 60 matrices (entries in units of 1/20, IcoField.IcoZ):
  icoGen, icoGenMul  the three generators, and right multiplication by them
  icoBfsParent/Gen  each element as (smaller element) * generator, so that
                    Lean derives closure from the 180 generator products
  icoRzIndex, icoRxIndex  Rz(72 deg) and Rx(180 deg)
  icoNeighborIndex  the 12 rotations by +-72 deg about the six 5-fold axes, in
                    the order of nopert229/symmetry_neighbors.h (the C++ search
                    journals refer to neighbor n)
  icoInverseIndex   each element's inverse (its transpose)
  elementVertexIndex  the inverse of vertexElementIndex
  vertexElementIndex  the element g with vertex i = g * vertex 0, from the
                    model's vertices (nopert229/snub_model.txt); the snub
                    dodecahedron's vertices are a free I-orbit

The script checks, in exact arithmetic, that the 60 matrices are orthogonal
with determinant 1, and numerically that the neighbors and the vertex
elements match the model. Lean re-decides the algebraic facts.

Usage: python3 scripts/snub_ico_group.py [--nopert229 DIR] [--out FILE]
"""

from __future__ import annotations

import argparse
import math
import re
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent

R5 = math.sqrt(5)
S72 = math.sqrt((5 + R5) / 8)


class K:
    """a + b sqrt5 + c s + d s sqrt5, s^2 = (5 + sqrt5)/8 (IcoK in Lean)."""

    __slots__ = ("v",)

    def __init__(self, a=0, b=0, c=0, d=0):
        self.v = (F(a), F(b), F(c), F(d))

    def __add__(x, y):
        return K(*(p + q for p, q in zip(x.v, y.v)))

    def __neg__(x):
        return K(*(-p for p in x.v))

    def __sub__(x, y):
        return x + (-y)

    def __mul__(x, y):
        a, b, c, d = x.v
        e, f, g, h = y.v
        p, q = c * g + 5 * d * h, c * h + d * g
        return K(a * e + 5 * b * f + (5 * p + 5 * q) / 8, a * f + b * e + (p + 5 * q) / 8,
                 a * g + 5 * b * h + c * e + 5 * d * f, a * h + b * g + c * f + d * e)

    def __eq__(x, y):
        return x.v == y.v

    def __hash__(x):
        return hash(x.v)

    def f(x) -> float:
        a, b, c, d = x.v
        return float(a) + float(b) * R5 + float(c) * S72 + float(d) * R5 * S72


Z, ONE = K(), K(1)


def mm(x, y):
    return tuple(tuple(sum((x[i][k] * y[k][j] for k in range(3)), Z) for j in range(3))
                 for i in range(3))


def transpose(x):
    return tuple(tuple(x[j][i] for j in range(3)) for i in range(3))


def det(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


IDENTITY = tuple(tuple(ONE if i == j else Z for j in range(3)) for i in range(3))
C72 = K(F(-1, 4), F(1, 4))  # (sqrt5 - 1)/4
S72K = K(0, 0, 1)
RZ = ((C72, -S72K, Z), (S72K, C72, Z), (Z, Z, ONE))
RX = ((ONE, Z, Z), (Z, -ONE, Z), (Z, Z, -ONE))


def tilted_rotation():
    """Rotation by 72 deg about the 5-fold axis at polar cos 1/sqrt5, azimuth 54 deg."""
    sin_t, cos_t = K(0, F(2, 5)), K(0, F(1, 5))  # 2/sqrt5, 1/sqrt5
    cos_a = K(0, 0, F(-1, 2), F(1, 2))  # cos 54 = sin 36 = s (sqrt5 - 1)/2
    sin_a = K(F(1, 4), F(1, 4))  # sin 54 = cos 36 = (1 + sqrt5)/4
    n = (sin_t * cos_a, sin_t * sin_a, cos_t)
    cross = ((Z, -n[2], n[1]), (n[2], Z, -n[0]), (-n[1], n[0], Z))
    return tuple(tuple((C72 if i == j else Z) + S72K * cross[i][j] + (ONE - C72) * n[i] * n[j]
                       for j in range(3)) for i in range(3))


def generate():
    gens = [RZ, RX, tilted_rotation()]
    group, index = [IDENTITY], {IDENTITY: 0}
    i = 0
    while i < len(group):
        for g in gens:
            h = mm(group[i], g)
            if h not in index:
                index[h] = len(group)
                group.append(h)
        if len(group) > 60:
            raise SystemExit("closure exceeded 60 elements")
        i += 1
    if len(group) != 60:
        raise SystemExit(f"closure has {len(group)} elements, want 60")
    for g in group:
        if mm(g, transpose(g)) != IDENTITY or det(g) != ONE:
            raise SystemExit("an element is not a rotation")
    table = [[index[mm(g, h)] for h in group] for g in group]
    return group, index, table


def numeric(m):
    return [m[i][j].f() for i in range(3) for j in range(3)]


def match(m, target, tol):
    return all(abs(x - y) < tol for x, y in zip(numeric(m), target))


def lean_q(q: F) -> str:
    if q.denominator == 1:
        return f"{q.numerator}" if q >= 0 else f"({q.numerator})"
    return f"({q.numerator}/{q.denominator})"


def lean_k(x: K) -> str:
    return "⟨" + ", ".join(lean_q(q) for q in x.v) + "⟩"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nopert229", type=Path, default=REPO.parent / "nopert229")
    ap.add_argument("--out", type=Path, default=REPO / "Noperthedron/Nopert231/IcoGroupData.lean")
    args = ap.parse_args()

    group, index, table = generate()

    hdr = (args.nopert229 / "symmetry_neighbors.h").read_text()
    rows = [[int(x) / 1e12 for x in r.split(",")]
            for r in re.findall(r"\{([-0-9, ]+)\}", hdr)]
    rows = [r for r in rows if len(r) == 9]
    if len(rows) != 12:
        raise SystemExit(f"expected 12 neighbors in symmetry_neighbors.h, got {len(rows)}")
    neighbors = []
    for r in rows:
        hits = [k for k, g in enumerate(group) if match(g, r, 1e-11)]
        if len(hits) != 1:
            raise SystemExit(f"neighbor matches {len(hits)} elements")
        neighbors.append(hits[0])

    verts = []
    for line in (args.nopert229 / "snub_model.txt").read_text().splitlines():
        if line.startswith("vertex "):
            parts = line.split()
            verts.append([float(x) for x in parts[2:5]])
    if len(verts) != 60:
        raise SystemExit(f"expected 60 vertices, got {len(verts)}")
    v0 = verts[0]
    elem = []
    for v in verts:
        hits = [k for k, g in enumerate(group)
                if all(abs(sum(numeric(g)[3 * i + j] * v0[j] for j in range(3)) - v[i]) < 1e-12
                       for i in range(3))]
        if len(hits) != 1:
            raise SystemExit(f"vertex matches {len(hits)} elements")
        elem.append(hits[0])
    if sorted(elem) != list(range(60)):
        raise SystemExit("vertexElement is not a bijection")
    rz, rx = index[RZ], index[RX]
    # Rotation-major order: vertex 12 k + s = Rz^k seed s.
    for k in range(5):
        for s in range(12):
            want = elem[s]
            for _ in range(k):
                want = table[rz][want]
            if elem[12 * k + s] != want:
                raise SystemExit("vertex order is not rotation-major under Rz")

    gens = [index[RZ], index[RX], index[tilted_rotation()]]
    # BFS parents: element h > 0 was found as parent * generator, parent < h.
    parent, parent_gen = [0], [0]
    for h in range(1, 60):
        for p in range(h):
            hit = [k for k, g in enumerate(gens) if table[p][g] == h]
            if hit:
                parent.append(p)
                parent_gen.append(hit[0])
                break
        else:
            raise SystemExit("no BFS parent")

    def z(x):
        v = [q * 20 for q in x.v]
        if any(q.denominator != 1 for q in v):
            raise SystemExit("an entry is not an integer multiple of 1/20")
        return [int(q) for q in v]

    def m3(g):
        return "⟨" + ", ".join("⟨" + ", ".join(str(c) for c in z(x)) + "⟩"
                               for row in g for x in row) + "⟩"

    def tree(lo, hi, indent):
        if hi - lo == 1:
            return m3(group[lo])
        mid = (lo + hi) // 2
        pad = " " * (indent + 2)
        return (f"if n < {mid} then\n{pad}{tree(lo, mid, indent + 2)}\n"
                f"{' ' * indent}else\n{pad}{tree(mid, hi, indent + 2)}")

    def nat_list(xs):
        return "[" + ", ".join(map(str, xs)) + "]"

    out = []
    w = out.append
    w("module\n\npublic import Noperthedron.Nopert231.IcoField\n\n@[expose] public section\n")
    w("/-!\n# The icosahedral rotation group in the 5-fold frame (generated)\n\n"
      "Generated by `scripts/snub_ico_group.py`; do not edit. See that script for\n"
      "the construction and the numbering. Entries are in units of 1/20.\n-/\n")
    w("namespace Noperthedron.Nopert231\n")
    w("/-- The 60 rotations over K, times 20 (element 0 is the identity). A balanced\n"
      "`if` tree keeps the kernel's lookups short. -/")
    w("def icoEntry (n : Nat) : M3 :=\n  " + tree(0, 60, 2) + "\n")
    w("/-- The generators Rz(72°), Rx(180°) and the 72° rotation about the 5-fold\n"
      "axis at azimuth 54°. -/")
    w("def icoGen : List Nat := " + nat_list(gens) + "\n")
    w("/-- `icoGenMul.getD g [] |>.getD k 0` is the index of g * icoGen[k]. -/")
    w("def icoGenMul : List (List Nat) := [\n" +
      ",\n".join("  " + nat_list([table[g][x] for x in gens]) for g in range(60)) + "]\n")
    w("/-- Element h > 0 is icoBfsParent[h] * icoGen[icoBfsGen[h]], with a smaller parent. -/")
    w("def icoBfsParent : List Nat := " + nat_list(parent) + "\n")
    w("def icoBfsGen : List Nat := " + nat_list(parent_gen) + "\n")
    w(f"/-- Rz(72°). -/\ndef icoRzIndex : Nat := {rz}\n")
    w(f"/-- Rx(180°) = diag(1, -1, -1). -/\ndef icoRxIndex : Nat := {rx}\n")
    w("/-- The 12 rotations by ±72° about the six 5-fold axes, in the order of\n"
      "nopert229/symmetry_neighbors.h. -/")
    w("def icoNeighborIndex : List Nat := " + nat_list(neighbors) + "\n")
    w("/-- vertex i = icoEntry (vertexElement[i]) / 20 * vertex 0. -/")
    w("def vertexElementIndex : List Nat := " + nat_list(elem) + "\n")
    inv_elem = [elem.index(k) for k in range(60)]
    w("/-- The inverse of `vertexElementIndex`. -/")
    w("def elementVertexIndex : List Nat := " + nat_list(inv_elem) + "\n")
    inverse = [index[transpose(g)] for g in group]
    w("/-- The inverse (transpose) of each element. -/")
    w("def icoInverseIndex : List Nat := " + nat_list(inverse) + "\n")
    w("end Noperthedron.Nopert231")
    args.out.write_text("\n".join(out) + "\n", encoding="utf-8")
    den = 1
    for g in group:
        for row in g:
            for x in row:
                for q in x.v:
                    den = math.lcm(den, q.denominator)
    print(f"wrote {args.out}: 60 elements, Rz = {rz}, Rx = {rx}, neighbors {neighbors}, "
          f"common denominator {den}")


if __name__ == "__main__":
    main()
