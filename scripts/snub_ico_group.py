#!/usr/bin/env python3
"""Generate Noperthedron/PentagonalHexecontahedron/IcoGroupData.lean: the icosahedral rotation
group I in the snub dodecahedron's 5-fold frame, exactly over
K = Q(sqrt5, s), s = sin 72 deg (IcoField.lean; README.md, "Frame and exact algebra").

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
                    the order of the C++ search's symmetry_neighbors.h (the C++ search
                    journals refer to neighbor n)
  icoInverseIndex   each element's inverse (its transpose)
  elementVertexIndex  the inverse of vertexElementIndex
  icoNeighborNum    the C++ search's rounded neighbors (numerators over 10^12),
                    copied from symmetry_neighbors.h so that the Lean prune
                    rows use exactly the same matrices
  vertexElementIndex  the element g with vertex i = g * vertex 0, from the
                    model's vertices (snub_model.txt); the snub
                    dodecahedron's vertices are a free I-orbit

The script checks, in exact arithmetic, that the 60 matrices are orthogonal
with determinant 1, and numerically that the neighbors and the vertex
elements match the model. Lean re-decides the algebraic facts.

Usage: python3 scripts/snub_ico_group.py [--model_dir DIR] [--out FILE]
(--model_dir defaults to $MODEL_DIR, the C++ pipeline directory.)
"""

from __future__ import annotations

import argparse
import itertools
import math
import os
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


def k_inverse(x):
    """1/x in K, x = A + B s with A, B in Q(sqrt5)."""
    a, b, c, d = x.v

    def qmul(p, q):
        return (p[0] * q[0] + 5 * p[1] * q[1], p[0] * q[1] + p[1] * q[0])

    def qinv(p):
        n = p[0] ** 2 - 5 * p[1] ** 2
        return (p[0] / n, -p[1] / n)

    A, B = (a, b), (c, d)
    s2 = (F(5, 8), F(1, 8))
    bb = qmul(qmul(B, B), s2)
    den = qmul(A, A)
    den_inv = qinv((den[0] - bb[0], den[1] - bb[1]))
    na, nb = qmul(A, den_inv), qmul(B, den_inv)
    return K(na[0], na[1], -nb[0], -nb[1])


def k_det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def view_reduction_data(group, triangle):
    """Data for the view reduction modulo Ih into the triangle T
    (S.md §2.3, reduction 2).

    The chamber's three walls are the mirrors of half-turns H_i in I (a
    mirror is -(half-turn about its normal)). With c a rational interior
    point, the Dirichlet choice of the view gives <w, c + H_i c> >= 0. Each
    homogeneous wall m_j of T (w in cone(T) iff <w, m_j> >= 0) is written as
    sum_i lambda_ji (c + H_i c), lambda >= 0, exactly in K. Returns integer
    data: the walls (group indices), C = 100 c, D_i = 2000 (c + H_i c) in
    IcoZ coordinates, the integer normals m_j, scales N_j and Lambda_ji (IcoZ)
    with N_j m_j = sum_i Lambda_ji D_i."""
    deg = math.pi / 180
    pole = (0.0, 0.0, 1.0)
    polar5 = math.acos(1 / math.sqrt(5))
    axis5 = (math.sin(polar5) * math.cos(54 * deg), math.sin(polar5) * math.sin(54 * deg),
             math.cos(polar5))
    normals = [(math.cos(108 * deg), math.sin(108 * deg), 0.0),
               (math.cos(144 * deg), math.sin(144 * deg), 0.0),
               tuple(p - q for p, q in zip(pole, axis5))]
    walls = []
    for n in normals:
        norm = math.sqrt(sum(x * x for x in n))
        n = [x / norm for x in n]
        hits = []
        for k, g in enumerate(group):
            if g[0][0] + g[1][1] + g[2][2] != K(-1):
                continue
            # A half-turn about n maps n to n.
            gn = [sum(g[i][j].f() * n[j] for j in range(3)) for i in range(3)]
            if all(abs(gn[i] - n[i]) < 1e-9 for i in range(3)):
                hits.append(k)
        if len(hits) != 1:
            raise SystemExit(f"wall half-turn: {len(hits)} matches")
        walls.append(hits[0])
    for w in walls:
        if transpose(group[w]) != group[w]:
            raise SystemExit("a wall half-turn is not symmetric")
    c = [F(1, 4), F(9, 50), F(19, 20)]
    ck = [K(x) for x in c]
    d = [[ck[i] + sum((group[w][i][j] * ck[j] for j in range(3)), Z) for i in range(3)]
         for w in walls]
    # Homogeneous walls of cone(T): m = corner_k x corner_l, positive on the third.
    m_list = []
    for k, l, o in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
        a, b = triangle[k], triangle[l]
        m = [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
        if sum(x * y for x, y in zip(m, triangle[o])) < 0:
            m = [-x for x in m]
        den = 1
        for x in m:
            den = math.lcm(den, x.denominator)
        m = [x * den for x in m]
        g = 0
        for x in m:
            g = math.gcd(g, int(x))
        m_list.append([int(x) // g for x in m])
    cols = [[d[i][r] for i in range(3)] for r in range(3)]
    det_inv = k_inverse(k_det3(cols))
    lam = []
    for m in m_list:
        mk = [K(x) for x in m]
        row = []
        for i in range(3):
            mi = [[mk[r] if col == i else cols[r][col] for col in range(3)] for r in range(3)]
            row.append(k_det3(mi) * det_inv)
        for r in range(3):
            if sum((row[i] * d[i][r] for i in range(3)), Z) != mk[r]:
                raise SystemExit("Farkas solve failed")
        if any(x.f() < 0 for x in row):
            raise SystemExit("T is not a superset of the chamber (negative multiplier)")
        lam.append(row)
    # Integer scaling: D_i = 2000 d_i; N_j m_j = sum_i Lambda_ji D_i with
    # Lambda_ji = N_j lambda_ji / 2000.
    dz = [[[int(q * 2000) for q in x.v] for x in di] for di in d]
    for di in d:
        for x in di:
            if any((q * 2000).denominator != 1 for q in x.v):
                raise SystemExit("D_i is not integral")
    scales, lz = [], []
    for row in lam:
        den = 1
        for x in row:
            for q in x.v:
                den = math.lcm(den, (q / 2000).denominator)
        scales.append(den)
        lz.append([[int(q / 2000 * den) for q in x.v] for x in row])
    return walls, [int(x * 100) for x in c], dz, m_list, scales, lz


def wikipedia_data(group, index, verts, verts_elem):
    """Wikipedia's snub dodecahedron (Snub_dodecahedron, Cartesian
    coordinates): the orbit of p = (phi^2 - phi^2 xi, -phi^3 + phi xi + 2 phi
    xi^2, xi), xi the real root of x^3 + 2x^2 - phi^2, under the rotations
    generated by M1 (2 pi/5 about (0, 1, phi)) and M2 (cyclic shift).

    Returns the 60 matrices of that group (breadth-first by left
    multiplication with the generators, so each is a word applied to p),
    the BFS parents, left multiplication by the generators, the exact
    rotation T (over K) taking Wikipedia's normalized vertex S_k p/|p| to our
    vertex k-correspondent, with T S_g T^T in our group, the correspondence
    tau (our vertex i = T S_tau(i) p up to scale), and xi, |p| to 60 digits."""
    from decimal import Decimal, getcontext
    getcontext().prec = 80
    r5 = Decimal(5).sqrt()
    phi_d = (1 + r5) / 2
    lo, hi = Decimal(0), Decimal(1)
    for _ in range(260):
        m = (lo + hi) / 2
        if m ** 3 + 2 * m * m - phi_d ** 2 < 0:
            lo = m
        else:
            hi = m
    xi_d = lo
    p_d = [phi_d ** 2 - phi_d ** 2 * xi_d, -phi_d ** 3 + phi_d * xi_d + 2 * phi_d * xi_d ** 2, xi_d]
    pnorm_d = sum(x * x for x in p_d).sqrt()
    half, kphi2 = K(F(1, 2)), K(F(1, 4), F(1, 4))  # 1/2, phi/2
    inv2phi = K(F(-1, 4), F(1, 4))  # 1/(2 phi)
    m1 = ((inv2phi, -kphi2, half), (kphi2, half, inv2phi), (-half, inv2phi, kphi2))
    m2 = ((Z, Z, ONE), (ONE, Z, Z), (Z, ONE, Z))
    gens = [m1, m2]
    wiki, widx = [IDENTITY], {IDENTITY: 0}
    parent, parent_gen = [0], [0]
    i = 0
    while i < len(wiki):
        for k, g in enumerate(gens):
            h = mm(g, wiki[i])
            if h not in widx:
                widx[h] = len(wiki)
                wiki.append(h)
                parent.append(i)
                parent_gen.append(k)
        i += 1
    if len(wiki) != 60:
        raise SystemExit(f"Wikipedia group has {len(wiki)} elements")
    left = [[widx[mm(g, s)] for s in wiki] for g in gens]
    # Numeric correspondence: T maps p/|p| to our vertex 0 and the nearest
    # neighbors to neighbors; then recognize T's entries in K.
    pf = [float(x) for x in p_d]
    pn = float(pnorm_d)
    A = [[sum(g[r][c].f() * pf[c] for c in range(3)) / pn for r in range(3)] for g in wiki]

    def nearest(P, i):
        return [j for _, j in sorted((math.dist(P[i], P[j]), j) for j in range(60) if j != i)[:5]]

    def det3f(m):
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))

    def inv3f(m):
        d = det3f(m)
        return [[(m[(j + 1) % 3][(i + 1) % 3] * m[(j + 2) % 3][(i + 2) % 3]
                  - m[(j + 1) % 3][(i + 2) % 3] * m[(j + 2) % 3][(i + 1) % 3]) / d
                 for j in range(3)] for i in range(3)]

    def recognize(x):
        for c in range(-20, 21):
            for d in range(-20, 21):
                y = 20 * x - c * S72 - d * S72 * R5
                for b in range(-20, 21):
                    a = y - b * R5
                    if abs(a - round(a)) < 1e-7:
                        return K(F(round(a), 20), F(b, 20), F(c, 20), F(d, 20))
        return None

    na, nb = nearest(A, 0), nearest(verts, 0)
    T = None
    for a1, a2 in itertools.permutations(nb, 2):
        X = [A[0], A[na[0]], A[na[1]]]
        Y = [verts[0], verts[a1], verts[a2]]
        XT = [[X[c][r] for c in range(3)] for r in range(3)]
        YT = [[Y[c][r] for c in range(3)] for r in range(3)]
        XI = inv3f(XT)
        Tf = [[sum(YT[r][k] * XI[k][c] for k in range(3)) for c in range(3)] for r in range(3)]
        if abs(det3f(Tf) - 1) > 1e-6:
            continue
        TA = [[sum(Tf[r][c] * a[c] for c in range(3)) for r in range(3)] for a in A]
        if all(min(math.dist(t, b) for b in verts) < 1e-8 for t in TA):
            T = tuple(tuple(recognize(Tf[r][c]) for c in range(3)) for r in range(3))
            break
    if T is None or any(x is None for row in T for x in row):
        raise SystemExit("no exact rotation from Wikipedia's snub to the model")
    if mm(T, transpose(T)) != IDENTITY or det(T) != ONE:
        raise SystemExit("T is not a rotation")
    # tau(i): our vertex i = g_i v0 with v0 = T p; g_i T = T S_tau(i).
    tau = []
    for i in range(60):
        g = group[verts_elem[i]]
        h = mm(transpose(T), mm(g, T))
        if h not in widx:
            raise SystemExit("T does not conjugate the groups")
        tau.append(widx[h])
    if sorted(tau) != list(range(60)):
        raise SystemExit("tau is not a bijection")
    return wiki, parent, parent_gen, left, T, tau, xi_d, pnorm_d


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
    ap.add_argument("--model_dir", type=Path, default=Path(os.environ["MODEL_DIR"]) if os.environ.get("MODEL_DIR") else None)
    ap.add_argument("--model_file", default="ph_model.txt",
                    help="the solid's model file, in --model_dir (vertex slots and seeds)")
    ap.add_argument("--out", type=Path, default=REPO / "Noperthedron/PentagonalHexecontahedron/IcoGroupData.lean")
    args = ap.parse_args()
    if args.model_dir is None:
        raise SystemExit("pass --model_dir or set MODEL_DIR to the C++ pipeline directory")

    group, index, table = generate()

    hdr = (args.model_dir / "symmetry_neighbors.h").read_text()
    nums = [[int(x) for x in r.split(",")] for r in re.findall(r"\{([-0-9, ]+)\}", hdr)]
    nums = [r for r in nums if len(r) == 9]
    if "SYMMETRY_NEIGHBOR_DENOM = 1000000000000;" not in hdr:
        raise SystemExit("symmetry_neighbors.h: expected denominator 10^12")
    rows = [[x / 1e12 for x in r] for r in nums]
    if len(rows) != 12:
        raise SystemExit(f"expected 12 neighbors in symmetry_neighbors.h, got {len(rows)}")
    neighbors = []
    for r in rows:
        hits = [k for k, g in enumerate(group) if match(g, r, 1e-11)]
        if len(hits) != 1:
            raise SystemExit(f"neighbor matches {len(hits)} elements")
        neighbors.append(hits[0])

    verts = []
    for line in (args.model_dir / "snub_model.txt").read_text().splitlines():
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

    # The solid's vertex slots (the model file), as I-orbits. Orbit o has a
    # base slot b_o (its first slot) and stabilizer Stab_o = {h : h b_o = b_o};
    # slot i is g_i * b_{orbit i}, with g_i = slotElem[i]. A point on the C5
    # axis is listed in several slots, one per C5 orbit.
    seeds = None
    pts = []
    for line in (args.model_dir / args.model_file).read_text().splitlines():
        t = line.split()
        if t and t[0] == "seeds":
            seeds = int(t[1])
        elif t and t[0] == "vertex":
            pts.append([float(x) for x in t[2:5]])
    nslots = len(pts)
    if seeds is None or nslots != 5 * seeds:
        raise SystemExit(f"{args.model_file}: expected 5 * seeds vertex slots")

    def act(k, v):
        m = numeric(group[k])
        return [sum(m[3 * i + j] * v[j] for j in range(3)) for i in range(3)]

    def same(u, v):
        return max(abs(a - b) for a, b in zip(u, v)) < 1e-12

    slot_orbit = [None] * nslots
    bases, stabs = [], []
    for i in range(nslots):
        if slot_orbit[i] is not None:
            continue
        o = len(bases)
        bases.append(i)
        stabs.append([k for k in range(60) if same(act(k, pts[i]), pts[i])])
        for k in range(60):
            q = act(k, pts[i])
            for j in range(nslots):
                if same(q, pts[j]):
                    if slot_orbit[j] not in (None, o):
                        raise SystemExit("orbits overlap")
                    slot_orbit[j] = o
    if any(o is None for o in slot_orbit):
        raise SystemExit("a slot is in no orbit")
    distinct = sum(1 for i in range(nslots) if not any(same(pts[i], pts[j]) for j in range(i)))
    if sum(60 // len(st) for st in stabs) != distinct:
        raise SystemExit("orbit sizes do not add up to the number of points")
    slot_elem = []
    for i in range(nslots):
        if i < seeds:
            b = pts[bases[slot_orbit[i]]]
            hits = [k for k in range(60) if same(act(k, b), pts[i])]
            if not hits:
                raise SystemExit(f"slot {i}: no element")
            slot_elem.append(hits[0])
        else:
            slot_elem.append(table[rz][slot_elem[i - seeds]])
            if slot_orbit[i] != slot_orbit[i - seeds] or not same(
                    act(slot_elem[i], pts[bases[slot_orbit[i]]]), pts[i]):
                raise SystemExit(f"slot {i} is not Rz * slot {i - seeds}")
    # For each orbit o and element k: a slot j of o and h in Stab_o with
    # G_k = G_{slotElem j} * G_h (so G_k b_o is slot j).
    orbit_slot, orbit_stab = [], []
    for o, b in enumerate(bases):
        sl, st = [], []
        for k in range(60):
            q = act(k, pts[b])
            j = next(j for j in range(nslots) if slot_orbit[j] == o and same(q, pts[j]))
            h = index[mm(transpose(group[slot_elem[j]]), group[k])]
            if h not in stabs[o]:
                raise SystemExit("slot table: not a stabilizer element")
            sl.append(j)
            st.append(h)
        orbit_slot.append(sl)
        orbit_stab.append(st)

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
    w("module\n\npublic import Noperthedron.PentagonalHexecontahedron.IcoField\n\n@[expose] public section\n")
    w("/-!\n# The icosahedral rotation group in the 5-fold frame (generated)\n\n"
      "Generated by `scripts/snub_ico_group.py`; do not edit. See that script for\n"
      "the construction and the numbering. Entries are in units of 1/20.\n-/\n")
    w("namespace Noperthedron.PentagonalHexecontahedron\n")
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
      "the C++ search's symmetry_neighbors.h. -/")
    w("def icoNeighborIndex : List Nat := " + nat_list(neighbors) + "\n")
    w("/-- The rounded neighbors of the C++ search's symmetry_neighbors.h (its\n"
      "icosahedral prune), row-major numerators over 10^12. -/")
    w("def icoNeighborNum : List (List Int) := [\n" +
      ",\n".join("  [" + ", ".join(str(x) for x in r) + "]" for r in nums) + "]\n")
    w(f"/-! ### The solid's vertex slots as I-orbits ({args.model_file}) -/\n")
    w(f"/-- The number of I-orbits. -/\ndef orbitCount : Nat := {len(bases)}\n")
    w("/-- The I-orbit of each vertex slot. -/")
    w("def vertexOrbitIndex : List Nat := " + nat_list(slot_orbit) + "\n")
    w("/-- The base slot of each orbit. -/")
    w("def orbitBaseSlot : List Nat := " + nat_list(bases) + "\n")
    w("/-- The stabilizer of each orbit's base point. -/")
    w("def orbitStabilizer : List (List Nat) := [" + ", ".join(nat_list(st) for st in stabs) + "]\n")
    w("/-- slot i = icoEntry (vertexElement[i]) / 20 * (the base point of its orbit). -/")
    w("def vertexElementIndex : List Nat := " + nat_list(slot_elem) + "\n")
    w("/-- `orbitSlot[o][k]`: a slot j of orbit o with element k = vertexElement[j] *\n"
      "`orbitStab[o][k]`, a stabilizer element. -/")
    w("def orbitSlot : List (List Nat) := [\n" +
      ",\n".join("  " + nat_list(r) for r in orbit_slot) + "]\n")
    w("def orbitStab : List (List Nat) := [\n" +
      ",\n".join("  " + nat_list(r) for r in orbit_stab) + "]\n")
    inverse = [index[transpose(g)] for g in group]
    w("/-- The inverse (transpose) of each element. -/")
    w("def icoInverseIndex : List Nat := " + nat_list(inverse) + "\n")
    tri_line = next(l for l in (args.model_dir / "snub_model.txt").read_text().splitlines()
                    if l.startswith("view_triangle "))
    vals = [F(x) for x in tri_line.split()[1:]]
    triangle = [vals[0:3], vals[3:6], vals[6:9]]
    walls, cz, dz, m_list, scales, lz = view_reduction_data(group, triangle)

    def lean_icoz(v):
        return "⟨" + ", ".join(str(x) for x in v) + "⟩"

    w("/-! ### View reduction modulo Ih into the triangle T (S.md §2.3) -/\n")
    w("/-- T, from the model file snub_model.txt: corners on x + y + z = 1. -/")
    w("def icoViewTriangleCorners : List (List ℚ) := [" + ", ".join(
        "[" + ", ".join(f"{q.numerator}/{q.denominator}" for q in corner) + "]"
        for corner in triangle) + "]\n")
    w("/-- The half-turns whose mirrors (-H) are the chamber's walls. -/")
    w("def viewWallIndex : List Nat := " + nat_list(walls) + "\n")
    w("/-- 100 c, c the rational interior point of the chamber. -/")
    w("def viewCenter100 : List Int := " + nat_list(cz) + "\n")
    w("/-- D_i = 2000 (c + H_i c), in `IcoZ` coordinates. -/")
    w("def viewWallVector : List (List IcoZ) := [" + ", ".join(
        "[" + ", ".join(lean_icoz(x) for x in di) + "]" for di in dz) + "]\n")
    w("/-- The homogeneous walls m_j of cone(T): w ∈ cone(T) iff ⟨w, m_j⟩ ≥ 0. -/")
    w("def viewTriangleNormal : List (List Int) := " +
      "[" + ", ".join(nat_list(m) for m in m_list) + "]\n")
    w("/-- N_j m_j = Σ_i Λ_ji D_i with Λ_ji ≥ 0 (Farkas multipliers, exact in K). -/")
    w("def viewFarkasScale : List Nat := " + nat_list(scales) + "\n")
    w("def viewFarkas : List (List IcoZ) := [" + ", ".join(
        "[" + ", ".join(lean_icoz(x) for x in row) + "]" for row in lz) + "]\n")
    wiki, wparent, wpgen, wleft, frame_t, tau, xi_d, pnorm_d = wikipedia_data(group, index, verts, elem)
    from decimal import Decimal
    scale_q = F(int(((Decimal(1) - Decimal(1) / 10 ** 9) / pnorm_d) * 10 ** 40), 10 ** 40)
    # xi's enclosure must be wider than the sqrt5 bounds' effect (~1e-26):
    # [floor(xi 1e24) - 1, + 3] / 1e24.
    xi_lo_num = int(xi_d * 10 ** 24) - 1

    def wtree(lo, hi, indent):
        if hi - lo == 1:
            return m3(wiki[lo])
        mid = (lo + hi) // 2
        pad = " " * (indent + 2)
        return (f"if n < {mid} then\n{pad}{wtree(lo, mid, indent + 2)}\n"
                f"{' ' * indent}else\n{pad}{wtree(mid, hi, indent + 2)}")

    w("/-! ### Wikipedia's snub dodecahedron (WikipediaSnub.lean) -/\n")
    w("/-- The rotation group generated by Wikipedia's M₁ and M₂, times 20; element\n"
      "0 is the identity, and element h > 0 is `wikiGen[wikiBfsGen[h]] * element\n"
      "wikiBfsParent[h]` (left multiplication, so each is a word applied to p). -/")
    w("def wikiEntry (n : Nat) : M3 :=\n  " + wtree(0, 60, 2) + "\n")
    w("def wikiBfsParent : List Nat := " + nat_list(wparent) + "\n")
    w("def wikiBfsGen : List Nat := " + nat_list(wpgen) + "\n")
    w("/-- `wikiLeftMul[k][g]`: the index of generator k (M₁, M₂) times element g. -/")
    w("def wikiLeftMul : List (List Nat) := [" + ", ".join(nat_list(r) for r in wleft) + "]\n")
    w("/-- The rotation T (times 20) from Wikipedia's frame to the 5-fold frame:\n"
      "our vertex i is (scale) · T · (element `vertexWikiIndex[i]`) · p. -/")
    w("def snubFrameT : M3 := " + m3(frame_t) + "\n")
    w("def vertexWikiIndex : List Nat := " + nat_list(tau) + "\n")
    w("def wikiVertexIndex : List Nat := " + nat_list([tau.index(k) for k in range(60)]) + "\n")
    w("/-- ξ (Wikipedia's, the real root of x³ + 2x² − φ²) lies in\n"
      "[xiWLoNum, xiWLoNum + 3] / 10²⁴. -/")
    w(f"def xiWLoNum : Nat := {xi_lo_num}\n")
    w("/-- The scale: (1 − 10⁻⁹)/|p| rounded down to a multiple of 10⁻⁴⁰ (the rational\n"
      "model is the unit-circumradius solid scaled by 1 − 10⁻⁹). -/")
    w(f"def snubScaleNum : Nat := {scale_q.numerator * (10 ** 40 // scale_q.denominator)}\n")
    w("end Noperthedron.PentagonalHexecontahedron")
    args.out.write_text("\n".join(out) + "\n", encoding="utf-8")
    den = 1
    for g in group:
        for row in g:
            for x in row:
                for q in x.v:
                    den = math.lcm(den, q.denominator)
    print(f"wrote {args.out}: 60 elements, Rz = {rz}, Rx = {rx}, neighbors {neighbors}, "
          f"common denominator {den}; {args.model_file}: {nslots} slots, orbits of sizes "
          f"{[60 // len(st) for st in stabs]} (bases {bases})")


if __name__ == "__main__":
    main()
