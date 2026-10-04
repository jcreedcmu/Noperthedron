#!/usr/bin/env python3
"""Generate Noperthedron/PentagonalHexecontahedron/PHStatementData.lean: the certificate
data for Statement.lean, which identifies the pentagonal hexecontahedron (the
facet poles of Wikipedia's snub dodecahedron) with an `IModel`.

Notation: S = {S_g p : g < 60} is Wikipedia's snub dodecahedron (S_g =
`wiki g`, IcoGroupData.lean). The pole of a face through vertices a, b, c is
the y with <a, y> = <b, y> = <c, y> = 1. For x in S let
  D(a, b, c; x) = det(b - a, c - a, x - a),
so that det(a, b, c) (<x, y> - 1) = D(a, b, c; x) (Cramer).

Emitted:
  snubBoxLoZ/HiZ     boxes around the 60 vertices of S, times 2^64 (Lean
                     checks that they contain interval images of p's box)
  wikiInvIndex       inverses in Wikipedia's group
  pairCert           for every ordered pair (j, k) of vertices, a reason why
                     no facet pole y has <p, y> = <S_j p, y> = <S_k p, y> = 1
                     with p, S_j p, S_k p affinely independent, unless it is
                     one of ours:
                       [0]            degenerate (j = 0, k = 0 or j = k), or
                                      j > k (the pair (k, j) is used);
                       [1, x1, x2]    D(x1) > 0 > D(x2): the plane through
                                      the three has vertices on both sides;
                       [2, o, h, m0, mj, mk]  the three are vertices m0, mj,
                                      mk of S_h (base face o), i.e.
                                      S_h^-1 S_0 = S_m0 etc., and
                                      det(p, S_j p, S_k p) /= 0.
  baseFace           per orbit o, the vertices of the base face at p (the
                     pentagon about M1's axis, the triangle about a 3-fold
                     axis, a generic triangle); the first three define the
                     pole y_o
  baseStab           per orbit, the elements of Wikipedia's group fixing y_o
  orbitWiki          per orbit, g_o: the model's base point is
                     phScale * T * S_{g_o} y_o
  stabConj           per orbit o and h < 60 (ico numbering): for h in the
                     model's stabilizer of orbit o, [sigma, q, tau] with
                     ico h T = T S_sigma and S_sigma S_{g_o} = S_q = S_{g_o} S_tau,
                     tau in baseStab ([0, 0, 0] for other h)
  slotSigma,         per vertex slot i: ico(vElem i) T = T S_sigma_i and
  slotWiki           S_sigma_i S_{g_o} = S_{w_i}
  orbitCover         per orbit o and g < 60: [i, tau] with S_g = S_{w_i} S_tau
  phScaleNum         the scale (times 10^40): scale * |p| (ph_model.py's
                     scale times Wikipedia's |p|; T maps p/|p| to the model's
                     snub frame)

Usage: python3 scripts/ph_statement_data.py [--model_dir DIR]
"""

import argparse
import importlib.util
import os
import re
import sys
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from pathlib import Path

getcontext().prec = 80
HERE = Path(__file__).resolve().parent
REPO = HERE.parent
spec = importlib.util.spec_from_file_location("sig", HERE / "snub_ico_group.py")
sig = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sig)


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model_dir", type=Path,
                    default=Path(os.environ["MODEL_DIR"]) if os.environ.get("MODEL_DIR") else None)
    ap.add_argument("--out", type=Path, default=REPO / "Noperthedron/PentagonalHexecontahedron/PHStatementData.lean")
    args = ap.parse_args()
    if args.model_dir is None:
        raise SystemExit("pass --model_dir or set MODEL_DIR")

    group, index, table = sig.generate()
    # The snub model's vertices and elements (as snub_ico_group.py), for T.
    verts = []
    for line in (args.model_dir / "snub_model.txt").read_text().splitlines():
        if line.startswith("vertex "):
            verts.append([float(x) for x in line.split()[2:5]])
    v0 = verts[0]
    elem = []
    for v in verts:
        hits = [k for k, g in enumerate(group)
                if all(abs(sum(sig.numeric(g)[3 * i + j] * v0[j] for j in range(3)) - v[i]) < 1e-12
                       for i in range(3))]
        elem.append(hits[0])
    wiki, wparent, wpgen, wleft, T, tau, xi_d, pnorm_d = sig.wikipedia_data(group, index, verts, elem)
    widx = {g: i for i, g in enumerate(wiki)}
    mm, tr = sig.mm, sig.transpose

    # Exact-enough numerics (80 digits) for the vertices of S.
    r5 = D(5).sqrt()
    s72 = ((5 + r5) / 8).sqrt()

    def kd(x):
        a, b, c, d = x.v
        return (D(a.numerator) / D(a.denominator) + D(b.numerator) / D(b.denominator) * r5 +
                D(c.numerator) / D(c.denominator) * s72 +
                D(d.numerator) / D(d.denominator) * s72 * r5)

    phi = (1 + r5) / 2
    p = [phi ** 2 - phi ** 2 * xi_d, -phi ** 3 + phi * xi_d + 2 * phi * xi_d ** 2, xi_d]

    def apply(M, v):
        return [sum(kd(M[i][j]) * v[j] for j in range(3)) for i in range(3)]

    S = [apply(g, p) for g in wiki]

    def sub(a, b): return [x - y for x, y in zip(a, b)]
    def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
    def dot(a, b): return sum(x * y for x, y in zip(a, b))
    def det(a, b, c): return dot(a, cross(b, c))
    def Dx(a, b, c, x): return det(sub(b, a), sub(c, a), sub(x, a))

    # Boxes: the value +- 2^-60, rounded outward to multiples of 2^-64.
    def box(x):
        lo = F(int((x - D(2) ** -60) * 2 ** 64) - 1, 2 ** 64)
        hi = F(int((x + D(2) ** -60) * 2 ** 64) + 1, 2 ** 64)
        return lo, hi

    boxes = [[box(c) for c in v] for v in S]
    inv = [widx[tr(g)] for g in wiki]

    # Faces at p, and the base faces.
    m1_orbit = [0]
    for _ in range(4):
        m1_orbit.append(wleft[0][m1_orbit[-1]])
    assert m1_orbit[-1] != 0 and wleft[0][m1_orbit[-1]] == 0, m1_orbit
    pentagon = m1_orbit
    facet_pairs = {}
    for j in range(1, 60):
        for k in range(j + 1, 60):
            ds = [Dx(S[0], S[j], S[k], S[x]) for x in range(60)]
            if max(ds) > D(10) ** -40 and min(ds) < -D(10) ** -40:
                continue
            facet_pairs[(j, k)] = ds
    faces = []
    for (j, k) in facet_pairs:
        on = tuple(sorted({0, j, k} | {x for x in range(60) if abs(facet_pairs[(j, k)][x]) < D(10) ** -40}))
        if on not in faces:
            faces.append(on)
    assert len(faces) == 5, faces
    assert tuple(sorted(pentagon)) in faces

    def stab_of(face):
        # Elements mapping the face's vertex set to itself.
        out = []
        for h in range(60):
            img = {widx[mm(wiki[h], wiki[m])] for m in face}
            if img == set(face):
                out.append(h)
        return out

    tri3 = next(f for f in faces if len(f) == 3 and len(stab_of(f)) == 3)
    generic = next(f for f in faces if len(f) == 3 and len(stab_of(f)) == 1)
    # Orbit order of the model (IcoGroupData: orbitStabilizer sizes).
    data = (REPO / "Noperthedron/PentagonalHexecontahedron/IcoGroupData.lean").read_text()

    def lean_nat_list(name):
        return [int(x) for x in re.search(rf"def {name} : List Nat := \[([^\]]*)\]", data).group(1).split(",")]

    stabs = [[int(x) for x in s.split(",")] for s in
             re.findall(r"\[([0-9, ]+)\]", re.search(r"def orbitStabilizer : List \(List Nat\) := (.*)", data).group(1))]
    vorbit = lean_nat_list("vertexOrbitIndex")
    velem = lean_nat_list("vertexElementIndex")
    bases = lean_nat_list("orbitBaseSlot")
    by_size = {5: pentagon, 3: list(tri3), 1: list(generic)}
    base_face = [by_size[len(st)] for st in stabs]
    base_stab = [stab_of(f) if len(f) == 3 else pentagon for f in base_face]

    def pole(a, b, c):
        n = [x + y + z for x, y, z in zip(cross(b, c), cross(c, a), cross(a, b))]
        d = det(a, b, c)
        return [x / d for x in n]

    ys = [pole(S[f[0]], S[f[1]], S[f[2]]) for f in base_face]

    # The PH model's rational vertices and the scale.
    ph = (args.model_dir / "ph_model.txt").read_text().splitlines()
    ratv = []
    for line in ph:
        t = line.split()
        if t and t[0] == "rational_vertex":
            ratv.append([D(F(x).numerator) / D(F(x).denominator) for x in t[2:5]])
    # scale: the model's base vertex 0 over T y.
    Ty0 = apply(T, ys[0])
    nrm = lambda v: dot(v, v).sqrt()
    # orbitWiki: g_o with s T S_g y_o close to the base slot (s fitted on orbit 0).
    def fit(o, s):
        target = ratv[bases[o]]
        best = None
        for g in range(60):
            v = [s * x for x in apply(T, apply(wiki[g], ys[o]))]
            e = nrm(sub(v, target))
            if best is None or e < best[0]:
                best = (e, g)
        return best

    s_guess = nrm(ratv[bases[0]]) / nrm(Ty0)
    s_q = F(int(s_guess * D(10) ** 40), 10 ** 40)
    s = D(s_q.numerator) / D(s_q.denominator)
    orbit_wiki = []
    for o in range(len(bases)):
        e, g = fit(o, s)
        assert e < D(10) ** -17, (o, e)
        orbit_wiki.append(g)

    # T conjugation: ico h T = T S_sigma(h).
    def sigma(h):
        return widx[mm(tr(T), mm(group[h], T))]

    stab_conj = []
    for o, st in enumerate(stabs):
        rows = []
        for h in range(60):
            if h not in st:
                rows.append([0, 0, 0])
                continue
            sg = sigma(h)
            q = widx[mm(wiki[sg], wiki[orbit_wiki[o]])]
            t_ = widx[mm(tr(wiki[orbit_wiki[o]]), wiki[q])]
            assert t_ in base_stab[o], (o, h, t_)
            rows.append([sg, q, t_])
        stab_conj.append(rows)
    slot_sigma = [sigma(velem[i]) for i in range(len(vorbit))]
    slot_wiki = [widx[mm(wiki[slot_sigma[i]], wiki[orbit_wiki[vorbit[i]]])] for i in range(len(vorbit))]
    max_err = 0
    for i in range(len(vorbit)):
        v = [s * x for x in apply(T, apply(wiki[slot_wiki[i]], ys[vorbit[i]]))]
        max_err = max(max_err, nrm(sub(v, ratv[i])))
    assert max_err < D(10) ** -17, max_err
    orbit_cover = []
    for o in range(len(bases)):
        rows = []
        for g in range(60):
            hit = None
            for i in range(len(vorbit)):
                if vorbit[i] != o:
                    continue
                t_ = widx[mm(tr(wiki[slot_wiki[i]]), wiki[g])]
                if t_ in base_stab[o]:
                    hit = [i, t_]
                    break
            assert hit is not None
            rows.append(hit)
        orbit_cover.append(rows)

    # Pair certificates.
    certs = []
    margin = None
    for j in range(60):
        for k in range(60):
            if j == 0 or k == 0 or j >= k:
                certs.append([0])  # degenerate, or the pair (k, j) instead
                continue
            ds = [Dx(S[0], S[j], S[k], S[x]) for x in range(60)]
            x1 = max(range(60), key=lambda x: ds[x])
            x2 = min(range(60), key=lambda x: ds[x])
            if ds[x1] > D(10) ** -40 and ds[x2] < -D(10) ** -40:
                certs.append([1, x1, x2])
                m = min(ds[x1], -ds[x2])
                margin = m if margin is None else min(margin, m)
                continue
            # A face: find (o, h) with {0, j, k} in S_h(base face o).
            found = None
            for o, f in enumerate(base_face):
                for h in range(60):
                    img = {widx[mm(wiki[h], wiki[m])]: m for m in f}
                    if 0 in img and j in img and k in img:
                        found = [2, o, h, img[0], img[j], img[k]]
                        break
                if found:
                    break
            assert found, (j, k)
            assert abs(det(S[0], S[j], S[k])) > D(10) ** -3
            certs.append(found)
    print(f"{sum(1 for c in certs if c[0] == 1)} two-sided pairs (min margin {float(margin):.4f}), "
          f"{sum(1 for c in certs if c[0] == 2)} face pairs; faces at p {faces}; "
          f"base faces {base_face}, stabilizers {base_stab}, orbitWiki {orbit_wiki}, "
          f"scale {float(s):.12f}, max |model - s T S_w y| = {float(max_err):.2e}")

    def q(x):
        return f"({x.numerator}/{x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"

    out = []
    w = out.append
    w("module\n\npublic import Noperthedron.PentagonalHexecontahedron.IcoGroupData\n\n@[expose] public section\n")
    w("/-!\n# Certificate data for the pentagonal hexecontahedron's statement (generated)\n\n"
      "Generated by `scripts/ph_statement_data.py`; do not edit. See that script for\n"
      "the meaning of each table. Statement.lean checks all of it.\n-/\n")
    w("namespace Noperthedron.PentagonalHexecontahedron\n")
    for v in boxes:
        for b in v:
            assert (b[0] * 2 ** 64).denominator == 1 and (b[1] * 2 ** 64).denominator == 1
    w("/-- The vertex boxes' endpoints, times 2^64. -/")
    w("def snubBoxLoZ : List (List Int) := [\n" + ",\n".join(
        "  [" + ", ".join(str(int(b[0] * 2 ** 64)) for b in v) + "]" for v in boxes) + "]\n")
    w("def snubBoxHiZ : List (List Int) := [\n" + ",\n".join(
        "  [" + ", ".join(str(int(b[1] * 2 ** 64)) for b in v) + "]" for v in boxes) + "]\n")
    w("def wikiInvIndex : List Nat := " + lean_list(inv) + "\n")
    w("def pairCert : List (List Nat) := [\n" + ",\n".join(
        "  " + ", ".join(lean_list(c) for c in certs[60 * j:60 * j + 60]) for j in range(60)) + "]\n")
    w("def baseFace : List (List Nat) := " + lean_list([lean_list(f) for f in base_face]) + "\n")
    w("def baseStab : List (List Nat) := " + lean_list([lean_list(f) for f in base_stab]) + "\n")
    w("def orbitWiki : List Nat := " + lean_list(orbit_wiki) + "\n")
    w("def stabConj : List (List (List Nat)) := [\n" + ",\n".join(
        "  " + lean_list([lean_list(r) for r in rows]) for rows in stab_conj) + "]\n")
    w("def slotSigma : List Nat := " + lean_list(slot_sigma) + "\n")
    w("def slotWiki : List Nat := " + lean_list(slot_wiki) + "\n")
    w("def orbitCover : List (List (List Nat)) := [\n" + ",\n".join(
        "  " + lean_list([lean_list(r) for r in rows]) for rows in orbit_cover) + "]\n")
    w(f"def phScaleNum : Nat := {s_q.numerator * (10 ** 40 // s_q.denominator)}\n")
    w("end Noperthedron.PentagonalHexecontahedron")
    args.out.write_text("\n".join(out) + "\n", encoding="utf-8")
    print("wrote", args.out)


if __name__ == "__main__":
    main()
