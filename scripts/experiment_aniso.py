"""Measurement experiment: anisotropic (per-axis eps) second-order certificate.

Question: if the v5 second-order certificate took a PER-AXIS eps vector
(eps_t1, eps_f1, eps_t2, eps_f2, eps_a) instead of the scalar sup-metric
eps = max_side/2, how much smaller could the solution tree be, exploiting
thin (anisotropic) boxes along the hard set?

Anisotropic penalty (generalizes eval_cert / _grid_eval of
make_solution_tree_v5.py; reduces exactly to v5 when all eps_i are equal):

  G side (inner; params a, t1, f1):
    first order:   e_a*|R'M1S.w| + e_t1*|RM1tS.w| + e_f1*|RM1fS.w|
    second order:  (1/2)*(e_a^2*q_aa + 2 e_a e_t1 q_at + 2 e_a e_f1 q_af
                          + e_t1^2 q_tt + 2 e_t1 e_f1 q_tf + e_f1^2 q_ff)
    remainder:     E1^3/6,  E1 = e_a + e_t1 + e_f1
    kappa:         4*KAPPA*(1 + E1 + E1^2/2)
  H side (outer; params t2, f2): analogous with E2 = e_t2 + e_f2,
    remainder E2^3/6, kappa 3*KAPPA*(1 + E2 + E2^2/2).

Experiment: identify the 216,000 depth-5 grid cells of solution_tree_v5.csv,
sample ~150 cells WITHOUT local leaves weighted by v5 subtree row count, and
for each rebuild a certified cover greedily with anisotropic boxes (binary
splits; axis chosen by largest e_i * d(penalty)/d(e_i) at the best witness).
Compare row counts.

Usage (from the repo root):
  .venv/bin/python regen/experiment_aniso.py --step sanity
  .venv/bin/python regen/experiment_aniso.py --step pilot --pilot-cells 3
  .venv/bin/python regen/experiment_aniso.py --step run --workers 12
(--step all does sanity+run; the parsed-tree cache is reused across steps.)
"""
import argparse
import json
import os
import pickle
import sys
import time
import multiprocessing as mp

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import make_solution_tree_v5 as v5   # pythag, eval_cert (reference), constants

DENOM = 15360000.0
KAPPA = 1e-10
SLACK_MIN = 1e-9
PARAMS = ["T1", "V1", "T2", "V2", "A"]   # pose order (t1, f1, t2, f2, a)
TOTAL_V5 = 5_621_213

COARSE_ANGLES = 1024     # full-circle w grid per box (matches v5's coarse grid)
REFINE_TOP = 6           # best coarse angles refined on failure
REFINE_N = 33            # fine angles per refined candidate (matches v5)
SEED_CAP = 256           # max distinct v5-winner seeds per box
RESERVOIR_K = 8          # near-misses passed from parent to children
VOL_CAP = (1.0 / 32.0) ** 3   # rel-volume depth cap -> charge 33 rows
CAP_CHARGE = 33
MAX_SCANS = 60_000       # per-cell box-scan budget (safety valve)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CSV = os.path.join(ROOT, "data", "solution_tree_v5.csv")
VERTS_JSON = os.path.join(HERE, "verts90.json")
RESULTS_JSON = os.path.join(HERE, "experiment_aniso_results.json")
CACHE_DEFAULT = os.path.join(
    "/tmp/claude-1000/-home-dwrensha-linux-src-Noperthedron/"
    "31441e85-03b7-4334-b23f-23240dcb18a4/scratchpad",
    "experiment_aniso_cache.pkl")

# ---- globals shared with fork()ed workers ----
VERTS = None
PX = PY = PZ = None
COARSE_ANG = None
COARSE_W = None
REFINE_DEL = None
SAMPLED = None           # list of per-cell task dicts


def init_geometry():
    global VERTS, PX, PY, PZ, COARSE_ANG, COARSE_W, REFINE_DEL
    VERTS = np.array(json.load(open(VERTS_JSON)))
    assert VERTS.shape == (90, 3)
    PX, PY, PZ = VERTS[:, 0], VERTS[:, 1], VERTS[:, 2]
    # make the v5 reference implementation usable too
    v5.verts, v5.Px, v5.Py, v5.Pz = VERTS, PX, PY, PZ
    COARSE_ANG = np.linspace(-np.pi, np.pi, COARSE_ANGLES, endpoint=False)
    COARSE_W = np.stack(v5.pythag(COARSE_ANG), axis=1)
    spacing = 2 * np.pi / COARSE_ANGLES
    REFINE_DEL = np.linspace(-spacing, spacing, REFINE_N)


# ===================== anisotropic certificate (float model) =====================

def eval_cert_aniso(pose, epsv, sidx, w0, w1):
    """Anisotropic ValidGlobal slack, flat arrays of length N.

    pose (N,5) [t1,f1,t2,f2,a]; epsv (N,5) per-axis radii in the SAME order
    [e_t1, e_f1, e_t2, e_f2, e_a].  Returns slack = min_P (num - den).
    Mirrors v5.eval_cert; with all eps columns equal it reproduces it.
    """
    t1, f1, t2, f2, a = (pose[:, k] for k in range(5))
    e_t1, e_f1, e_t2, e_f2, e_a = (epsv[:, k] for k in range(5))
    st1, ct1, sf1, cf1 = np.sin(t1), np.cos(t1), np.sin(f1), np.cos(f1)
    st2, ct2, sf2, cf2 = np.sin(t2), np.cos(t2), np.sin(f2), np.cos(f2)
    sa, ca = np.sin(a), np.cos(a)
    S = VERTS[sidx]
    Sx, Sy, Sz = S[:, 0], S[:, 1], S[:, 2]
    m1S_0 = -st1 * Sx + ct1 * Sy
    m1S_1 = -ct1 * cf1 * Sx - st1 * cf1 * Sy + sf1 * Sz
    m1tS_0 = -ct1 * Sx - st1 * Sy
    m1tS_1 = st1 * cf1 * Sx - ct1 * cf1 * Sy
    m1fS_1 = ct1 * sf1 * Sx + st1 * sf1 * Sy + cf1 * Sz
    m1ttS_0 = st1 * Sx - ct1 * Sy
    m1ttS_1 = ct1 * cf1 * Sx + st1 * cf1 * Sy
    m1tfS_1 = -st1 * sf1 * Sx + ct1 * sf1 * Sy
    base_G = (ca * m1S_0 - sa * m1S_1) * w0 + (sa * m1S_0 + ca * m1S_1) * w1
    q_aa = np.abs(base_G)
    q_at = np.abs((-sa * m1tS_0 - ca * m1tS_1) * w0 + (ca * m1tS_0 - sa * m1tS_1) * w1)
    q_af = np.abs((-ca * m1fS_1) * w0 + (-sa * m1fS_1) * w1)
    q_tt = np.abs((ca * m1ttS_0 - sa * m1ttS_1) * w0 + (sa * m1ttS_0 + ca * m1ttS_1) * w1)
    q_tf = np.abs((-sa * m1tfS_1) * w0 + (ca * m1tfS_1) * w1)
    q_ff = np.abs((sa * m1S_1) * w0 + (-ca * m1S_1) * w1)
    d_a = np.abs((-sa * m1S_0 - ca * m1S_1) * w0 + (ca * m1S_0 - sa * m1S_1) * w1)
    d_t = np.abs((ca * m1tS_0 - sa * m1tS_1) * w0 + (sa * m1tS_0 + ca * m1tS_1) * w1)
    d_f = np.abs((-sa * m1fS_1) * w0 + (ca * m1fS_1) * w1)
    E1 = e_a + e_t1 + e_f1
    pen_G = e_a * d_a + e_t1 * d_t + e_f1 * d_f \
        + 0.5 * (e_a**2 * q_aa + 2 * e_a * e_t1 * q_at + 2 * e_a * e_f1 * q_af
                 + e_t1**2 * q_tt + 2 * e_t1 * e_f1 * q_tf + e_f1**2 * q_ff) \
        + E1**3 / 6 + 4 * KAPPA * (1 + E1 + E1**2 / 2)
    st2_, ct2_, sf2_, cf2_ = (x[:, None] for x in (st2, ct2, sf2, cf2))
    w0_, w1_ = w0[:, None], w1[:, None]
    e2t, e2f = e_t2[:, None], e_f2[:, None]
    m2P_0 = -st2_ * PX + ct2_ * PY
    m2P_1 = -ct2_ * cf2_ * PX - st2_ * cf2_ * PY + sf2_ * PZ
    m2tP_0 = -ct2_ * PX - st2_ * PY
    m2tP_1 = st2_ * cf2_ * PX - ct2_ * cf2_ * PY
    m2fP_1 = ct2_ * sf2_ * PX + st2_ * sf2_ * PY + cf2_ * PZ
    m2ttP_1 = ct2_ * cf2_ * PX + st2_ * cf2_ * PY
    m2tfP_1 = -st2_ * sf2_ * PX + ct2_ * sf2_ * PY
    base_H = m2P_0 * w0_ + m2P_1 * w1_
    h_tt = np.abs(-m2P_0 * w0_ + m2ttP_1 * w1_)
    h_tf = np.abs(m2tfP_1 * w1_)
    h_ff = np.abs(m2P_1 * w1_)
    E2 = e2t + e2f
    pen_H = e2t * np.abs(m2tP_0 * w0_ + m2tP_1 * w1_) + e2f * np.abs(m2fP_1 * w1_) \
        + 0.5 * (e2t**2 * h_tt + 2 * e2t * e2f * h_tf + e2f**2 * h_ff) \
        + E2**3 / 6 + 3 * KAPPA * (1 + E2 + E2**2 / 2)
    num = base_G[:, None] - base_H
    den = pen_G[:, None] + pen_H
    return (num - den).min(axis=1)


def aniso_grid(center, e, w3):
    """Anisotropic slack for one box (pose = center, per-axis radii e) against a
    grid of w.  Mirrors v5._grid_eval.  Returns (slack (90,A), comps dict for
    the split-axis derivative)."""
    w0 = w3[:, 0] / w3[:, 2]
    w1 = w3[:, 1] / w3[:, 2]
    t1, f1, t2, f2, a = center
    e_t1, e_f1, e_t2, e_f2, e_a = e
    st1, ct1, sf1, cf1 = np.sin(t1), np.cos(t1), np.sin(f1), np.cos(f1)
    st2, ct2, sf2, cf2 = np.sin(t2), np.cos(t2), np.sin(f2), np.cos(f2)
    sa, ca = np.sin(a), np.cos(a)
    Sx, Sy, Sz = VERTS[:, 0], VERTS[:, 1], VERTS[:, 2]
    m1S_0 = -st1 * Sx + ct1 * Sy
    m1S_1 = -ct1 * cf1 * Sx - st1 * cf1 * Sy + sf1 * Sz
    m1tS_0 = -ct1 * Sx - st1 * Sy
    m1tS_1 = st1 * cf1 * Sx - ct1 * cf1 * Sy
    m1fS_1 = ct1 * sf1 * Sx + st1 * sf1 * Sy + cf1 * Sz
    m1ttS_0 = st1 * Sx - ct1 * Sy
    m1ttS_1 = ct1 * cf1 * Sx + st1 * cf1 * Sy
    m1tfS_1 = -st1 * sf1 * Sx + ct1 * sf1 * Sy
    gA = ca * m1S_0 - sa * m1S_1
    gB = sa * m1S_0 + ca * m1S_1
    dA = -sa * m1S_0 - ca * m1S_1
    tA = ca * m1tS_0 - sa * m1tS_1
    tB = sa * m1tS_0 + ca * m1tS_1
    fA = -sa * m1fS_1
    fB = ca * m1fS_1
    ttA = ca * m1ttS_0 - sa * m1ttS_1
    ttB = sa * m1ttS_0 + ca * m1ttS_1
    tfA = -sa * m1tfS_1
    tfB = ca * m1tfS_1
    ffA = sa * m1S_1
    ffB = -ca * m1S_1
    base_G = gA[:, None] * w0 + gB[:, None] * w1
    q_aa = np.abs(base_G)
    q_at = np.abs(-tB[:, None] * w0 + tA[:, None] * w1)
    q_af = np.abs(-fB[:, None] * w0 + fA[:, None] * w1)
    q_tt = np.abs(ttA[:, None] * w0 + ttB[:, None] * w1)
    q_tf = np.abs(tfA[:, None] * w0 + tfB[:, None] * w1)
    q_ff = np.abs(ffA[:, None] * w0 + ffB[:, None] * w1)
    d_a = np.abs(dA[:, None] * w0 + gA[:, None] * w1)
    d_t = np.abs(tA[:, None] * w0 + tB[:, None] * w1)
    d_f = np.abs(fA[:, None] * w0 + fB[:, None] * w1)
    E1 = e_a + e_t1 + e_f1
    pen_G = e_a * d_a + e_t1 * d_t + e_f1 * d_f \
        + 0.5 * (e_a**2 * q_aa + 2 * e_a * e_t1 * q_at + 2 * e_a * e_f1 * q_af
                 + e_t1**2 * q_tt + 2 * e_t1 * e_f1 * q_tf + e_f1**2 * q_ff) \
        + E1**3 / 6 + 4 * KAPPA * (1 + E1 + E1**2 / 2)
    m2P_0 = -st2 * PX + ct2 * PY
    m2P_1 = -ct2 * cf2 * PX - st2 * cf2 * PY + sf2 * PZ
    m2tP_0 = -ct2 * PX - st2 * PY
    m2tP_1 = st2 * cf2 * PX - ct2 * cf2 * PY
    m2fP_1 = ct2 * sf2 * PX + st2 * sf2 * PY + cf2 * PZ
    m2ttP_1 = ct2 * cf2 * PX + st2 * cf2 * PY
    m2tfP_1 = -st2 * sf2 * PX + ct2 * sf2 * PY
    base_H = m2P_0[:, None] * w0 + m2P_1[:, None] * w1
    h_tt = np.abs(-m2P_0[:, None] * w0 + m2ttP_1[:, None] * w1)
    h_tf = np.abs(m2tfP_1[:, None] * w1)
    h_ff = np.abs(m2P_1[:, None] * w1)
    hd_t = np.abs(m2tP_0[:, None] * w0 + m2tP_1[:, None] * w1)
    hd_f = np.abs(m2fP_1[:, None] * w1)
    E2 = e_t2 + e_f2
    pen_H = e_t2 * hd_t + e_f2 * hd_f \
        + 0.5 * (e_t2**2 * h_tt + 2 * e_t2 * e_f2 * h_tf + e_f2**2 * h_ff) \
        + E2**3 / 6 + 3 * KAPPA * (1 + E2 + E2**2 / 2)
    HB = base_H + pen_H
    slack = base_G - pen_G - HB.max(axis=0)[None, :]
    comps = dict(d_a=d_a, d_t=d_t, d_f=d_f, q_aa=q_aa, q_at=q_at, q_af=q_af,
                 q_tt=q_tt, q_tf=q_tf, q_ff=q_ff, HB=HB,
                 hd_t=hd_t, hd_f=hd_f, h_tt=h_tt, h_tf=h_tf, h_ff=h_ff)
    return slack, comps


def axis_contrib(e, comps, s, c):
    """Per-axis eps_i * d(penalty)/d(eps_i) at grid witness (S=s, w=col c),
    H side taken at the arg-max P.  Order [T1, V1, T2, V2, A]."""
    e_t1, e_f1, e_t2, e_f2, e_a = e
    E1 = e_a + e_t1 + e_f1
    E2 = e_t2 + e_f2
    d_a = comps["d_a"][s, c]; d_t = comps["d_t"][s, c]; d_f = comps["d_f"][s, c]
    q_aa = comps["q_aa"][s, c]; q_at = comps["q_at"][s, c]; q_af = comps["q_af"][s, c]
    q_tt = comps["q_tt"][s, c]; q_tf = comps["q_tf"][s, c]; q_ff = comps["q_ff"][s, c]
    P = int(comps["HB"][:, c].argmax())
    hd_t = comps["hd_t"][P, c]; hd_f = comps["hd_f"][P, c]
    h_tt = comps["h_tt"][P, c]; h_tf = comps["h_tf"][P, c]; h_ff = comps["h_ff"][P, c]
    g_a = d_a + e_a * q_aa + e_t1 * q_at + e_f1 * q_af + E1 * E1 / 2
    g_t1 = d_t + e_a * q_at + e_t1 * q_tt + e_f1 * q_tf + E1 * E1 / 2
    g_f1 = d_f + e_a * q_af + e_t1 * q_tf + e_f1 * q_ff + E1 * E1 / 2
    h_t2 = hd_t + e_t2 * h_tt + e_f2 * h_tf + E2 * E2 / 2
    h_f2 = hd_f + e_t2 * h_tf + e_f2 * h_ff + E2 * E2 / 2
    return np.array([e_t1 * g_t1, e_f1 * g_f1, e_t2 * h_t2, e_f2 * h_f2, e_a * g_a])


def eval_pairs(center, e, seeds):
    """Slack of explicit witness pairs seeds (N,4) int64 [s,wx,wy,wd] for one box."""
    n = len(seeds)
    pose = np.broadcast_to(center, (n, 5))
    epsv = np.broadcast_to(e, (n, 5))
    w0 = seeds[:, 1] / seeds[:, 3]
    w1 = seeds[:, 2] / seeds[:, 3]
    return eval_cert_aniso(pose, epsv, seeds[:, 0].astype(np.int64), w0, w1)


# ===================== greedy anisotropic build of one cell =====================

def build_cell(idx):
    rec = SAMPLED[idx]
    lo0 = rec["lo"].astype(np.int64)
    hi0 = rec["hi"].astype(np.int64)
    lbmin, lbmax, lwin = rec["lbmin"], rec["lbmax"], rec["lwin"]
    cell_vol = float(np.prod((hi0 - lo0).astype(float)))
    t0 = time.time()
    stack = [(lo0, hi0, None)]
    rows = n_leaf = n_split = n_cap = scans = 0
    axis_hist = np.zeros(5, dtype=np.int64)
    budget_exceeded = False
    while stack:
        lo, hi, res = stack.pop()
        if scans >= MAX_SCANS:
            budget_exceeded = True
            rows += CAP_CHARGE * (len(stack) + 1)
            n_cap += len(stack) + 1
            break
        scans += 1
        center = (lo + hi) / (2 * DENOM)
        e = (hi - lo) / (2 * DENOM)          # per-axis eps from box's own sides
        # ---- stage 1: seed witnesses (v5 winners of intersecting leaves + parent near-misses)
        if len(lwin):
            m = ((lbmin <= hi) & (lbmax >= lo)).all(axis=1)
            seeds = lwin[m]
        else:
            seeds = lwin
        if len(seeds):
            u, cts = np.unique(seeds, axis=0, return_counts=True)
            if len(u) > SEED_CAP:
                u = u[np.argsort(-cts)[:SEED_CAP]]
            seeds = u
        if res is not None:
            seeds = np.concatenate([seeds, res]) if len(seeds) else res
        accepted = False
        if len(seeds) and eval_pairs(center, e, seeds).max() >= SLACK_MIN:
            accepted = True
        if not accepted:
            # ---- stage 2: full-circle coarse grid (+ seed w's), all 90 S
            w3 = COARSE_W
            angs = COARSE_ANG
            if len(seeds):
                sw = np.unique(seeds[:, 1:4], axis=0)
                w3 = np.concatenate([w3, sw])
                angs = np.concatenate([angs, np.arctan2(sw[:, 1], sw[:, 0])])
            slack, comps = aniso_grid(center, e, w3)
            A = slack.shape[1]
            flat = slack.ravel()
            jb = int(flat.argmax())
            if flat[jb] >= SLACK_MIN:
                accepted = True
            else:
                # ---- stage 3: fine refinement of the best coarse angles
                order = np.argpartition(-flat, 63)[:64]
                order = order[np.argsort(-flat[order])]
                cols = np.unique(order % A)[:REFINE_TOP]
                ra = (angs[cols][:, None] + REFINE_DEL).ravel()
                ra = np.arctan2(np.sin(ra), np.cos(ra))
                rw = np.stack(v5.pythag(ra), axis=1)
                slack2, _ = aniso_grid(center, e, rw)
                if slack2.max() >= SLACK_MIN:
                    accepted = True
        if accepted:
            rows += 1
            n_leaf += 1
            continue
        relvol = float(np.prod((hi - lo).astype(float))) / cell_vol
        if relvol < VOL_CAP:
            rows += CAP_CHARGE
            n_cap += 1
            continue
        # ---- split: axis with largest eps_i * d(pen)/d(eps_i) at best witness
        contrib = axis_contrib(e, comps, jb // A, jb % A)
        sides = hi - lo
        contrib[sides < 2] = -np.inf
        ax = int(np.argmax(contrib))
        if not np.isfinite(contrib[ax]):
            rows += CAP_CHARGE
            n_cap += 1
            continue
        axis_hist[ax] += 1
        top = order[:RESERVOIR_K]
        res_rows = np.stack([top // A, w3[top % A, 0], w3[top % A, 1],
                             w3[top % A, 2]], axis=1).astype(np.int64)
        mid = (int(lo[ax]) + int(hi[ax])) // 2
        hi1 = hi.copy(); hi1[ax] = mid
        lo2 = lo.copy(); lo2[ax] = mid
        stack.append((lo, hi1, res_rows))
        stack.append((lo2, hi, res_rows))
        rows += 1
        n_split += 1
    return dict(cell=int(rec["id"]), v5_rows=int(rec["v5_rows"]),
                mult=int(rec.get("mult", 1)),
                aniso_rows=int(rows), n_leaf=int(n_leaf), n_split=int(n_split),
                n_cap=int(n_cap), n_scans=int(scans),
                axis_hist=[int(x) for x in axis_hist],
                budget_exceeded=bool(budget_exceeded),
                seconds=round(time.time() - t0, 2))


# ===================== tree parsing / cell identification =====================

def prep(cache_path, n_sample, rng_seed):
    print("loading v5 table ...", flush=True)
    df = pd.read_csv(CSV, dtype={c: "Int64" for c in v5.NULLABLE_INT_COLS})
    n = len(df)
    print(f"{n:,} rows")
    assert n == TOTAL_V5, n
    nt = df["nodeType"].to_numpy(np.int8)
    nrc = df["nrChildren"].fillna(0).to_numpy(np.int64)
    fc = df["IDfirstChild"].fillna(0).to_numpy(np.int64)
    bmin = np.stack([df[p + "_min"].to_numpy(np.int64) for p in PARAMS], axis=1)
    bmax = np.stack([df[p + "_max"].to_numpy(np.int64) for p in PARAMS], axis=1)
    s_idx = df["S_index"].fillna(0).to_numpy(np.int64)
    wx = df["wx_nominator"].fillna(0).to_numpy(np.int64)
    wy = df["wy_nominator"].fillna(0).to_numpy(np.int64)
    wd = df["w_denominator"].fillna(0).to_numpy(np.int64)
    del df

    # depth + depth-5 ancestor by downward propagation (BFS ids: parent < child)
    print("propagating depths ...", flush=True)
    depth = np.full(n, -1, dtype=np.int16)
    depth[0] = 0
    anc5 = np.full(n, -1, dtype=np.int64)
    for i in np.nonzero(nt == 3)[0]:
        f, c = fc[i], nrc[i]
        d1 = depth[i] + 1
        depth[f:f + c] = d1
        if d1 == 5:
            anc5[f:f + c] = np.arange(f, f + c)
        elif d1 > 5:
            anc5[f:f + c] = anc5[i]
    assert (depth >= 0).all()
    n_shallow = int((depth < 5).sum())
    assert ((anc5 >= 0) == (depth >= 5)).all()
    cells = np.nonzero(depth == 5)[0]
    cnt = np.bincount(anc5[anc5 >= 0], minlength=n)          # subtree row counts
    loc = np.bincount(anc5[(anc5 >= 0) & (nt == 2)], minlength=n)
    assert n_shallow + int(cnt.sum()) == TOTAL_V5, (n_shallow, cnt.sum())
    print(f"depth<5 rows: {n_shallow:,}   grid cells: {len(cells):,}   "
          f"check-total: {n_shallow + int(cnt.sum()):,} == {TOTAL_V5:,}")

    has_local = loc[cells] > 0
    g_cells = cells[~has_local]
    l_cells = cells[has_local]
    rows_global = int(cnt[g_cells].sum())
    rows_local = int(cnt[l_cells].sum())
    print(f"cells without local leaves: {len(g_cells):,} ({rows_global:,} rows)")
    print(f"cells with    local leaves: {len(l_cells):,} ({rows_local:,} rows)")

    # PPS sample WITH replacement (prob ~ v5 subtree rows): the unweighted mean
    # of per-draw ratios aniso/v5 is then an unbiased estimator of the
    # aggregate ratio sum(aniso)/sum(v5) over the whole global-cell region.
    # Duplicated draws are computed once and carried as a multiplicity.
    rng = np.random.default_rng(rng_seed)
    p = cnt[g_cells] / cnt[g_cells].sum()
    pick = rng.choice(len(g_cells), size=n_sample, replace=True, p=p)
    uniq, mult = np.unique(g_cells[pick], return_counts=True)
    sample_ids = uniq
    print(f"sampled {n_sample} draws -> {len(uniq)} distinct cells, "
          f"v5 rows in sample: {int(cnt[sample_ids].sum()):,}")

    # per-cell leaf data (bounds + v5 winners) for seed witnesses
    sampled = []
    sset = np.zeros(n, dtype=bool)
    sset[sample_ids] = True
    is_leafrow = (nt == 1) & (anc5 >= 0)
    keep = is_leafrow.copy()
    keep[is_leafrow] = sset[anc5[is_leafrow]]
    rows_kept = np.nonzero(keep)[0]
    order = np.argsort(anc5[rows_kept], kind="stable")
    rows_kept = rows_kept[order]
    starts = np.searchsorted(anc5[rows_kept], sample_ids)
    ends = np.searchsorted(anc5[rows_kept], sample_ids, side="right")
    for cid, mlt, s0, s1 in zip(sample_ids, mult, starts, ends):
        rr = rows_kept[s0:s1]
        sampled.append(dict(
            id=int(cid), lo=bmin[cid].copy(), hi=bmax[cid].copy(),
            v5_rows=int(cnt[cid]), mult=int(mlt),
            lbmin=bmin[rr].copy(), lbmax=bmax[rr].copy(),
            lwin=np.stack([s_idx[rr], wx[rr], wy[rr], wd[rr]], axis=1)))
    # big cells first for pool load balancing
    sampled.sort(key=lambda r: -r["v5_rows"])

    # sanity-check sample: 10k random global leaves (box + winner)
    gl = np.nonzero(nt == 1)[0]
    gs = rng.choice(gl, size=min(10_000, len(gl)), replace=False)
    sanity = dict(lo=bmin[gs], hi=bmax[gs],
                  win=np.stack([s_idx[gs], wx[gs], wy[gs], wd[gs]], axis=1))

    meta = dict(total=TOTAL_V5, rows_shallow=n_shallow,
                n_cells=len(cells), n_global_cells=len(g_cells),
                n_local_cells=len(l_cells),
                rows_global_cells=rows_global, rows_local_cells=rows_local,
                rng_seed=rng_seed, n_draws=n_sample)
    with open(cache_path, "wb") as f:
        pickle.dump(dict(meta=meta, sampled=sampled, sanity=sanity), f, protocol=4)
    print(f"cache written: {cache_path}")
    return dict(meta=meta, sampled=sampled, sanity=sanity)


def load_cache(cache_path, n_sample, rng_seed):
    if os.path.exists(cache_path):
        with open(cache_path, "rb") as f:
            c = pickle.load(f)
        if (c["meta"]["rng_seed"] == rng_seed
                and c["meta"].get("n_draws") == n_sample):
            print(f"using cache {cache_path} ({len(c['sampled'])} sampled cells)")
            return c
    return prep(cache_path, n_sample, rng_seed)


# ===================== sanity checks =====================

def sanity_check(cache):
    sn = cache["sanity"]
    lo, hi, win = sn["lo"], sn["hi"], sn["win"]
    pose = (lo + hi) / (2 * DENOM)
    eps = ((hi - lo).max(axis=1) / 2) / DENOM
    sidx = win[:, 0].astype(np.int64)
    w0 = win[:, 1] / win[:, 3]
    w1 = win[:, 2] / win[:, 3]
    sl_v5, _ = v5.eval_cert(pose, eps, sidx, w0, w1)
    epsv = np.repeat(eps[:, None], 5, axis=1)      # all axes = sup-metric eps
    sl_an = eval_cert_aniso(pose, epsv, sidx, w0, w1)
    dmax = float(np.abs(sl_v5 - sl_an).max())
    print(f"[sanity] equal-eps agreement on {len(lo):,} v5 global leaves: "
          f"max |slack_v5 - slack_aniso| = {dmax:.3e}")
    assert dmax < 1e-12, dmax
    assert (sl_v5 >= SLACK_MIN).all(), "v5 leaf winners should re-verify"

    # monotonicity: growing any eps_i never increases the slack
    rng = np.random.default_rng(7)
    sub = rng.choice(len(lo), size=400, replace=False)
    pose_s = pose[sub]
    sidx_s, w0_s, w1_s = sidx[sub], w0[sub], w1[sub]
    base_e = ((hi[sub] - lo[sub]) / (2 * DENOM)) * rng.uniform(0.2, 1.5, (len(sub), 5))
    worst = 0.0
    for ax in range(5):
        for fac in (1.3, 2.0, 5.0):
            e2 = base_e.copy()
            e2[:, ax] *= fac
            s1 = eval_cert_aniso(pose_s, base_e, sidx_s, w0_s, w1_s)
            s2 = eval_cert_aniso(pose_s, e2, sidx_s, w0_s, w1_s)
            worst = max(worst, float((s2 - s1).max()))
    print(f"[sanity] monotonicity: max slack increase when growing an eps axis = "
          f"{worst:.3e} (must be <= 0 up to fp noise)")
    assert worst <= 1e-15, worst
    print("[sanity] PASSED")
    return dmax, worst


# ===================== driver =====================

def summarize(results, meta, elapsed, args, sanity_out):
    ok = [r for r in results if not r["budget_exceeded"]]
    bad = [r for r in results if r["budget_exceeded"]]
    sum_v5 = sum(r["v5_rows"] for r in results)
    sum_an = sum(r["aniso_rows"] for r in results)
    cell_ratios = np.array([r["aniso_rows"] / r["v5_rows"] for r in results])
    mults = np.array([r["mult"] for r in results])
    # PPS-with-replacement draws (prob ~ v5 subtree size): the unweighted mean
    # of per-DRAW ratios is an unbiased estimator of the aggregate ratio
    # sum(aniso)/sum(v5) over the global-cell region.
    ratios = np.repeat(cell_ratios, mults)          # draw-level
    mean_ratio = float(ratios.mean())
    sem = float(ratios.std(ddof=1) / np.sqrt(len(ratios)))
    rng = np.random.default_rng(0)
    boots = np.array([ratios[rng.integers(0, len(ratios), len(ratios))].mean()
                      for _ in range(2000)])
    ci = (float(np.percentile(boots, 2.5)), float(np.percentile(boots, 97.5)))
    axis_tot = np.sum([r["axis_hist"] for r in results], axis=0)
    n_cap = sum(r["n_cap"] for r in results)
    n_leaf = sum(r["n_leaf"] for r in results)
    n_split = sum(r["n_split"] for r in results)
    secs = np.array([r["seconds"] for r in results])
    v6_est = (meta["rows_shallow"] + meta["rows_local_cells"]
              + mean_ratio * meta["rows_global_cells"])
    v6_lo = (meta["rows_shallow"] + meta["rows_local_cells"]
             + ci[0] * meta["rows_global_cells"])
    v6_hi = (meta["rows_shallow"] + meta["rows_local_cells"]
             + ci[1] * meta["rows_global_cells"])
    out = dict(
        config=dict(coarse_angles=COARSE_ANGLES, refine_top=REFINE_TOP,
                    refine_n=REFINE_N, seed_cap=SEED_CAP,
                    reservoir_k=RESERVOIR_K, vol_cap=VOL_CAP,
                    cap_charge=CAP_CHARGE, max_scans=MAX_SCANS,
                    n_cells_requested=args.cells, rng_seed=args.seed),
        sanity=dict(equal_eps_max_diff=sanity_out[0],
                    monotonicity_max_violation=sanity_out[1]),
        meta=meta,
        headline=dict(
            n_cells=len(results), n_draws=int(mults.sum()),
            n_budget_exceeded=len(bad),
            sample_v5_rows=sum_v5, sample_aniso_rows=sum_an,
            pooled_ratio_sample=sum_an / sum_v5,
            mean_per_cell_ratio=mean_ratio, sem=sem,
            ratio_ci95=ci,
            ratio_percentiles={str(q): float(np.percentile(ratios, q))
                               for q in (5, 25, 50, 75, 95)},
            v6_estimate_rows=int(v6_est),
            v6_ci95_rows=[int(v6_lo), int(v6_hi)],
            v5_total_rows=meta["total"],
            table_shrink_factor=meta["total"] / v6_est),
        search=dict(n_leaf=n_leaf, n_split=n_split, n_capped=n_cap,
                    cap_rate_of_boxes=n_cap / max(1, n_leaf + n_split + n_cap),
                    axis_split_hist=dict(zip(PARAMS, [int(x) for x in axis_tot]))),
        timing=dict(wall_total_s=elapsed,
                    per_cell_s=dict(mean=float(secs.mean()),
                                    median=float(np.median(secs)),
                                    max=float(secs.max()))),
        cells=results)
    return out


def main():
    global MAX_SCANS, SAMPLED
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--step", default="all", choices=["prep", "sanity", "pilot", "run", "all"])
    ap.add_argument("--cells", type=int, default=150)
    ap.add_argument("--pilot-cells", type=int, default=3)
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--cache", default=CACHE_DEFAULT)
    ap.add_argument("--max-scans", type=int, default=MAX_SCANS)
    args = ap.parse_args()
    MAX_SCANS = args.max_scans

    init_geometry()
    os.makedirs(os.path.dirname(args.cache), exist_ok=True)
    cache = load_cache(args.cache, args.cells, args.seed)
    meta = cache["meta"]
    if args.step == "prep":
        return
    sanity_out = sanity_check(cache)
    if args.step == "sanity":
        return

    SAMPLED = cache["sampled"]
    if args.step == "pilot":
        # serial run of a few cells across the size spectrum, for timing
        idxs = [0, len(SAMPLED) // 2, len(SAMPLED) - 1][:args.pilot_cells]
        for i in idxs:
            r = build_cell(i)
            print(f"[pilot] cell {r['cell']}: v5={r['v5_rows']:,} "
                  f"aniso={r['aniso_rows']:,} ratio={r['aniso_rows']/r['v5_rows']:.3f} "
                  f"scans={r['n_scans']:,} capped={r['n_cap']} "
                  f"leaf/split={r['n_leaf']}/{r['n_split']} "
                  f"axes={r['axis_hist']} t={r['seconds']}s", flush=True)
        return

    print(f"\n=== greedy aniso build: {len(SAMPLED)} cells, "
          f"{args.workers} workers ===", flush=True)
    t0 = time.time()
    results = []
    with mp.Pool(args.workers) as pool:
        for k, r in enumerate(pool.imap_unordered(build_cell, range(len(SAMPLED))), 1):
            results.append(r)
            print(f"[{k:3d}/{len(SAMPLED)}] cell {r['cell']:>8}: "
                  f"v5={r['v5_rows']:>7,} aniso={r['aniso_rows']:>7,} "
                  f"ratio={r['aniso_rows']/r['v5_rows']:5.3f} "
                  f"cap={r['n_cap']:>4} t={r['seconds']:7.1f}s"
                  f"{'  BUDGET-EXCEEDED' if r['budget_exceeded'] else ''}",
                  flush=True)
    elapsed = time.time() - t0
    out = summarize(results, meta, elapsed, args, sanity_out)
    with open(RESULTS_JSON, "w") as f:
        json.dump(out, f, indent=1)
    h = out["headline"]
    print(f"\nwrote {RESULTS_JSON}")
    print(f"headline: mean per-cell ratio = {h['mean_per_cell_ratio']:.4f} "
          f"+- {h['sem']:.4f} (CI95 {h['ratio_ci95'][0]:.4f}..{h['ratio_ci95'][1]:.4f})")
    print(f"pooled sample ratio = {h['pooled_ratio_sample']:.4f} "
          f"({h['sample_aniso_rows']:,} / {h['sample_v5_rows']:,})")
    print(f"extrapolated v6 rows = {h['v6_estimate_rows']:,} "
          f"(CI95 {h['v6_ci95_rows'][0]:,}..{h['v6_ci95_rows'][1]:,}); "
          f"v5 = {h['v5_total_rows']:,} -> {h['table_shrink_factor']:.2f}x smaller")
    print(f"axis split histogram: {out['search']['axis_split_hist']}")
    print(f"cap rate: {out['search']['cap_rate_of_boxes']:.4f}  "
          f"budget-exceeded cells: {h['n_budget_exceeded']}")
    print(f"wall time: {elapsed/60:.1f} min; per-cell "
          f"mean {out['timing']['per_cell_s']['mean']:.1f}s / "
          f"median {out['timing']['per_cell_s']['median']:.1f}s / "
          f"max {out['timing']['per_cell_s']['max']:.1f}s")


if __name__ == "__main__":
    main()
