"""Produce solution_tree_v4.csv from SY25's original solution_tree.csv.

Supersedes make_solution_tree_v3.py: same two passes (prune fold boxes
bottom-up, then flip surviving local leaves to global), same Lean checker,
same lemmas, same 1e-9 slack margin — but the witness search per box is
(nearly) exhaustive instead of seeded-and-narrow:

  For every candidate box, in addition to the cheap stage (witnesses
  inherited from children/siblings), we scan ALL 90 vertices S against a
  full-circle grid of Pythagorean-rational directions w (--coarse-angles,
  default 1024), refine the top --refine-top candidates by m* on a fine
  sub-grid (33 angles within one grid step), and also scan a +-0.10 rad x
  41-angle window around the best inherited witness.  The window scan is a
  strict superset of the v3 search, so, up to float64 reproducibility, v4's
  kills/flips are a superset of v3's per box, and the superset property
  propagates bottom-up.

  The per-box scan exploits that the pose is fixed at the box center: the
  outer-shadow side max_P (H + pen_H) is independent of S, so the whole
  (S, w) grid evaluates with a few (90 x A) outer products instead of a
  flat (S*A) x P sweep — a few ms per box.

Sampling with a fully exhaustive scan (90 S x 1024 angles) estimated the
remaining headroom over v3 at ~17.8% of surviving fold boxes killable
(~2.4M rows) and ~34.6% of remaining local leaves flippable (~120k rows),
for roughly 25-30% less Lean check time on top of v3's 1.45x.

Inputs (same as v3):
  - the original solution_tree.csv (from SY25's solution_tree.zip,
    https://github.com/Jakob256/Rupert/blob/main/data/solution_tree.zip)
  - verts90.json: the 90 Noperthedron vertices in CSV index order, extracted
    from Noperthedron/Vertices/Python.lean (mkV integer coordinates / 10^16)

Usage:
  python make_solution_tree_v4.py \
      --input   data/solution_tree.csv \
      --verts   regen/verts90.json \
      --pruned-out solution_tree_v4_pruned.csv \
      --v4-out  solution_tree_v4.csv \
      --workers 16

Runtime: roughly an hour wall-clock on 16 cores (dominated by CSV parsing,
the cheap stages, and emission; the ~1M exhaustive box scans themselves run
at a few ms each).  Peak memory ~16 GB in the parent (workers share pages
copy-on-write).  Requires numpy + pandas and a fork-capable OS
(Linux/macOS).

Checkpoints/resume: pass 1 saves state after each depth level and pass 2
every 25k scanned boxes, into --checkpoint-dir (default: alongside
--v4-out).  Rerun with --resume to continue after an interruption; use
--skip-prune to reuse an already-written --pruned-out file.

Determinism: the search has no randomness and worker scheduling cannot
affect results (boxes are independent; results are applied by box id), but
acceptance depends on float64 rounding, so bit-identical output across
machines or math-library versions is not guaranteed.  Every accepted
witness carries the 1e-9 slack margin against the exact rational
ValidGlobal inequality, so any output of this script passes the Lean
checker regardless.
"""
import argparse
import json
import multiprocessing as mp
import os
import pickle
import time
from collections import deque

import numpy as np
import pandas as pd

DENOM = 15360000.0
KAPPA = 1e-10
SLACK_MIN = 1e-9          # required min_P (num - den) for acceptance
K_RES = 16                # witness reservoir size propagated upward (pass 1)
PARAMS = ["T1", "V1", "T2", "V2", "A"]
NULLABLE_INT_COLS = ["nrChildren", "IDfirstChild", "split",
                     "P1_index", "P2_index", "P3_index",
                     "Q1_index", "Q2_index", "Q3_index", "r", "sigma_Q",
                     "wx_nominator", "wy_nominator", "w_denominator", "S_index"]
HEADER = ("ID,nodeType,nrChildren,IDfirstChild,split,"
          "T1_min,T1_max,V1_min,V1_max,T2_min,T2_max,V2_min,V2_max,A_min,A_max,"
          "P1_index,P2_index,P3_index,Q1_index,Q2_index,Q3_index,r,sigma_Q,"
          "wx_nominator,wy_nominator,w_denominator,S_index")
SEED_DEL = np.linspace(-0.10, 0.10, 41)     # window around inherited witness
REFINE_N = 33                               # fine angles per refined candidate

# ---- globals shared with fork()ed workers (set before Pool creation) ----
verts = None
Px = Py = Pz = None
CENTERS = None            # (n,5) box-center poses of the current table
EPS_ALL = None            # (n,) sup-metric radii of the current table
COARSE_ANG = None         # (A,) full-circle coarse angle grid
COARSE_W = None           # (A,3) int64 [wx, wy, wd] for the coarse grid
REFINE_DEL = None         # (REFINE_N,) offsets within one coarse step
REFINE_TOP = None


def load_table(path):
    if path.endswith(".parquet"):
        return pd.read_parquet(path)
    return pd.read_csv(path, dtype={c: "Int64" for c in NULLABLE_INT_COLS})


def eval_cert(pose, eps, sidx, w0, w1):
    """Exact ValidGlobal inequality Gq > maxHq, split as num > den.

    Flat float64 arrays of length N (pose is (N,5)).  Returns (slack, mstar):
    slack = min_P (num - den), mstar = min_P num/den.  A witness is accepted
    only when slack >= SLACK_MIN.
    """
    t1, f1, t2, f2, a = (pose[:, k] for k in range(5))
    st1, ct1, sf1, cf1 = np.sin(t1), np.cos(t1), np.sin(f1), np.cos(f1)
    st2, ct2, sf2, cf2 = np.sin(t2), np.cos(t2), np.sin(f2), np.cos(f2)
    sa, ca = np.sin(a), np.cos(a)
    S = verts[sidx]
    Sx, Sy, Sz = S[:, 0], S[:, 1], S[:, 2]
    m1S_0 = -st1 * Sx + ct1 * Sy
    m1S_1 = -ct1 * cf1 * Sx - st1 * cf1 * Sy + sf1 * Sz
    m1tS_0 = -ct1 * Sx - st1 * Sy
    m1tS_1 = st1 * cf1 * Sx - ct1 * cf1 * Sy
    m1fS_1 = ct1 * sf1 * Sx + st1 * sf1 * Sy + cf1 * Sz
    base_G = (ca * m1S_0 - sa * m1S_1) * w0 + (sa * m1S_0 + ca * m1S_1) * w1
    pen_G = eps * (np.abs((-sa * m1S_0 - ca * m1S_1) * w0 + (ca * m1S_0 - sa * m1S_1) * w1) +
                   np.abs((ca * m1tS_0 - sa * m1tS_1) * w0 + (sa * m1tS_0 + ca * m1tS_1) * w1) +
                   np.abs((-sa * m1fS_1) * w0 + (ca * m1fS_1) * w1)) \
            + 4.5 * eps**2 + 4 * KAPPA * (1 + 3 * eps)
    st2_, ct2_, sf2_, cf2_ = (x[:, None] for x in (st2, ct2, sf2, cf2))
    w0_, w1_, eps_ = w0[:, None], w1[:, None], eps[:, None]
    m2P_0 = -st2_ * Px + ct2_ * Py
    m2P_1 = -ct2_ * cf2_ * Px - st2_ * cf2_ * Py + sf2_ * Pz
    m2tP_0 = -ct2_ * Px - st2_ * Py
    m2tP_1 = st2_ * cf2_ * Px - ct2_ * cf2_ * Py
    m2fP_1 = ct2_ * sf2_ * Px + st2_ * sf2_ * Py + cf2_ * Pz
    base_H = m2P_0 * w0_ + m2P_1 * w1_
    pen_H = eps_ * (np.abs(m2tP_0 * w0_ + m2tP_1 * w1_) + np.abs(m2fP_1 * w1_)) \
            + 2 * eps_**2 + 3 * KAPPA * (1 + 2 * eps_)
    num = base_G[:, None] - base_H
    den = pen_G[:, None] + pen_H
    return (num - den).min(axis=1), (num / den).min(axis=1)


def pythag(angles):
    """Exact Pythagorean-rational w for each angle: t = tan(a/2) ~ p/q.

    Angles must lie in (-pi, pi]; directions within ~0.02 rad of angle -pi
    collapse onto the clip boundary (same limitation as the v3 search).
    """
    t = np.tan(np.clip(angles, -np.pi + 1e-6, np.pi - 1e-6) / 2)
    t = np.clip(t, -100.0, 100.0)
    q = 100_000
    p = np.round(t * q).astype(np.int64)
    wx = q * q - p * p
    wy = 2 * p * q
    wd = q * q + p * p
    return wx, wy, wd


def init_scan_grids(coarse_angles, refine_top):
    global COARSE_ANG, COARSE_W, REFINE_DEL, REFINE_TOP
    COARSE_ANG = np.linspace(-np.pi, np.pi, coarse_angles, endpoint=False)
    COARSE_W = np.stack(pythag(COARSE_ANG), axis=1)
    spacing = 2 * np.pi / coarse_angles
    REFINE_DEL = np.linspace(-spacing, spacing, REFINE_N)
    REFINE_TOP = refine_top


TOPM = 512    # candidates (by slack) that get an exact m* for ranking


def _grid_eval(i, w3):
    """Evaluate the ValidGlobal slack for one box against a grid of w.

    w3 is (A,3) int64 [wx, wy, wd].  The pose is the box center, so all
    pose trig is scalar and both sides reduce to (90 x A) outer products;
    max over P separates out of the slack.  Returns slack (90 S, A) plus
    the four component arrays needed to compute exact m* for a subset.
    """
    w0 = w3[:, 0] / w3[:, 2]
    w1 = w3[:, 1] / w3[:, 2]
    t1, f1, t2, f2, a = CENTERS[i]
    eps = EPS_ALL[i]
    st1, ct1, sf1, cf1 = np.sin(t1), np.cos(t1), np.sin(f1), np.cos(f1)
    st2, ct2, sf2, cf2 = np.sin(t2), np.cos(t2), np.sin(f2), np.cos(f2)
    sa, ca = np.sin(a), np.cos(a)
    Sx, Sy, Sz = verts[:, 0], verts[:, 1], verts[:, 2]
    m1S_0 = -st1 * Sx + ct1 * Sy
    m1S_1 = -ct1 * cf1 * Sx - st1 * cf1 * Sy + sf1 * Sz
    m1tS_0 = -ct1 * Sx - st1 * Sy
    m1tS_1 = st1 * cf1 * Sx - ct1 * cf1 * Sy
    m1fS_1 = ct1 * sf1 * Sx + st1 * sf1 * Sy + cf1 * Sz
    gA = ca * m1S_0 - sa * m1S_1
    gB = sa * m1S_0 + ca * m1S_1
    dA = -sa * m1S_0 - ca * m1S_1
    tA = ca * m1tS_0 - sa * m1tS_1
    tB = sa * m1tS_0 + ca * m1tS_1
    fA = -sa * m1fS_1
    fB = ca * m1fS_1
    base_G = gA[:, None] * w0 + gB[:, None] * w1
    pen_G = eps * (np.abs(dA[:, None] * w0 + gA[:, None] * w1) +
                   np.abs(tA[:, None] * w0 + tB[:, None] * w1) +
                   np.abs(fA[:, None] * w0 + fB[:, None] * w1)) \
            + 4.5 * eps**2 + 4 * KAPPA * (1 + 3 * eps)
    m2P_0 = -st2 * Px + ct2 * Py
    m2P_1 = -ct2 * cf2 * Px - st2 * cf2 * Py + sf2 * Pz
    m2tP_0 = -ct2 * Px - st2 * Py
    m2tP_1 = st2 * cf2 * Px - ct2 * cf2 * Py
    m2fP_1 = ct2 * sf2 * Px + st2 * sf2 * Py + cf2 * Pz
    base_H = m2P_0[:, None] * w0 + m2P_1[:, None] * w1          # (90 P, A)
    pen_H = eps * (np.abs(m2tP_0[:, None] * w0 + m2tP_1[:, None] * w1) +
                   np.abs(m2fP_1[:, None] * w1)) \
            + 2 * eps**2 + 3 * KAPPA * (1 + 2 * eps)
    slack = base_G - pen_G - (base_H + pen_H).max(axis=0)[None, :]
    return slack, base_G, pen_G, base_H, pen_H


def _mstar_subset(flat, A, base_G, pen_G, base_H, pen_H):
    """Exact m* = min_P num/den for flat (s*A + w) indices."""
    s, w = flat // A, flat % A
    num = base_G[s, w][:, None] - base_H[:, w].T                # (K, 90 P)
    den = pen_G[s, w][:, None] + pen_H[:, w].T
    return (num / den).min(axis=1)


def scan_box(task):
    """Exhaustive witness search for one box.  task = (id, seed_angle|nan).

    Full-circle grid over all 90 S x COARSE_ANG, plus a +-0.10 rad window
    around the seed angle (the best inherited witness); if nothing passes,
    the top REFINE_TOP candidates by exact m* get a fine angle sub-grid.
    All candidate w are exact Pythagorean rationals, so an accepted witness
    needs no post-processing.  Returns (id, accepted [s,wx,wy,wd] | None,
    reservoir rows (4,4) int64 | None, best m* seen).
    """
    i, seed = task
    angs = COARSE_ANG
    w3 = COARSE_W
    if not np.isnan(seed):
        sang = np.arctan2(np.sin(seed + SEED_DEL), np.cos(seed + SEED_DEL))
        angs = np.concatenate([angs, sang])
        w3 = np.concatenate([w3, np.stack(pythag(sang), axis=1)])
    A = len(angs)
    slack, *parts = _grid_eval(i, w3)
    flat = slack.ravel()
    jb = int(flat.argmax())
    if flat[jb] >= SLACK_MIN:
        s, w = jb // A, jb % A
        return i, [int(s), int(w3[w, 0]), int(w3[w, 1]), int(w3[w, 2])], None, float("nan")

    # rank the best TOPM grid points by exact m*
    top = np.argpartition(-flat, min(TOPM, flat.size) - 1)[:TOPM]
    mst = _mstar_subset(top, A, *parts)
    order = top[np.argsort(-mst)]
    best_m = float(mst.max())

    # fine refinement around the top candidates' angles (all 90 S at once)
    ra = np.unique(angs[order[:REFINE_TOP] % A])[:, None] + REFINE_DEL
    ra = np.arctan2(np.sin(ra), np.cos(ra)).ravel()
    rw = np.stack(pythag(ra), axis=1)
    slack2, *parts2 = _grid_eval(i, rw)
    flat2 = slack2.ravel()
    j2 = int(flat2.argmax())
    if flat2[j2] >= SLACK_MIN:
        s, w = j2 // len(ra), j2 % len(ra)
        return i, [int(s), int(rw[w, 0]), int(rw[w, 1]), int(rw[w, 2])], None, best_m

    res4 = order[:4]
    res = np.stack([res4 // A, w3[res4 % A, 0], w3[res4 % A, 1], w3[res4 % A, 2]], axis=1)
    return i, None, res, best_m


def run_pool(pool, tasks, apply_result, label, ckpt_every=None, ckpt_fn=None):
    t0 = time.time()
    n_hit = 0
    chunk = max(1, len(tasks) // (pool._processes * 16)) if tasks else 1
    for k, out in enumerate(pool.imap_unordered(scan_box, tasks, chunksize=chunk), 1):
        n_hit += apply_result(out)
        if k % 20_000 == 0:
            rate = k / (time.time() - t0)
            print(f"    {label}: {k:,}/{len(tasks):,} scanned, {n_hit:,} hits, "
                  f"{rate:.0f} boxes/s, eta {(len(tasks) - k) / rate / 60:.0f} min",
                  flush=True)
            if ckpt_every and ckpt_fn and k % ckpt_every == 0:
                ckpt_fn()
    return n_hit


def save_pickle(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "wb") as f:
        pickle.dump(obj, f, protocol=4)
    os.replace(tmp, path)


# ======================= PASS 1: prune (original -> pruned) =======================

def prune(df, pruned_path, workers, min_mstar, ckpt_dir, resume):
    global CENTERS, EPS_ALL
    n = len(df)
    node_type = df["nodeType"].to_numpy(np.int8)
    nr_children = df["nrChildren"].fillna(0).to_numpy(np.int32)
    first_child = df["IDfirstChild"].fillna(0).to_numpy(np.int64)
    splitk = df["split"].fillna(0).to_numpy(np.int8)
    s_idx = df["S_index"].fillna(0).to_numpy(np.int16)
    wxA = df["wx_nominator"].fillna(0).to_numpy(np.int64)
    wyA = df["wy_nominator"].fillna(0).to_numpy(np.int64)
    wdA = df["w_denominator"].fillna(0).to_numpy(np.int64)

    bounds = {}
    for p in PARAMS:
        bounds[p + "_min"] = df[p + "_min"].to_numpy(np.int64)
        bounds[p + "_max"] = df[p + "_max"].to_numpy(np.int64)
    INT_COLS = ["P1_index", "P2_index", "P3_index", "Q1_index", "Q2_index", "Q3_index",
                "r", "sigma_Q"]
    misc = {c: df[c].to_numpy() for c in INT_COLS}
    misc_na = {c: df[c].isna().to_numpy() for c in INT_COLS}
    wna = df["wx_nominator"].isna().to_numpy()
    del df

    sides = np.stack([(bounds[p + "_max"] - bounds[p + "_min"]) / DENOM
                      for p in PARAMS], axis=1)
    CENTERS = np.stack([(bounds[p + "_max"] + bounds[p + "_min"]) / (2 * DENOM)
                        for p in PARAMS], axis=1)
    EPS_ALL = sides.max(axis=1) / 2

    depth = np.full(n, -1, dtype=np.int8)
    depth[0] = 0
    for i in np.nonzero(node_type == 3)[0]:
        fc = first_child[i]
        depth[fc:fc + nr_children[i]] = depth[i] + 1

    is_fold = (node_type == 3) & (splitk == 6)
    fold_ids = np.nonzero(is_fold)[0]
    kill = np.zeros(n, dtype=bool)
    win = np.zeros((n, 4), dtype=np.int64)        # [s, wx, wy, wd]
    reservoir = {}                                # fold id -> (k,4) int64
    stats = {"cheap_kill": 0, "scan_kill": 0}
    done_depths = set()

    ckpt = os.path.join(ckpt_dir, "pass1_state.pkl")
    if resume and os.path.exists(ckpt):
        st = pickle.load(open(ckpt, "rb"))
        done_depths = st["done_depths"]
        kill[st["kill_idx"]] = True
        win[st["kill_idx"]] = st["win_rows"]
        reservoir = st["reservoir"]
        stats = st["stats"]
        print(f"resumed pass 1: depths {sorted(done_depths, reverse=True)} done, "
              f"{kill.sum():,} kills so far")

    def checkpoint():
        idx = np.nonzero(kill)[0]
        save_pickle(ckpt, {"done_depths": done_depths, "kill_idx": idx,
                           "win_rows": win[idx], "reservoir": reservoir,
                           "stats": stats})

    def gather_candidates(i):
        fc, c = first_child[i], nr_children[i]
        kids = np.arange(fc, fc + c)
        parts = []
        gl = kids[node_type[kids] == 1]
        if len(gl):
            parts.append(np.stack([s_idx[gl].astype(np.int64), wxA[gl], wyA[gl], wdA[gl]], axis=1))
        for k in kids[is_fold[kids]]:
            if kill[k]:
                parts.append(win[k][None, :])
            elif k in reservoir:
                parts.append(reservoir[k])
        if not parts:
            return None
        return np.unique(np.concatenate(parts), axis=0)

    with mp.Pool(workers) as pool:
        order_depths = sorted(np.unique(depth[fold_ids]), reverse=True)
        for d in order_depths:
            if d in done_depths:
                continue
            t0 = time.time()
            ids = fold_ids[depth[fold_ids] == d]
            # ---- cheap stage: inherited witnesses ----
            owners, cands = [], []
            no_cand = []
            for i in ids:
                c = gather_candidates(i)
                if c is None:
                    no_cand.append(i)
                    continue
                owners.append(np.full(len(c), i, dtype=np.int64))
                cands.append(c)
            n1 = 0
            survivors = []          # (id, seed_angle, cheap_mstar)
            if owners:
                owner = np.concatenate(owners)
                cand = np.concatenate(cands)
                slack = np.empty(len(owner))
                mstar = np.empty(len(owner))
                CH = 400_000
                for lo in range(0, len(owner), CH):
                    sl = slice(lo, lo + CH)
                    o = owner[sl]
                    slack[sl], mstar[sl] = eval_cert(
                        CENTERS[o], EPS_ALL[o], cand[sl, 0].astype(np.int64),
                        cand[sl, 1] / cand[sl, 3], cand[sl, 2] / cand[sl, 3])
                cut = np.nonzero(np.diff(owner))[0] + 1
                starts = np.concatenate([[0], cut])
                ends = np.concatenate([cut, [len(owner)]])
                for s0, s1 in zip(starts, ends):
                    g = owner[s0]
                    j = s0 + np.argmax(slack[s0:s1])
                    if slack[j] >= SLACK_MIN:
                        kill[g] = True
                        win[g] = cand[j]
                        n1 += 1
                    else:
                        jm = s0 + np.argmax(mstar[s0:s1])
                        seed = np.arctan2(float(cand[jm, 2]) / float(cand[jm, 3]),
                                          float(cand[jm, 1]) / float(cand[jm, 3]))
                        survivors.append((g, seed, mstar[jm]))
                        rows = np.arange(s0, s1)
                        if len(rows) > K_RES:
                            rows = rows[np.argsort(-mstar[rows])[:K_RES]]
                        reservoir[g] = cand[rows]
            stats["cheap_kill"] += n1

            # ---- exhaustive stage: coarse full-circle scan + refine ----
            tasks = [(int(g), float(seed)) for g, seed, m in survivors
                     if m >= min_mstar]
            tasks += [(int(g), float("nan")) for g in no_cand]

            def apply(out, _res=reservoir):
                i, accepted, res, _ = out
                if accepted is not None:
                    kill[i] = True
                    win[i] = accepted
                    _res.pop(i, None)
                    return 1
                prev = _res.get(i)
                _res[i] = np.unique(
                    np.concatenate([prev, res]) if prev is not None else res, axis=0)
                return 0

            n2 = run_pool(pool, tasks, apply, f"depth {d}") if tasks else 0
            stats["scan_kill"] += n2
            done_depths.add(int(d))
            checkpoint()
            print(f"depth {d}: folds={len(ids):>7}  cheap kills={n1:>7}  "
                  f"scan kills={n2:>7}  ({time.time() - t0:.0f}s)", flush=True)

    print(f"\ntotal kills: {kill.sum():,} of {len(fold_ids):,} folds "
          f"(cheap {stats['cheap_kill']:,}, scan {stats['scan_kill']:,})")

    # paranoia: re-verify every winner in isolation
    kids = np.nonzero(kill)[0]
    sl, _ = eval_cert(CENTERS[kids], EPS_ALL[kids], win[kids, 0],
                      win[kids, 1] / win[kids, 3], win[kids, 2] / win[kids, 3])
    assert (sl >= SLACK_MIN).all(), "winner re-verification failed!"
    assert (win[kids, 1]**2 + win[kids, 2]**2 == win[kids, 3]**2).all(), "non-Pythagorean w!"
    print("winner re-verification passed")

    # ---------------- emission (BFS renumber, prune killed subtrees) ----------------
    print("\nemitting pruned tree ...", flush=True)

    def fmt(v, na):
        return "" if na else str(int(v))

    bT = [bounds[p + s] for p in PARAMS for s in ["_min", "_max"]]
    queue = deque([0])
    new_id_of = {0: 0}
    next_id = 1
    n_out = 0
    with open(pruned_path, "w") as f:
        f.write(HEADER + "\n")
        while queue:
            i = queue.popleft()
            nid = new_id_of.pop(i)
            b = ",".join(str(x[i]) for x in bT)
            if kill[i]:
                line = (f"{nid},1,,,,{b},,,,,,,,,"
                        f"{win[i, 1]},{win[i, 2]},{win[i, 3]},{win[i, 0]}")
            elif node_type[i] == 3:
                fcid = next_id
                for k in range(nr_children[i]):
                    new_id_of[first_child[i] + k] = next_id
                    queue.append(first_child[i] + k)
                    next_id += 1
                line = f"{nid},3,{nr_children[i]},{fcid},{splitk[i]},{b},,,,,,,,,,,,"
            else:
                m = ",".join(fmt(misc[c][i], misc_na[c][i]) for c in INT_COLS)
                if wna[i]:
                    wpart = ",,,"
                    spart = ""
                else:
                    wpart = f"{wxA[i]},{wyA[i]},{wdA[i]},"
                    spart = f"{s_idx[i]}"
                line = f"{nid},{node_type[i]},,,,{b},{m},{wpart}{spart}"
            f.write(line + "\n")
            n_out += 1
    print(f"wrote {pruned_path}: {n_out:,} rows (was {n:,}; {n / n_out:.2f}x smaller)")


# ================== PASS 2: flip local -> global (pruned -> v4) ==================

def find_flips(df, workers, min_mstar, ckpt_dir, resume):
    global CENTERS, EPS_ALL
    n = len(df)
    nt = df["nodeType"].to_numpy(np.int8)
    fc = df["IDfirstChild"].fillna(0).to_numpy(np.int64)
    nrc = df["nrChildren"].fillna(0).to_numpy(np.int64)
    s_idx = df["S_index"].fillna(0).to_numpy(np.int16)
    wxA = df["wx_nominator"].fillna(0).to_numpy(np.int64)
    wyA = df["wy_nominator"].fillna(0).to_numpy(np.int64)
    wdA = df["w_denominator"].fillna(0).to_numpy(np.int64)
    bmin = np.stack([df[p + "_min"].to_numpy(np.int64) for p in PARAMS], axis=1)
    bmax = np.stack([df[p + "_max"].to_numpy(np.int64) for p in PARAMS], axis=1)
    del df
    CENTERS = (bmin + bmax) / (2 * DENOM)
    EPS_ALL = ((bmax - bmin).max(axis=1) / 2) / DENOM

    parent = np.full(n, -1, dtype=np.int64)
    for i in np.nonzero(nt == 3)[0]:
        parent[fc[i]:fc[i] + nrc[i]] = i

    locals_ = np.nonzero(nt == 2)[0]
    print(f"local leaves: {len(locals_):,}")

    flip = {}
    done = set()
    ckpt = os.path.join(ckpt_dir, "pass2_state.pkl")
    if resume and os.path.exists(ckpt):
        st = pickle.load(open(ckpt, "rb"))
        flip, done = st["flip"], st["done"]
        print(f"resumed pass 2: {len(done):,} boxes scanned, {len(flip):,} flips so far")

    # cheap stage: sibling witnesses
    owners, cands = [], []
    no_sib = []
    for i in locals_:
        par = parent[i]
        kids = np.arange(fc[par], fc[par] + nrc[par])
        gl = kids[nt[kids] == 1]
        if len(gl) == 0:
            no_sib.append(i)
            continue
        c = np.unique(np.stack([s_idx[gl].astype(np.int64), wxA[gl], wyA[gl], wdA[gl]], axis=1), axis=0)
        owners.append(np.full(len(c), i, dtype=np.int64))
        cands.append(c)
    owner = np.concatenate(owners)
    cand = np.concatenate(cands)
    print(f"cheap-stage candidate rows: {len(owner):,}", flush=True)
    slack = np.empty(len(owner))
    mstar = np.empty(len(owner))
    CH = 400_000
    for lo in range(0, len(owner), CH):
        sl = slice(lo, lo + CH)
        o = owner[sl]
        slack[sl], mstar[sl] = eval_cert(CENTERS[o], EPS_ALL[o], cand[sl, 0].astype(np.int64),
                                         cand[sl, 1] / cand[sl, 3], cand[sl, 2] / cand[sl, 3])
    cut = np.nonzero(np.diff(owner))[0] + 1
    starts = np.concatenate([[0], cut])
    ends = np.concatenate([cut, [len(owner)]])
    n1 = 0
    survivors = []
    for s0, s1 in zip(starts, ends):
        g = int(owner[s0])
        if g in flip or g in done:
            continue
        j = s0 + np.argmax(slack[s0:s1])
        if slack[j] >= SLACK_MIN:
            flip[g] = cand[j].tolist()
            n1 += 1
        else:
            jm = s0 + np.argmax(mstar[s0:s1])
            seed = np.arctan2(float(cand[jm, 2]) / float(cand[jm, 3]),
                              float(cand[jm, 1]) / float(cand[jm, 3]))
            survivors.append((g, seed, mstar[jm]))
    print(f"cheap-stage flips: {n1:,}", flush=True)

    tasks = [(g, float(seed)) for g, seed, m in survivors if m >= min_mstar]
    tasks += [(int(g), float("nan")) for g in no_sib if int(g) not in done and int(g) not in flip]

    def checkpoint():
        save_pickle(ckpt, {"flip": flip, "done": done})

    def apply(out):
        i, accepted, _, _ = out
        done.add(i)
        if accepted is not None:
            flip[i] = accepted
            return 1
        return 0

    with mp.Pool(workers) as pool:
        n2 = run_pool(pool, tasks, apply, "flip scan",
                      ckpt_every=25_000, ckpt_fn=checkpoint)
    checkpoint()
    print(f"scan flips: {n2:,}")
    print(f"total flips: {len(flip):,} / {len(locals_):,} ({len(flip) / len(locals_) * 100:.1f}%)")
    return flip


def apply_flips(pruned_path, v4_path, flip):
    bad = [k for k, (s, wx, wy, wd) in flip.items()
           if int(wx)**2 + int(wy)**2 != int(wd)**2 or int(wd) <= 0 or not (0 <= int(s) < 90)]
    assert not bad, bad[:5]
    print("all flip witnesses exactly Pythagorean")

    flips = {str(k): v for k, v in flip.items()}
    n_flipped = 0
    counts = {}
    with open(pruned_path) as f, open(v4_path, "w") as g:
        g.write(f.readline())      # header
        for line in f:
            rid = line[:line.index(",")]
            w = flips.get(rid)
            if w is None:
                nt = line.split(",", 2)[1]
                g.write(line)
            else:
                cols = line.rstrip("\n").split(",")
                assert cols[1] == "2", (rid, cols[1])
                b = ",".join(cols[5:15])
                s, wx, wy, wd = w
                g.write(f"{rid},1,,,,{b},,,,,,,,,{wx},{wy},{wd},{s}\n")
                n_flipped += 1
                nt = "1"
            counts[nt] = counts.get(nt, 0) + 1
    assert n_flipped == len(flips)
    print(f"wrote {v4_path}: flipped {n_flipped:,} rows")
    total = sum(counts.values())
    print(f"final composition: total={total:,} split={counts.get('3', 0):,} "
          f"global={counts.get('1', 0):,} local={counts.get('2', 0):,}")


def main():
    global verts, Px, Py, Pz
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--input", required=True,
                    help="original solution_tree.csv (or .parquet)")
    ap.add_argument("--verts", required=True, help="verts90.json")
    ap.add_argument("--pruned-out", required=True,
                    help="output path for the intermediate pruned tree csv")
    ap.add_argument("--v4-out", required=True, help="output path for solution_tree_v4.csv")
    ap.add_argument("--workers", type=int, default=min(16, os.cpu_count()),
                    help="parallel scan workers (default: min(16, cpus))")
    ap.add_argument("--coarse-angles", type=int, default=1024,
                    help="full-circle w-angle grid size (default 1024)")
    ap.add_argument("--refine-top", type=int, default=6,
                    help="coarse candidates refined per box (default 6)")
    ap.add_argument("--min-mstar", type=float, default=0.0,
                    help="skip exhaustive scan for boxes whose cheap-stage m* is "
                         "below this (default 0.0 = scan everything)")
    ap.add_argument("--checkpoint-dir", default=None,
                    help="checkpoint directory (default: alongside --v4-out)")
    ap.add_argument("--resume", action="store_true",
                    help="resume from checkpoints in --checkpoint-dir")
    ap.add_argument("--skip-prune", action="store_true",
                    help="reuse an existing --pruned-out file (skip pass 1)")
    args = ap.parse_args()

    verts = np.array(json.load(open(args.verts)))
    assert verts.shape == (90, 3)
    Px, Py, Pz = verts[:, 0], verts[:, 1], verts[:, 2]
    init_scan_grids(args.coarse_angles, args.refine_top)
    ckpt_dir = args.checkpoint_dir or os.path.dirname(os.path.abspath(args.v4_out))
    os.makedirs(ckpt_dir, exist_ok=True)

    if not args.skip_prune:
        print("=== PASS 1: prune (original -> pruned), exhaustive witness search ===")
        print("loading original table ...", flush=True)
        df = load_table(args.input)
        print(f"{len(df):,} rows")
        prune(df, args.pruned_out, args.workers, args.min_mstar, ckpt_dir, args.resume)

    print("\n=== PASS 2: flip local leaves to global (pruned -> v4) ===")
    print("loading pruned tree ...", flush=True)
    df2 = load_table(args.pruned_out)
    print(f"{len(df2):,} rows")
    flip = find_flips(df2, args.workers, args.min_mstar, ckpt_dir, args.resume)
    apply_flips(args.pruned_out, args.v4_out, flip)


if __name__ == "__main__":
    main()
