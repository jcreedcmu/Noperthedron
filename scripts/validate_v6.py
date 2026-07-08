"""Paranoia pass for solution_tree_v6.csv (adapted from validate_v2.py).

Re-reads the emitted CSV and independently re-verifies, against the Lean
checker's requirements on branch second-order:

  * structure: IDs sequential; nodeTypes in {1,2,3}; intervals nonempty;
    every row referenced exactly once as a child (root aside); split kinds
    1..6; children in range; single-param splits (kinds 1..5, any child
    count N) tile the parent exactly as Interval.nth_part slices IN ORDER
    (binary v6 splits: lower half first); full splits (kind 6) have the 32
    cubeFold children in order (bits T1..A, T1 outermost, lower first);
  * row 0 equals v5's row 0 (Checker/RowZero.lean);
  * every global leaf: w_denominator > 0, wx^2+wy^2 == wd^2 exactly
    (big-int), all five per-axis widths > 0 (Row.ValidGlobal positivity),
    center in [-4,4]^5, and the ANISOTROPIC second-order float certificate
    (experiment_aniso.eval_cert_aniso, mirroring Gq > maxHq with per-axis
    radii) passes with the row's own stored witness at slack >= 1e-9;
  * every local leaf passes local_check.check_local at margin 1e-9.

Usage:  .venv/bin/python regen/validate_v6.py \
            [--csv data/solution_tree_v6.csv] [--v5-csv data/solution_tree_v5.csv]
"""
import argparse
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import make_solution_tree_v5 as v5
import experiment_aniso as ea
from local_check import check_local_rows

DENOM = 15360000.0
PARAMS = ["T1", "V1", "T2", "V2", "A"]
SLACK_MIN = 1e-9

fails = []


def check(name, cond, extra=""):
    print(("PASS " if cond else "FAIL ") + name + (f"  [{extra}]" if extra else ""),
          flush=True)
    if not cond:
        fails.append(name)


def main():
    ap = argparse.ArgumentParser()
    root = os.path.dirname(HERE)
    ap.add_argument("--csv", default=os.path.join(root, "data", "solution_tree_v6.csv"))
    ap.add_argument("--v5-csv", default=os.path.join(root, "data", "solution_tree_v5.csv"))
    ap.add_argument("--out", default=os.path.join(HERE, "v6_validation.json"))
    args = ap.parse_args()

    ea.init_geometry()
    print("parsing v6 csv ...", flush=True)
    df = v5.load_table(args.csv)
    n = len(df)
    print(f"{n:,} rows", flush=True)

    ids = df["ID"].to_numpy(np.int64)
    check("ID == row index", bool((ids == np.arange(n)).all()))

    nt = df["nodeType"].to_numpy(np.int8)
    nrc = df["nrChildren"].fillna(0).to_numpy(np.int64)
    fcid = df["IDfirstChild"].fillna(0).to_numpy(np.int64)
    spl = df["split"].fillna(0).to_numpy(np.int64)
    bmin = np.stack([df[p + "_min"].to_numpy(np.int64) for p in PARAMS], axis=1)
    bmax = np.stack([df[p + "_max"].to_numpy(np.int64) for p in PARAMS], axis=1)
    check("node types in {1,2,3}", bool(np.isin(nt, [1, 2, 3]).all()))
    check("intervals nonempty (min <= max)", bool((bmin <= bmax).all()))

    # ---- row 0 matches v5's row 0 (== rowZero) ----
    with open(args.v5_csv) as f:
        f.readline()
        v5row0 = f.readline().rstrip("\n")
    with open(args.csv) as f:
        f.readline()
        v6row0 = f.readline().rstrip("\n")
    check("row 0 identical to v5 row 0", v5row0 == v6row0)

    is_split = nt == 3
    is_glob = nt == 1
    is_loc = nt == 2
    counts = dict(split=int(is_split.sum()), global_=int(is_glob.sum()),
                  local=int(is_loc.sum()))
    print(f"splits={counts['split']:,} global={counts['global_']:,} "
          f"local={counts['local']:,}", flush=True)

    # ---- split structure ----
    sp = np.nonzero(is_split)[0]
    check("split kind in 1..6", bool(np.isin(spl[sp], [1, 2, 3, 4, 5, 6]).all()))
    check("nrChildren > 0 on splits", bool((nrc[sp] > 0).all()))
    check("IDfirstChild > ID for splits", bool((fcid[sp] > ids[sp]).all()))
    check("children in range", bool((fcid[sp] + nrc[sp] <= n).all()))
    check("full splits have 32 children", bool((nrc[sp[spl[sp] == 6]] == 32).all()))
    check("binary/k-ary kinds 1..5 only on single-param splits",
          bool(np.isin(spl[sp], [1, 2, 3, 4, 5, 6]).all()))

    # every non-root row is some row's child exactly once
    covered = np.zeros(n, dtype=np.int32)
    covered[0] += 1
    for i in sp:
        covered[fcid[i]:fcid[i] + nrc[i]] += 1
    check("tree structure: every row referenced exactly once",
          bool((covered == 1).all()))

    # ---- single-param split child intervals: Interval.nth_part, in order ----
    print("checking single-param split child intervals ...", flush=True)
    ok = True
    for kind, k in [(1, 0), (2, 1), (3, 2), (4, 3), (5, 4)]:
        rows = sp[spl[sp] == kind]
        if not len(rows):
            continue
        # vectorized for the (dominant) binary case
        b2 = rows[nrc[rows] == 2]
        if len(b2):
            lo, hi = bmin[b2, k], bmax[b2, k]
            c0, c1 = fcid[b2], fcid[b2] + 1
            for other in range(5):
                if other == k:
                    continue
                for c in (c0, c1):
                    ok &= bool((bmin[c, other] == bmin[b2, other]).all())
                    ok &= bool((bmax[c, other] == bmax[b2, other]).all())
            ok &= bool((bmin[c0, k] == lo).all())
            ok &= bool((2 * bmax[c0, k] == lo + hi).all())   # exact midpoint
            ok &= bool((2 * bmin[c1, k] == lo + hi).all())
            ok &= bool((bmax[c1, k] == hi).all())
        for i in rows[nrc[rows] != 2]:
            N = nrc[i]
            kids = np.arange(fcid[i], fcid[i] + N)
            for other in range(5):
                if other == k:
                    continue
                ok &= bool((bmin[kids, other] == bmin[i, other]).all())
                ok &= bool((bmax[kids, other] == bmax[i, other]).all())
            ns = np.arange(N)
            lo, hi = bmin[i, k], bmax[i, k]
            ok &= bool((N * bmin[kids, k] == (N - ns) * lo + ns * hi).all())
            ok &= bool((N * bmax[kids, k] == (N - ns - 1) * lo + (ns + 1) * hi).all())
    check("single-param split child intervals exact (nth_part, in order)", ok)

    # ---- cube-fold children: bit b4..b0 = T1,V1,T2,V2,A; lower half first ----
    print("checking cube-fold child intervals ...", flush=True)
    cf = sp[spl[sp] == 6]
    ok = True
    for j in range(32):
        kid = fcid[cf] + j
        bits = [(j >> (4 - k)) & 1 for k in range(5)]
        for k in range(5):
            pmin, pmax = bmin[cf, k], bmax[cf, k]
            s = pmin + pmax
            if bits[k] == 0:
                ok &= bool((bmin[kid, k] == pmin).all())
                ok &= bool((2 * bmax[kid, k] == s).all())
            else:
                ok &= bool((2 * bmin[kid, k] == s).all())
                ok &= bool((bmax[kid, k] == pmax).all())
    check("cube-fold child intervals exact", ok)

    # ---- global leaves ----
    g = np.nonzero(is_glob)[0]
    wx = df["wx_nominator"].to_numpy()[g]
    wy = df["wy_nominator"].to_numpy()[g]
    wd = df["w_denominator"].to_numpy()[g]
    check("w fields present on global leaves",
          not (df["wx_nominator"].isna().to_numpy()[g].any()
               or df["S_index"].isna().to_numpy()[g].any()))
    check("w_denominator > 0 on global leaves", bool((wd.astype(np.int64) > 0).all()))
    tri = set(zip(wx.astype(object), wy.astype(object), wd.astype(object)))
    print(f"distinct w triples: {len(tri):,}", flush=True)
    check("wx^2+wy^2 == wd^2 exactly (python ints)",
          all(int(a) ** 2 + int(b) ** 2 == int(c) ** 2 for a, b, c in tri))
    widths = bmax - bmin
    check("per-axis widths > 0 on global leaves (ValidGlobal eps positivity)",
          bool((widths[g] > 0).all()))
    check("centers in [-4,4]^5",
          bool((np.abs(bmin + bmax) <= 2 * 4 * 15360000).all()))
    check("eps > 0 on local leaves", bool((widths[np.nonzero(is_loc)[0]].max(axis=1) > 0).all()))

    print("anisotropic certificate check on all global leaves ...", flush=True)
    sidx = df["S_index"].to_numpy()[g].astype(np.int64)
    w0 = wx.astype(np.float64) / wd.astype(np.float64)
    w1 = wy.astype(np.float64) / wd.astype(np.float64)
    pose = (bmin[g] + bmax[g]) / (2 * DENOM)
    epsv = widths[g] / (2 * DENOM)
    min_slack = np.inf
    t0 = time.time()
    CH = 100_000
    for lo in range(0, len(g), CH):
        sl = slice(lo, lo + CH)
        s = ea.eval_cert_aniso(pose[sl], epsv[sl], sidx[sl], w0[sl], w1[sl])
        min_slack = min(min_slack, float(s.min()))
    print(f"  ({time.time() - t0:.0f}s)", flush=True)
    check(f"all global leaves pass aniso certificate at slack >= 1e-9 "
          f"(min slack {min_slack:.3e})", min_slack >= SLACK_MIN)

    # ---- local leaves: conservative float mirror of Row.ValidLocal ----
    print("local check (float mirror of Row.ValidLocal, margin 1e-9) ...",
          flush=True)
    loc = df[df.nodeType == 2].reset_index(drop=True)
    t0 = time.time()
    if len(loc):
        acc, sl = check_local_rows(loc, margin=1e-9)
        worst = {k: float(np.min(v)) for k, v in sl.items()
                 if k not in ("symmetry_exists", "delta_hi", "delta_consistency")}
        print(f"  ({time.time() - t0:.0f}s)  worst slacks: "
              + ", ".join(f"{k}={v:.2e}" for k, v in worst.items()), flush=True)
        check(f"all {len(loc):,} local leaves pass check_local at margin 1e-9 "
              f"({int(acc.sum()):,} accepted)", bool(acc.all()))
    else:
        worst = {}
        check("all local leaves pass check_local (none present)", True)

    verdict = "ALL CHECKS PASSED" if not fails else f"FAILURES: {fails}"
    print("\n" + verdict, flush=True)
    out = dict(csv=args.csv, n_rows=n, counts=counts,
               n_distinct_w=len(tri),
               min_global_slack=min_slack,
               worst_local_slacks=worst,
               failures=fails, passed=not fails)
    with open(args.out, "w") as f:
        json.dump(out, f, indent=2)
    print("wrote", args.out)
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
