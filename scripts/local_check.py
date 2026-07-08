"""Float64 mirror of the Lean checker's LOCAL leaf check `Row.ValidLocal`.

Ground truth (branch second-order of ~/src/Noperthedron):
  - Noperthedron/Checker/Local.lean          (Row.ValidLocal, Spanningℚ, Row.δ, BεℚPy.check)
  - Noperthedron/RationalApprox/RationalLocal.lean (Aεℚσ, Bεℚ.lhs/check, BoundRℚ, BoundDeltaℚi)
  - Noperthedron/RationalApprox/Basic.lean   (sinℚ/cosℚ, round13, κℚ, vecXℚ, rotM₂Rℚ)
  - Noperthedron/Checker/ApproxSqrt.lean     (sqrtℚLow/sqrtℚUp, sqrtApprox: 1.42, 2.24)
  - Noperthedron/Vertices/Symmetry.lean      (TriangleSymmetry rotation/reflection)

The Lean check is exact rational arithmetic; this module evaluates the same
formulas in float64 and subtracts a rigorous error budget from every strict
inequality, so that `slack > margin` here implies (up to the budget's
correctness) that the exact Lean check accepts.  Conversely a Lean-accepted
row can only be rejected here if its true slack is below the (tiny) budget.

================================ ERROR BUDGET ================================

Let t := per-row trig budget, computed from A = max |center angle|:

    t = 1e-13  (round13: sinℚ x = floor(psum * 1e13)/1e13, one-sided down,
                |round13 y - y| <= 1e-13)
      + A^26/26! + A^27/27!  (Taylor truncation: sinℚ/cosℚ are the degree-25/24
                partial sums; alternating series remainders are <= first
                omitted term, x^27/27! for sin and x^26/26! for cos; we add
                both so one constant covers either.  A <= 3.15 in the v5 data
                => <= 2.6e-14)
      + 1e-15  (np.sin/np.cos ulp error ~2e-16, plus the float64 rounding of
                the box-center angle (min+max)/(2*DENOM), ~2.5e-16 phase)

  so |sinℚ(x_exact) - np.sin(x_float)| <= t  (same for cos).  t ~ 1.3e-13.

round13 of applied vectors (rotM₂Rℚ = round13v(M₂ v)): modeled as an extra
  +-1e-13 (R13) on each rounded component, NOT simulated.

sqrt (ApproxSqrt.lean): sqrtℚLow x = floor(sqrt(m)) * 10^-a with
  m = floor(x*100^a) in [10^20, 10^22).  Hence b = floor(sqrt m) >= 10^10 and
    sqrt(x)*(1 - 1.01e-10) <= sqrtℚLow x <= sqrt(x)
  (b <= sqrt(m) <= sqrt(x*100^a); b > sqrt(m)-1 >= sqrt(x*100^a) - 1 - 5.1e-11
   and sqrt(x*100^a) >= 1e10 gives the relative bound).
  sqrtℚUp x = 1/sqrtℚLow(1/x), so
    sqrt(x) <= sqrtℚUp x <= sqrt(x)*(1 + 1.02e-10)  =: (1 + REL_SQRT).
  In float we use sqrt(arg_lo) resp. sqrt(arg_hi)*(1+REL_SQRT) as one-sided
  bounds of the Lean value, where arg_lo/hi absorb the argument's own budget.

vertices: regen/verts90.json = float64 of the exact pythonVertex rationals
  (integer/1e16), rep error <= 1.2e-16/coordinate; covered by SLOP.

SLOP = 1e-14: generic per-inequality allowance for float64 arithmetic
  rounding of the O(30)-term expressions at O(1) magnitudes (each op is
  <= 1.1e-16 relative), vertex rep error, and r = r'/1000 rep error.

Where each budget enters (conjunct -> budget subtracted from float slack):

  X1/X2 (Aεℚσ)     dot(X, v) with X = vecXℚ products of two trigs:
                   5t + SLOP.
  P/Q_span         <rot90 M v, M w>: entries err <= 2t, |values| <= 1.01:
                   15t + SLOP.
  r_valid          q = round13(M₂ v): EQ0 = 2t + 1e-13, EQ1 = 5t + 1e-13;
                   arg = q0²+q1² gets 2(|q0|EQ0 + |q1|EQ1) + EQ²; lower_sqrt
                   lower bound sqrt(arg - err)*(1 - REL_SQRT) - SLOP.
  δ (Row.δ)        unrounded R·M₁P - M₂Q: component budgets 11.5t / 14.5t
                   (M₁P: 2t/5t; rotR mixes: +|ca|2t+|sa|5t+2.02t <= 9.5t;
                   minus M₂Q: +2t/5t); upper_sqrt band => [δ_lo, δ_hi];
                   B_eps uses δ_hi (conservative).
  B_eps            bound_hi = (δ_hi + 2.24 ε)/r + SLOP;
                   numer_lo = q·d - (|q|ED + |d|EQ + EQ·ED) - 10κ
                              - 2ε(n_dv*(1+REL_SQRT) + 2κ)(1.42 + ε) - SLOP,
                   ED0 = (|dv0|+|dv1|)t + 1e-13,
                   ED1 = (2|dv0|+2|dv1|+|dv2|)t + 1e-13;
                   denom_hi = sqrt(arg + err)*(1+REL_SQRT) + eps/κ terms + SLOP;
                   slack = numer_lo/(denom1_hi*denom2_hi) - bound_hi.

===================== LEAN-DEFINITION SUBTLETIES (for v6) ====================

* CSV column order T1,V1,T2,V2,A = θ₁,φ₁,θ₂,φ₂,α; center = (min+max)/2/DENOM,
  ε = Row.epsilon = PoseInterval.radius = (max side)/2/DENOM (sup metric),
  r = r'/1000, σ_Q ∈ {0,1}.
* Aεℚσ: X₁ conjunct always uses σ = 0; X₂ uses σ = row.sigma_Q.
  RHS is 1.42ε + 3κ (upper_sqrt_two is the CONSTANT 1.42, not a sqrt call).
* Spanningℚ: strict `2ε(1.42+ε) + 6κ < <rot90·Mv_i, Mv_{i+1}>` for i = 0,1,2
  cyclically (i+1 mod 3), with sqrt_twoℚ = 142/100 = 1.42.
* Row.δ = max_i [ upper_sqrt(‖R·M₁P_i − M₂Q_i‖²)/2 + 3κ ]; the applied
  vectors here are NOT round13'd (only the trig values are).  ValidLocal
  does not store δ: the Lean checker recomputes it and feeds it to Bεℚ.
* BoundRℚ and Bεℚ DO round13 the applied 2-vectors componentwise
  (rotM₂Rℚ = round13v ∘ M₂), including M₂(Q_i − v_k) — rounding is applied
  AFTER the matrix multiply of the difference vector.
* Bεℚ's n_dv term is the 3-D norm upper_sqrt(‖Q_i − v_k‖²) of the UNROUNDED
  difference (pose independent, table `sqrtDv` in Lean).
* Bεℚ's inner ∀ k ranges over ALL 90 vertices except Q_i itself (the other
  two Q vertices and the P vertices are included as k).
* matEntries m₀₂ = 0 exactly (first row of rotMℚ_mat is (−sinθ, cosθ, 0)).
* TriangleSymmetry (flat index j = k + 15·i + 45·ℓ, k∈[0,15), i∈[0,3),
  ℓ∈[0,2)): rotation(m,n): (k,ℓ,i) ↦ ((k+n)%15, (ℓ+m)%2, i), applicable to
  every triangle; reflection(m,n): (k,ℓ,i) ↦ ((15−k+n)%15, (ℓ+m)%2, i),
  applicable only when (Q 0).i = (Q 1).i = (Q 2).i.  ValidLocal needs some
  s with s.applicable Qi and ∀ j, Pi j = s.apply (Qi j).
* center_in_fourQ: every center angle ∈ [−4, 4] (non-strict).
* epsilon_pos (0 < ε) and rpos (0 < r) are also conjuncts.
"""

import json
import os

import numpy as np

DENOM = 15360000.0
KAPPA = 1e-10          # κℚ = 1/10^10
US2 = 1.42             # sqrtApprox.upper_sqrt_two (= sqrt_twoℚ = 142/100)
US5 = 2.24             # sqrtApprox.upper_sqrt_five
REL_SQRT = 1.02e-10    # one-sided relative bound on sqrtℚUp/sqrtℚLow (see header)
R13 = 1e-13            # |round13 y - y| <= 1e-13
SLOP = 1e-14           # generic float64 arithmetic allowance per inequality

_HERE = os.path.dirname(os.path.abspath(__file__))
VERTS = np.array(json.load(open(os.path.join(_HERE, "verts90.json"))), dtype=np.float64)
assert VERTS.shape == (90, 3)
# Pairwise difference table DV[a,b,:] = V[a] - V[b] and its 3-D norms
DV = VERTS[:, None, :] - VERTS[None, :, :]
NDV = np.sqrt((DV ** 2).sum(-1))

_FACT26 = 403291461126605635584000000.0   # 26!
_FACT27 = _FACT26 * 27.0                   # 27!

CONJUNCTS = ["center_in_fourQ", "epsilon_pos", "symmetry_exists", "X1", "X2",
             "P_span", "Q_span", "rpos", "r_valid", "B_eps", "delta_consistency"]


def _trig_budget(maxang):
    """Per-row bound on |sinℚ/cosℚ(exact center) - np.sin/cos(float center)|."""
    a = np.abs(maxang)
    taylor = a ** 26 / _FACT26 + a ** 27 / _FACT27
    return R13 + taylor + 1e-15


def _symmetry_exists(P, Q):
    """Exact TriangleSymmetry search (Vertices/Symmetry.lean), vectorized.

    P, Q: (n,3) int arrays of flat vertex indices j = k + 15*i + 45*l.
    Returns bool (n,).
    """
    P = np.asarray(P, dtype=np.int64)
    Q = np.asarray(Q, dtype=np.int64)
    pk, pl, pi = P % 15, P // 45, (P % 45) // 15
    qk, ql, qi = Q % 15, Q // 45, (Q % 45) // 15
    i_ok = (pi == qi).all(axis=1)                      # apply preserves orbit i
    m = (pl - ql) % 2                                  # ℓ' = ℓ + m
    m_ok = (m[:, 0] == m[:, 1]) & (m[:, 1] == m[:, 2])
    # rotation(m,n): k' = (k + n) % 15  =>  n = (pk - qk) % 15 constant
    nrot = (pk - qk) % 15
    rot = i_ok & m_ok & (nrot[:, 0] == nrot[:, 1]) & (nrot[:, 1] == nrot[:, 2])
    # reflection(m,n): k' = (15 - k + n) % 15  =>  n = (pk + qk) % 15 constant,
    # applicable only if all Q vertices share one orbit
    nref = (pk + qk) % 15
    orbit = (qi[:, 0] == qi[:, 1]) & (qi[:, 1] == qi[:, 2])
    ref = i_ok & m_ok & orbit & (nref[:, 0] == nref[:, 1]) & (nref[:, 1] == nref[:, 2])
    return rot | ref


def _check_chunk(centers, eps, P, Q, r, sigma):
    """Core check on flat arrays. centers: (n,5) in CSV order (θ₁,φ₁,θ₂,φ₂,α).

    Returns dict of (n,) conservative slack arrays (Lean slack >= float slack).
    """
    n = centers.shape[0]
    t1, f1, t2, f2, al = (centers[:, j] for j in range(5))
    st1, ct1, sf1, cf1 = np.sin(t1), np.cos(t1), np.sin(f1), np.cos(f1)
    st2, ct2, sf2, cf2 = np.sin(t2), np.cos(t2), np.sin(f2), np.cos(f2)
    sa, ca = np.sin(al), np.cos(al)
    t = _trig_budget(np.abs(centers).max(axis=1))

    PV = VERTS[P]          # (n,3,3): PV[:,i,:] = vertex P_i
    QV = VERTS[Q]

    out = {}
    out["center_in_fourQ"] = 4.0 - np.abs(centers).max(axis=1) + 1e-15
    out["epsilon_pos"] = eps.copy()
    out["rpos"] = r.copy()
    out["symmetry_exists"] = np.where(_symmetry_exists(P, Q), 1.0, -1.0)

    # ---- Aεℚσ: (-1)^σ <X, v_i>  >  1.42 ε + 3κ ------------------------------
    a_rhs = US2 * eps + 3 * KAPPA
    bud_x = 5 * t + SLOP

    def aeps_slack(st, ct, sf, cf, TV, sgn):
        x0, x1, x2 = ct * sf, st * sf, cf
        dots = (x0[:, None] * TV[:, :, 0] + x1[:, None] * TV[:, :, 1]
                + x2[:, None] * TV[:, :, 2])
        return (sgn[:, None] * dots).min(axis=1) - a_rhs - bud_x

    ones = np.ones(n)
    out["X1"] = aeps_slack(st1, ct1, sf1, cf1, PV, ones)             # σ = 0
    out["X2"] = aeps_slack(st2, ct2, sf2, cf2, QV, np.where(sigma % 2 == 1, -1.0, 1.0))

    # ---- Spanningℚ: 2ε(1.42+ε) + 6κ < <rot90·Mv_i, Mv_{i+1}> ----------------
    sp_lhs = 2 * eps * (US2 + eps) + 6 * KAPPA
    bud_sp = 15 * t + SLOP

    def span_slack(st, ct, sf, cf, TV):
        worst = np.full(n, np.inf)
        for i in range(3):
            v = TV[:, i, :]
            w = TV[:, (i + 1) % 3, :]
            dot = (-(-ct * cf * v[:, 0] + -st * cf * v[:, 1] + sf * v[:, 2])
                   * (-st * w[:, 0] + ct * w[:, 1])
                   + (-st * v[:, 0] + ct * v[:, 1])
                   * (-ct * cf * w[:, 0] + -st * cf * w[:, 1] + sf * w[:, 2]))
            worst = np.minimum(worst, dot - sp_lhs - bud_sp)
        return worst

    out["P_span"] = span_slack(st1, ct1, sf1, cf1, PV)
    out["Q_span"] = span_slack(st2, ct2, sf2, cf2, QV)

    # ---- matEntries(θ₂, φ₂) (rows of rotMℚ_mat; m02 = 0 exactly) ------------
    m00, m01 = -st2, ct2
    m10, m11, m12 = -ct2 * cf2, -st2 * cf2, sf2
    EQ0 = 2 * t + R13          # budget of q0 = round13(m00 v0 + m01 v1)
    EQ1 = 5 * t + R13          # budget of q1 = round13(m10 v0 + m11 v1 + m12 v2)

    # ---- BoundRℚ: lower_sqrt(q0²+q1²) > r + 1.42 ε + 3κ  (per Q_i) ----------
    br_rhs = r + US2 * eps + 3 * KAPPA + SLOP
    r_slack = np.full(n, np.inf)
    q0s, q1s = [], []          # keep for B_eps denom1
    for i in range(3):
        v = QV[:, i, :]
        q0 = m00 * v[:, 0] + m01 * v[:, 1]
        q1 = m10 * v[:, 0] + m11 * v[:, 1] + m12 * v[:, 2]
        q0s.append(q0)
        q1s.append(q1)
        arg = q0 * q0 + q1 * q1
        err = 2 * (np.abs(q0) * EQ0 + np.abs(q1) * EQ1) + EQ0 ** 2 + EQ1 ** 2 + SLOP
        lhs_lo = np.sqrt(np.maximum(arg - err, 0.0)) * (1 - REL_SQRT) - SLOP
        r_slack = np.minimum(r_slack, lhs_lo - br_rhs)
    out["r_valid"] = r_slack

    # ---- Row.δ = max_i upper_sqrt(‖R·M₁P_i − M₂Q_i‖²)/2 + 3κ  (no round13) --
    d_hi = np.full(n, -np.inf)
    d_lo = np.full(n, -np.inf)
    for i in range(3):
        Pv = PV[:, i, :]
        Qv = QV[:, i, :]
        m1p0 = -st1 * Pv[:, 0] + ct1 * Pv[:, 1]
        m1p1 = -ct1 * cf1 * Pv[:, 0] - st1 * cf1 * Pv[:, 1] + sf1 * Pv[:, 2]
        rm0 = ca * m1p0 - sa * m1p1
        rm1 = sa * m1p0 + ca * m1p1
        m2q0 = -st2 * Qv[:, 0] + ct2 * Qv[:, 1]
        m2q1 = -ct2 * cf2 * Qv[:, 0] - st2 * cf2 * Qv[:, 1] + sf2 * Qv[:, 2]
        d0 = rm0 - m2q0
        d1 = rm1 - m2q1
        e0 = 11.5 * t + SLOP   # 9.5t (R·M₁P component) + 2t (M₂Q row 0)
        e1 = 14.5 * t + SLOP   # 9.5t + 5t (M₂Q row 1)
        nsq = d0 * d0 + d1 * d1
        ensq = 2 * (np.abs(d0) * e0 + np.abs(d1) * e1) + e0 ** 2 + e1 ** 2 + SLOP
        d_hi = np.maximum(d_hi, np.sqrt(nsq + ensq) * (1 + REL_SQRT) / 2 + 3 * KAPPA + SLOP)
        d_lo = np.maximum(d_lo, np.sqrt(np.maximum(nsq - ensq, 0.0)) / 2 + 3 * KAPPA - SLOP)
    out["delta_hi"] = d_hi
    out["delta_consistency"] = d_hi - d_lo   # informational: width of the δ model band

    # ---- Bεℚ: (δ + 2.24 ε)/r < numer/(denom1·denom2) for i∈3, k≠Q_i ---------
    bound_hi = (d_hi + US5 * eps) / r + SLOP
    b_slack = np.full(n, np.inf)
    two_eps_f = 2 * eps * (US2 + eps)      # factor of the ε-term, reused
    for i in range(3):
        qi = Q[:, i]
        q0, q1 = q0s[i], q1s[i]
        argq = q0 * q0 + q1 * q1
        errq = 2 * (np.abs(q0) * EQ0 + np.abs(q1) * EQ1) + EQ0 ** 2 + EQ1 ** 2 + SLOP
        denom1_hi = (np.sqrt(argq + errq) * (1 + REL_SQRT)
                     + US2 * eps + 3 * KAPPA + SLOP)
        dv = DV[qi]                        # (n,90,3) = V[Q_i] - V[k]
        dv0, dv1, dv2 = dv[:, :, 0], dv[:, :, 1], dv[:, :, 2]
        d0 = m00[:, None] * dv0 + m01[:, None] * dv1
        d1 = m10[:, None] * dv0 + m11[:, None] * dv1 + m12[:, None] * dv2
        adv01 = np.abs(dv0) + np.abs(dv1)
        ED0 = adv01 * t[:, None] + R13
        ED1 = (2 * adv01 + np.abs(dv2)) * t[:, None] + R13
        n_dv_hi = NDV[qi] * (1 + REL_SQRT) + SLOP
        dot = q0[:, None] * d0 + q1[:, None] * d1
        err_dot = (np.abs(q0)[:, None] * ED0 + np.abs(d0) * EQ0[:, None]
                   + np.abs(q1)[:, None] * ED1 + np.abs(d1) * EQ1[:, None]
                   + EQ0[:, None] * ED0 + EQ1[:, None] * ED1)
        numer_lo = (dot - err_dot - 10 * KAPPA
                    - two_eps_f[:, None] * (n_dv_hi + 2 * KAPPA) - SLOP)
        argd = d0 * d0 + d1 * d1
        errd = 2 * (np.abs(d0) * ED0 + np.abs(d1) * ED1) + ED0 ** 2 + ED1 ** 2 + SLOP
        denom2_hi = (np.sqrt(argd + errd) * (1 + REL_SQRT)
                     + (2 * US2 * eps)[:, None] + 6 * KAPPA + SLOP)
        sl = numer_lo / (denom1_hi[:, None] * denom2_hi) - bound_hi[:, None]
        sl[np.arange(n), qi] = np.inf      # k ≠ Q_i
        b_slack = np.minimum(b_slack, sl.min(axis=1))
    out["B_eps"] = b_slack
    return out


def _accept(slacks, margin):
    ok = slacks["symmetry_exists"] > 0
    for key in ["center_in_fourQ", "epsilon_pos", "rpos",
                "X1", "X2", "P_span", "Q_span", "r_valid", "B_eps"]:
        ok = ok & (slacks[key] > margin)
    return ok


def check_local_arrays(centers, eps, P, Q, r, sigma, margin=1e-9, chunk=20000):
    """Vectorized check. centers (n,5) float [θ₁,φ₁,θ₂,φ₂,α]; eps (n,);
    P, Q (n,3) int vertex indices 0..89; r (n,) float (= r'/1000);
    sigma (n,) int in {0,1}.  Returns (accept bool (n,), slacks dict)."""
    centers = np.ascontiguousarray(centers, dtype=np.float64)
    eps = np.asarray(eps, dtype=np.float64)
    P = np.asarray(P, dtype=np.int64)
    Q = np.asarray(Q, dtype=np.int64)
    r = np.asarray(r, dtype=np.float64)
    sigma = np.asarray(sigma, dtype=np.int64)
    n = centers.shape[0]
    keys = CONJUNCTS + ["delta_hi"]
    slacks = {k: np.empty(n) for k in keys}
    for lo in range(0, n, chunk):
        hi = min(lo + chunk, n)
        part = _check_chunk(centers[lo:hi], eps[lo:hi], P[lo:hi], Q[lo:hi],
                            r[lo:hi], sigma[lo:hi])
        for k in keys:
            slacks[k][lo:hi] = part[k]
    return _accept(slacks, margin), slacks


def check_local(center5, eps, P_idx3, Q_idx3, r, sigma_q, margin=1e-9):
    """Single-candidate check.

    center5: 5 floats (θ₁, φ₁, θ₂, φ₂, α) — CSV column order T1,V1,T2,V2,A.
    eps: box half-width (sup metric).  P_idx3/Q_idx3: 3 vertex indices 0..89.
    r: the certificate radius (r'/1000).  sigma_q: 0 or 1.

    Returns (accept, diagnostics) with the worst conservative slack per
    conjunct.  Every slack is a LOWER bound on the exact Lean slack;
    delta_consistency is the width of the float model's band around Lean's
    computed Row.δ (informational, already folded into B_eps via δ_hi)."""
    acc, sl = check_local_arrays(
        np.asarray(center5, dtype=np.float64).reshape(1, 5),
        [eps], np.asarray(P_idx3).reshape(1, 3), np.asarray(Q_idx3).reshape(1, 3),
        [r], [sigma_q], margin=margin)
    diag = {k: float(v[0]) for k, v in sl.items()}
    return bool(acc[0]), diag


def check_local_rows(df_rows, margin=1e-9, chunk=20000):
    """Check a DataFrame of solution-tree rows (CSV schema of
    solution_tree_v5.csv; nodeType==2 rows).  Returns (accept, slacks)."""
    df = df_rows
    params = ["T1", "V1", "T2", "V2", "A"]
    bmin = np.stack([df[p + "_min"].to_numpy(np.int64) for p in params], axis=1)
    bmax = np.stack([df[p + "_max"].to_numpy(np.int64) for p in params], axis=1)
    centers = (bmin + bmax) / (2 * DENOM)
    eps = ((bmax - bmin).max(axis=1) / 2) / DENOM
    P = np.stack([df[c].to_numpy(np.int64) for c in
                  ["P1_index", "P2_index", "P3_index"]], axis=1)
    Q = np.stack([df[c].to_numpy(np.int64) for c in
                  ["Q1_index", "Q2_index", "Q3_index"]], axis=1)
    r = df["r"].to_numpy(np.int64) / 1000.0
    sigma = df["sigma_Q"].to_numpy(np.int64)
    return check_local_arrays(centers, eps, P, Q, r, sigma,
                              margin=margin, chunk=chunk)


# ============================ validation protocol ============================

def _percentiles(a):
    return {"min": float(np.min(a)), "p1": float(np.percentile(a, 1)),
            "p50": float(np.percentile(a, 50)), "max": float(np.max(a))}


def main():
    import argparse
    import time

    import pandas as pd

    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", default=os.path.join(_HERE, "..", "data", "solution_tree_v5.csv"))
    ap.add_argument("--out", default=os.path.join(_HERE, "local_check_validation.json"))
    args = ap.parse_args()

    int_cols = ["nrChildren", "IDfirstChild", "split", "P1_index", "P2_index",
                "P3_index", "Q1_index", "Q2_index", "Q3_index", "r", "sigma_Q",
                "wx_nominator", "wy_nominator", "w_denominator", "S_index"]
    print("loading", args.csv)
    df = pd.read_csv(args.csv, dtype={c: "Int64" for c in int_cols})
    loc = df[df.nodeType == 2].reset_index(drop=True)
    nloc = len(loc)
    print(f"{nloc} local rows")

    t0 = time.time()
    acc0, sl = check_local_rows(loc, margin=0.0)
    wall = time.time() - t0
    print(f"full run: {wall:.1f}s;  margin=0 acceptance {acc0.mean()*100:.4f}%")

    summary = {"n_local_rows": int(nloc), "wall_seconds": wall,
               "margin0_acceptance": float(acc0.mean()),
               "margin0_rejected_ids": loc.ID[~acc0].tolist()[:50]}

    dist = {}
    for k in CONJUNCTS:
        if k == "symmetry_exists":
            dist[k] = {"found_fraction": float((sl[k] > 0).mean())}
        else:
            dist[k] = _percentiles(sl[k])
        print(f"  {k:18s} {dist[k]}")
    summary["slack_distributions"] = dist

    acc9 = _accept(sl, 1e-9)
    summary["margin1e9_acceptance"] = float(acc9.mean())
    near = {}
    for k in ["X1", "X2", "P_span", "Q_span", "r_valid", "B_eps"]:
        near[k] = int(((sl[k] <= 1e-9) & (sl[k] > 0)).sum())
    summary["margin1e9_rows_within_1e9_by_conjunct"] = near
    print(f"margin=1e-9 acceptance {acc9.mean()*100:.4f}%  near-boundary: {near}")

    # -------- negative controls (1000 rows each) --------
    rng = np.random.default_rng(0)
    idx = rng.choice(nloc, size=min(1000, nloc), replace=False)
    sub = loc.iloc[idx].reset_index(drop=True)

    # (a) r *= 1.01
    params = ["T1", "V1", "T2", "V2", "A"]
    bmin = np.stack([sub[p + "_min"].to_numpy(np.int64) for p in params], axis=1)
    bmax = np.stack([sub[p + "_max"].to_numpy(np.int64) for p in params], axis=1)
    centers = (bmin + bmax) / (2 * DENOM)
    eps = ((bmax - bmin).max(axis=1) / 2) / DENOM
    P = np.stack([sub[c].to_numpy(np.int64) for c in
                  ["P1_index", "P2_index", "P3_index"]], axis=1)
    Q = np.stack([sub[c].to_numpy(np.int64) for c in
                  ["Q1_index", "Q2_index", "Q3_index"]], axis=1)
    r = sub["r"].to_numpy(np.int64) / 1000.0
    sigma = sub["sigma_Q"].to_numpy(np.int64)

    # NOTE (finding): SY25's data has a *minimum* r_valid headroom of ~1.02%
    # of r (slack/r: min .01024, p50 .022), so the canonical 1% bump lands
    # just inside the margin on every row; 2%/5% bumps show the rejection.
    # A larger r only helps B_eps (bound = (δ+2.24ε)/r shrinks), so r_valid
    # is the only conjunct that can fail here.
    for pct, fac in [("1pct", 1.01), ("2pct", 1.02), ("5pct", 1.05)]:
        acc_r, sl_r = check_local_arrays(centers, eps, P, Q, r * fac, sigma, margin=0.0)
        rej_by = {k: int(((sl_r[k] <= 0.0)).sum()) for k in ["r_valid", "B_eps"]}
        summary[f"negative_control_r_up_{pct}"] = {
            "n": int(len(idx)), "rejection_rate": float(1 - acc_r.mean()),
            "failed_r_valid": rej_by["r_valid"], "failed_B_eps": rej_by["B_eps"]}
        print(f"neg control (r*{fac}):", summary[f"negative_control_r_up_{pct}"])

    # (b) swap one Q index randomly
    Q2 = Q.copy()
    pos = rng.integers(0, 3, size=len(idx))
    newq = rng.integers(0, 90, size=len(idx))
    cur = Q2[np.arange(len(idx)), pos]
    newq = np.where(newq == cur, (newq + 1) % 90, newq)
    Q2[np.arange(len(idx)), pos] = newq
    acc_q, sl_q = check_local_arrays(centers, eps, P, Q2, r, sigma, margin=0.0)
    fails = {k: int((sl_q[k] <= 0.0).sum()) for k in
             ["X2", "Q_span", "r_valid", "B_eps"]}
    fails["symmetry_exists"] = int((sl_q["symmetry_exists"] <= 0).sum())
    summary["negative_control_swap_Q"] = {
        "n": int(len(idx)), "rejection_rate": float(1 - acc_q.mean()),
        "failed_by_conjunct": fails}
    print("neg control (swap Q):", summary["negative_control_swap_Q"])

    with open(args.out, "w") as f:
        json.dump(summary, f, indent=2)
    print("wrote", args.out)


if __name__ == "__main__":
    main()
