//! Gap certificates whose separating direction is affine in the box coordinates:
//! `w(t) = w0 + Σ_i t_i W_i` (normalized `t ∈ [-1,1]^5`). Each constraint stays a
//! bilinear form `X(u,v) ⊗ Y(y)`, now with per-variable degree ≤ 3.

use crate::geom::*;
use crate::poly::*;
use crate::{BoxPolys, Bx, Ctx};

pub const DA: usize = 3;

/// Re-embed `p` (degree cap `p.d`) with a larger degree cap `d`.
pub fn lift(p: &P, d: usize) -> P {
    let mut r = P::zero(p.nv, d);
    for (i, &a) in p.c.iter().enumerate() {
        if a == 0.0 {
            continue;
        }
        let e = p.exps(i);
        let mut idx = 0;
        let mut m = 1;
        for k in 0..p.nv {
            idx += e[k] * m;
            m *= d + 1;
        }
        r.c[idx] = a;
    }
    r
}

/// `p · t_i` in the normalized variable `i`.
pub fn mul_var(p: &P, i: usize) -> P {
    let mut r = P::zero(p.nv, p.d);
    for (idx, &a) in p.c.iter().enumerate() {
        if a == 0.0 {
            continue;
        }
        let e = p.exps(idx);
        assert!(e[i] < p.d, "degree overflow");
        r.c[idx + (p.d + 1).pow(i as u32)] += a;
    }
    r
}

/// An affine direction: `w0` and the coefficients `wt[i]` of `t_i` (i = 0..5; 0,1 are X vars).
#[derive(Clone, Copy, Debug)]
pub struct AffW {
    pub w0: [f64; 2],
    pub wt: [[f64; 2]; 5],
}

/// Pointwise optimal separating angle for inner vertex `s` at normalized point `t`
/// (direction from the outer hull, without the paired vertex, to the inner vertex).
pub fn opt_theta(ctx: &Ctx, b: &Bx, s: usize, t: [f64; 5]) -> Option<f64> {
    let u = b.c(0) + b.h(0) * t[0];
    let v = b.c(1) + b.h(1) * t[1];
    let r = b.r_at([t[2], t[3], t[4]]);
    let ro = outer(u, v);
    let ri = mm(&ro, &mm(&chart(b.chart), &cay(r[0], r[1], r[2])));
    let paired = if b.blowup() { ctx.pair(b.chart, s) } else { None };
    let pts: Vec<[f64; 2]> = ctx
        .verts
        .iter()
        .enumerate()
        .filter(|(j, _)| Some(*j) != paired)
        .map(|(_, v)| {
            let p = mv(&ro, v);
            [p[0], p[1]]
        })
        .collect();
    let q = {
        let p = mv(&ri, &ctx.verts[s]);
        [p[0], p[1]]
    };
    let h = hull(&pts);
    // nearest point of the hull boundary to q
    let mut best = (f64::INFINITY, [0.0; 2]);
    for e in 0..h.len() {
        let a = pts[h[e]];
        let c = pts[h[(e + 1) % h.len()]];
        let d = [c[0] - a[0], c[1] - a[1]];
        let l2 = d[0] * d[0] + d[1] * d[1];
        let tt = (((q[0] - a[0]) * d[0] + (q[1] - a[1]) * d[1]) / l2).clamp(0.0, 1.0);
        let n = [a[0] + tt * d[0], a[1] + tt * d[1]];
        let dist = (q[0] - n[0]).powi(2) + (q[1] - n[1]).powi(2);
        if dist < best.0 {
            best = (dist, n);
        }
    }
    let dir = [q[0] - best.1[0], q[1] - best.1[1]];
    if dir[0] == 0.0 && dir[1] == 0.0 {
        return None;
    }
    Some(dir[1].atan2(dir[0]))
}

/// Affine direction around angle `th0`, slope from finite differences of the optimal angle.
pub fn affine_dir(ctx: &Ctx, b: &Bx, s: usize, th0: f64, delta: f64, gain: f64) -> AffW {
    let mut g = [0.0; 5];
    for i in 0..5 {
        let mut tp = [0.0; 5];
        let mut tm = [0.0; 5];
        tp[i] = delta;
        tm[i] = -delta;
        if let (Some(a), Some(c)) = (opt_theta(ctx, b, s, tp), opt_theta(ctx, b, s, tm)) {
            let mut d = a - c;
            while d > std::f64::consts::PI {
                d -= 2.0 * std::f64::consts::PI;
            }
            while d < -std::f64::consts::PI {
                d += 2.0 * std::f64::consts::PI;
            }
            g[i] = gain * d / (2.0 * delta);
        }
    }
    let (c, sn) = (th0.cos(), th0.sin());
    let q = |x: f64| (x * 1024.0).round();
    AffW { w0: [q(c), q(sn)], wt: g.map(|gi| [q(-sn * gi), q(c * gi)]) }
}

/// `Σ_k α_k ⊗ y_k` with `α_k = Σ_l w_l(t) N_o[l][k]`, where the `y_k` are Y-polys (cap DA).
fn alpha_dot(no: &[[P; 3]; 3], aw: &AffW, ys: &[P; 3]) -> B {
    let nx = (DA + 1).pow(2);
    let ny = (DA + 1).pow(3);
    let mut f = B::zero(nx, ny);
    for k in 0..3 {
        // X part: (w0_l + Σ_{i<2} wt[i]_l t_i) N_o[l][k]
        let mut ax = P::zero(2, DA);
        for l in 0..2 {
            let n = lift(&no[l][k], DA);
            ax = ax.add(&n.scale(aw.w0[l]));
            for i in 0..2 {
                if aw.wt[i][l] != 0.0 {
                    ax = ax.add(&mul_var(&n, i).scale(aw.wt[i][l]));
                }
            }
        }
        f.add_outer(&ax, &ys[k], 1.0);
        // Y part: N_o[l][k] ⊗ (Σ_{i≥2} wt[i]_l y_i) y_k
        for l in 0..2 {
            let n = lift(&no[l][k], DA);
            let mut yy = P::zero(3, DA);
            for i in 2..5 {
                if aw.wt[i][l] != 0.0 {
                    yy = yy.add(&mul_var(&ys[k], i - 2).scale(aw.wt[i][l]));
                }
            }
            f.add_outer(&n, &yy, 1.0);
        }
    }
    f
}

/// Does the affine-direction gap certificate for inner vertex `s` pass on the box?
pub fn check_affine(ctx: &Ctx, cl: &Classes, b: &Bx, bp: &BoxPolys, s: usize, aw: &AffW) -> bool {
    let sv = ctx.verts[s];
    let tol = 1e-11 * (aw.w0[0].abs() + aw.w0[1].abs());
    let beta: [P; 3] = [0, 1, 2].map(|k| {
        let mut y = P::zero(3, DY_);
        for m in 0..3 {
            y = y.add(&bp.cnr[k][m].scale(sv[m]));
        }
        lift(&y, DA)
    });
    let dr = lift(&bp.dr, DA);
    let paired = if b.blowup() { ctx.pair(b.chart, s) } else { None };
    if paired.is_some() {
        let bm = chart(b.chart);
        let cy = bp.cy.as_ref().unwrap();
        let rho = bp.rho.as_ref().unwrap();
        let sp = [P::constant(3, DY_, sv[0]), P::constant(3, DY_, sv[1]), P::constant(3, DY_, sv[2])];
        let cross = |a: &[P; 3], c: &[P; 3]| -> [P; 3] {
            [
                a[1].mul(&c[2]).sub(&a[2].mul(&c[1])),
                a[2].mul(&c[0]).sub(&a[0].mul(&c[2])),
                a[0].mul(&c[1]).sub(&a[1].mul(&c[0])),
            ]
        };
        let cs = cross(cy, &sp);
        let ccs = cross(cy, &cs);
        let inner: Vec<P> = (0..3).map(|k| cs[k].add(&ccs[k].mul(rho))).collect();
        let ys: [P; 3] = [0, 1, 2].map(|k| {
            let mut y = P::zero(3, DY_);
            for m in 0..3 {
                if bm[k][m] != 0.0 {
                    y = y.add(&inner[m].scale(bm[k][m]));
                }
            }
            lift(&y, DA)
        });
        if !pos(cl, &alpha_dot(&bp.no, aw, &ys), tol) {
            return false;
        }
    }
    for j in 0..ctx.verts.len() {
        if paired == Some(j) {
            continue;
        }
        let t = ctx.verts[j];
        let ys: [P; 3] = [0, 1, 2].map(|k| beta[k].sub(&dr.scale(t[k])));
        if !pos(cl, &alpha_dot(&bp.no, aw, &ys), tol) {
            return false;
        }
    }
    true
}

fn pos(cl: &Classes, f: &B, tol: f64) -> bool {
    cl.lower(f) > tol || (std::env::var("BERN").is_ok() && crate::bern_lower_nd(&f.c, &[DA; 5]) > tol)
}

const DY_: usize = 2;
