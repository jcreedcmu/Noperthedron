mod affine;
mod geom;
mod poly;

use geom::*;
use poly::*;
use std::f64::consts::PI;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

const DX: usize = 2; // per-variable degree cap for (u,v) in gap polys
const DXH: usize = 4; // ... in the half-turn domain polys
const DY: usize = 2;

#[derive(Clone, Copy, Debug)]
pub struct Bx {
    pub chart: usize,
    /// blow-up face (0..6) when `chart == 0`
    pub face: usize,
    pub lo: [f64; 5],
    pub hi: [f64; 5],
}

impl Bx {
    fn c(&self, i: usize) -> f64 {
        0.5 * (self.lo[i] + self.hi[i])
    }
    fn h(&self, i: usize) -> f64 {
        0.5 * (self.hi[i] - self.lo[i])
    }
    fn blowup(&self) -> bool {
        self.chart == 0 || self.chart == 4
    }
    /// Cayley vector at normalized coordinates (y in [-1,1]^3)
    fn r_at(&self, y: [f64; 3]) -> V3 {
        let g = |i: usize| self.c(2 + i) + self.h(2 + i) * y[i];
        if self.blowup() {
            let c = self.cvec([g(0), g(1)]);
            let rho = g(2);
            [rho * c[0], rho * c[1], rho * c[2]]
        } else {
            [g(0), g(1), g(2)]
        }
    }
    fn cvec(&self, s: [f64; 2]) -> V3 {
        let a = self.face / 2;
        let sg = if self.face % 2 == 0 { 1.0 } else { -1.0 };
        let mut c = [0.0; 3];
        c[a] = sg;
        c[(a + 1) % 3] = s[0];
        c[(a + 2) % 3] = s[1];
        c
    }
    fn split(&self, i: usize) -> (Bx, Bx) {
        let m = self.c(i);
        let mut a = *self;
        let mut b = *self;
        a.hi[i] = m;
        b.lo[i] = m;
        (a, b)
    }
}

struct Ctx {
    verts: Vec<V3>,
    group: Vec<M3>,
    cx: Classes,
    cxh: Classes,
    m_wedge: f64,
    pair4: Vec<Option<usize>>,
    delta: f64,
}

impl Ctx {
    fn pair(&self, chart: usize, s: usize) -> Option<usize> {
        match chart {
            0 => Some(s),
            4 => self.pair4[s],
            _ => None,
        }
    }
}

/// Polynomials for one box.
struct BoxPolys {
    no: [[P; 3]; 3],  // outer numerator, X polys deg 2
    noh: [[P; 3]; 3], // same, cap 4
    do2h: P,          // D_o^2, cap 4
    cnr: [[P; 3]; 3], // chart * N_r, Y polys
    dr: P,
    cy: Option<[P; 3]>, // blow-up direction c
    rho: Option<P>,
}

fn cay_num_p(x: &P, y: &P, z: &P) -> [[P; 3]; 3] {
    let xx = x.mul(x);
    let yy = y.mul(y);
    let zz = z.mul(z);
    let xy = x.mul(y);
    let xz = x.mul(z);
    let yz = y.mul(z);
    [
        [xx.sub(&yy).sub(&zz).add_const(1.0), xy.sub(z).scale(2.0), xz.add(y).scale(2.0)],
        [xy.add(z).scale(2.0), yy.sub(&xx).sub(&zz).add_const(1.0), yz.sub(x).scale(2.0)],
        [xz.sub(y).scale(2.0), yz.add(x).scale(2.0), zz.sub(&xx).sub(&yy).add_const(1.0)],
    ]
}

fn box_polys(b: &Bx) -> BoxPolys {
    let mk_x = |d: usize| {
        let u = P::var(2, d, 0, b.c(0), b.h(0));
        let v = P::var(2, d, 1, b.c(1), b.h(1));
        let z = P::zero(2, d);
        let no = cay_num_p(&v, &u.scale(-1.0), &z);
        let do_ = u.mul(&u).add(&v.mul(&v)).add_const(1.0);
        (no, do_)
    };
    let (no, _) = mk_x(DX);
    let (noh, doh) = mk_x(DXH);
    let do2h = doh.mul(&doh);
    let (r, cy, rho) = if b.blowup() {
        let s0 = P::var(3, DY, 0, b.c(2), b.h(2));
        let s1 = P::var(3, DY, 1, b.c(3), b.h(3));
        let rho = P::var(3, DY, 2, b.c(4), b.h(4));
        let a = b.face / 2;
        let sg = if b.face % 2 == 0 { 1.0 } else { -1.0 };
        let mut c = [P::zero(3, DY), P::zero(3, DY), P::zero(3, DY)];
        c[a] = P::constant(3, DY, sg);
        c[(a + 1) % 3] = s0;
        c[(a + 2) % 3] = s1;
        let r = [c[0].mul(&rho), c[1].mul(&rho), c[2].mul(&rho)];
        (r, Some(c), Some(rho))
    } else {
        let r = [
            P::var(3, DY, 0, b.c(2), b.h(2)),
            P::var(3, DY, 1, b.c(3), b.h(3)),
            P::var(3, DY, 2, b.c(4), b.h(4)),
        ];
        (r, None, None)
    };
    let nr = cay_num_p(&r[0], &r[1], &r[2]);
    let dr = r[0].mul(&r[0]).add(&r[1].mul(&r[1])).add(&r[2].mul(&r[2])).add_const(1.0);
    let ch = chart(b.chart);
    let cnr = [0, 1, 2].map(|i| {
        [0, 1, 2].map(|j| {
            let mut s = P::zero(3, DY);
            for k in 0..3 {
                if ch[i][k] != 0.0 {
                    s = s.add(&nr[k][j].scale(ch[i][k]));
                }
            }
            s
        })
    });
    BoxPolys { no, noh, do2h, cnr, dr, cy, rho }
}

/// tr(Bᵀ X) for a constant matrix B and polynomial matrix X
fn tr_bt(bm: &M3, x: &[[P; 3]; 3]) -> P {
    let mut s = P::zero(x[0][0].nv, x[0][0].d);
    for i in 0..3 {
        for j in 0..3 {
            if bm[i][j] != 0.0 {
                s = s.add(&x[i][j].scale(bm[i][j]));
            }
        }
    }
    s
}

/// Does some reduction inequality fail on the whole box?
fn domain_excluded(ctx: &Ctx, b: &Bx, bp: &BoxPolys) -> Option<u32> {
    // disk u^2+v^2 <= 1 (u, v >= 0 on all boxes)
    if b.lo[0].max(0.0).powi(2) + b.lo[1].max(0.0).powi(2) > 1.0 {
        return Some(0);
    }
    if b.lo[1] > ctx.m_wedge * b.hi[0] {
        return Some(1);
    }
    // chart scores s_k = tr(B_kᵀ Q) (numerators over D_r)
    let s: Vec<P> = (0..5).map(|k| tr_bt(&chart(k), &bp.cnr)).collect();
    // chart condition: own score is maximal
    for k in 0..5 {
        if k != b.chart && plow(&s[k].sub(&s[b.chart])) > 1e-9 {
            return Some(2 + k as u32);
        }
    }
    // orbit: F(X) = max(s0(X), s4(X) - δ) must not exceed F(Q)
    let base = [chart(0), chart(4)];
    let delta = ctx.delta;
    let s4d = s[4].sub(&bp.dr.scale(delta));
    // ε = 0: X = Q g, s_a(X) = tr(B_aᵀ Q g) = tr((B_a gᵀ)ᵀ Q)
    for k in 1..15 {
        let g = &ctx.group[k];
        for a in 0..2 {
            let bg = mm(&base[a], &transpose(g));
            let mut sx = tr_bt(&bg, &bp.cnr);
            if a == 1 {
                sx = sx.sub(&bp.dr.scale(delta));
            }
            if plow(&sx.sub(&s[0])) > 1e-9 && plow(&sx.sub(&s4d)) > 1e-9 {
                return Some(7 + (k as u32) * 2 + a as u32);
            }
        }
    }
    // ε = 1: X = H Q g, H = N_oᵀ Z N_o / D_o²; s_a(X) = tr(B_aᵀ H Q g) = Σ (H Q)[i][j] (B_a gᵀ)[i][j]
    let z = [-1.0, -1.0, 1.0];
    let mut hm: Vec<Vec<P>> = vec![vec![P::zero(2, DXH); 3]; 3];
    for a in 0..3 {
        for c in 0..3 {
            let mut t = P::zero(2, DXH);
            for k in 0..3 {
                t = t.add(&bp.noh[k][a].mul(&bp.noh[k][c]).scale(z[k]));
            }
            hm[a][c] = t;
        }
    }
    let nx = hm[0][0].c.len();
    let ny = s[0].c.len();
    let mut q0 = B::zero(nx, ny);
    q0.add_outer(&bp.do2h, &s[0], 1.0);
    let mut q4 = B::zero(nx, ny);
    q4.add_outer(&bp.do2h, &s4d, 1.0);
    let mut dsh = B::zero(nx, ny);
    dsh.add_outer(&bp.do2h, &bp.dr, delta);
    for k in 0..15 {
        let g = &ctx.group[k];
        for a in 0..2 {
            let bg = mm(&base[a], &transpose(g));
            // Σ_{i,j} bg[i][j] Σ_m H[i][m] Q[m][j]
            let mut bb = B::zero(nx, ny);
            for i in 0..3 {
                for m in 0..3 {
                    let mut y = P::zero(3, DY);
                    for j in 0..3 {
                        if bg[i][j] != 0.0 {
                            y = y.add(&bp.cnr[m][j].scale(bg[i][j]));
                        }
                    }
                    bb.add_outer(&hm[i][m], &y, 1.0);
                }
            }
            if a == 1 {
                for (x, y) in bb.c.iter_mut().zip(dsh.c.iter()) {
                    *x -= y;
                }
            }
            let mut d0 = bb.clone();
            for (x, y) in d0.c.iter_mut().zip(q0.c.iter()) {
                *x -= y;
            }
            if blow(&ctx.cxh, &d0, DXH, DY) > 1e-9 {
                let mut d4 = bb.clone();
                for (x, y) in d4.c.iter_mut().zip(q4.c.iter()) {
                    *x -= y;
                }
                if blow(&ctx.cxh, &d4, DXH, DY) > 1e-9 {
                    return Some(7 + (15 + k as u32) * 2 + a as u32);
                }
            }
        }
    }
    None
}

fn proj_pts(rot: &M3, verts: &[V3]) -> Vec<[f64; 2]> {
    verts
        .iter()
        .map(|v| {
            let p = mv(rot, v);
            [p[0], p[1]]
        })
        .collect()
}

#[derive(Clone, Copy, Debug)]
pub struct Cand {
    pub s: usize,
    pub w: [f64; 2],
    pub score: f64,
}

fn candidates(ctx: &Ctx, b: &Bx) -> Vec<Cand> { candidates_n(ctx, b, 4) }

fn candidates_n(ctx: &Ctx, b: &Bx, nkeep: usize) -> Vec<Cand> {
    let u = b.c(0);
    let v = b.c(1);
    let ro = outer(u, v);
    let r = b.r_at([0.0; 3]);
    let ri = mm(&ro, &mm(&chart(b.chart), &cay(r[0], r[1], r[2])));
    let p = proj_pts(&ro, &ctx.verts);
    let q = proj_pts(&ri, &ctx.verts);
    let rho_c = if b.blowup() { b.c(4) } else { 1.0 };
    const ND: usize = 256;
    let mut best: Vec<Cand> = vec![];
    let n = ctx.verts.len();
    let mut per_s: Vec<Cand> = (0..n).map(|s| Cand { s, w: [1.0, 0.0], score: f64::NEG_INFINITY }).collect();
    for d in 0..ND {
        let th = 2.0 * PI * d as f64 / ND as f64;
        let w = [th.cos(), th.sin()];
        let mut h1 = f64::NEG_INFINITY;
        let mut h2 = f64::NEG_INFINITY;
        let mut a1 = 0;
        for j in 0..n {
            let x = w[0] * p[j][0] + w[1] * p[j][1];
            if x > h1 {
                h2 = h1;
                h1 = x;
                a1 = j;
            } else if x > h2 {
                h2 = x;
            }
        }
        for s in 0..n {
            let qs = w[0] * q[s][0] + w[1] * q[s][1];
            let sc = if let (true, Some(pj)) = (b.blowup(), ctx.pair(b.chart, s)) {
                let other = qs - if a1 == pj { h2 } else { h1 };
                let me = (qs - (w[0] * p[pj][0] + w[1] * p[pj][1])) / rho_c;
                other.min(me)
            } else {
                qs - h1
            };
            if sc > per_s[s].score {
                per_s[s] = Cand { s, w, score: sc };
            }
        }
    }
    for c in per_s.iter_mut() {
        c.w = [(c.w[0] * 1024.0).round(), (c.w[1] * 1024.0).round()];
    }
    per_s.sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap());
    for c in per_s.iter().take(nkeep) {
        if c.score > 0.0 {
            best.push(*c);
        }
    }
    best
}

/// Many candidates: the best `ns` vertices, each with its best direction and rotated variants.
fn candidates_wide(ctx: &Ctx, b: &Bx, ns: usize, offs: &[f64]) -> Vec<Cand> {
    let base = candidates_n(ctx, b, ns);
    let mut out = vec![];
    for c in base {
        let th = c.w[1].atan2(c.w[0]);
        for &o in offs {
            let t = th + o;
            out.push(Cand { s: c.s, w: [(t.cos() * 1024.0).round(), (t.sin() * 1024.0).round()], score: c.score });
        }
    }
    out
}

fn slack_vars(a: &B) -> [f64; 5] {
    let mut s = [0.0; 5];
    for i in 0..a.nx {
        let ex = [i % 3, i / 3];
        for j in 0..a.ny {
            let ey = [j % 3, (j / 3) % 3, j / 9];
            let v = a.c[i * a.ny + j];
            let e = [ex[0], ex[1], ey[0], ey[1], ey[2]];
            if e.iter().all(|x| *x == 0) {
                continue;
            }
            let alleven = e.iter().all(|x| x % 2 == 0);
            let contrib = if alleven { (-v).max(0.0) } else { v.abs() };
            for k in 0..5 {
                if e[k] > 0 {
                    s[k] += contrib;
                }
            }
        }
    }
    s
}

/// Constant term, five linear coefficients and nonlinear abs-sum of a bilinear form
/// (X slots: (u,v) with per-variable degree ≤ 2; Y slots: three variables, degree ≤ 2).
fn form_stats(f: &B) -> (f64, [f64; 5], f64) {
    let mut c0 = 0.0;
    let mut lin = [0.0; 5];
    let mut nl = 0.0;
    for i in 0..f.nx {
        let ex = [i % 3, i / 3];
        for j in 0..f.ny {
            let ey = [j % 3, (j / 3) % 3, j / 9];
            let v = f.c[i * f.ny + j];
            let e = [ex[0], ex[1], ey[0], ey[1], ey[2]];
            let deg: usize = e.iter().sum();
            if deg == 0 { c0 += v; }
            else if deg == 1 { let k = e.iter().position(|x| *x == 1).unwrap(); lin[k] += v; }
            else { nl += v.abs(); }
        }
    }
    (c0, lin, nl)
}

/// The kernel checker's tests: quick (constant + abs-sum) or linear-exact, no full bound.
fn tiers_ok(ctx: &Ctx, b: &Bx, bp: &BoxPolys, c: &Cand) -> bool {
    let w = c.w;
    let alpha: Vec<P> = (0..3).map(|k| bp.no[0][k].scale(w[0]).add(&bp.no[1][k].scale(w[1]))).collect();
    let sv = ctx.verts[c.s];
    let nx = alpha[0].c.len();
    let ny = bp.dr.c.len();
    let mut a = B::zero(nx, ny);
    for k in 0..3 {
        let mut beta = P::zero(3, DY);
        for m in 0..3 { beta = beta.add(&bp.cnr[k][m].scale(sv[m])); }
        a.add_outer(&alpha[k], &beta, 1.0);
    }
    let (a0, al, an) = form_stats(&a);
    let as_ = al.iter().map(|x| x.abs()).sum::<f64>() + an;
    let mut es = vec![];
    for k in 0..3 {
        let mut e = B::zero(nx, ny);
        e.add_outer(&alpha[k], &bp.dr, 1.0);
        let (e0, el, en) = form_stats(&e);
        let esl = el.iter().map(|x| x.abs()).sum::<f64>() + en;
        es.push((e0, el, en, esl));
    }
    let tol = 1e-11 * (w[0].abs() + w[1].abs());
    let paired = if b.blowup() { ctx.pair(b.chart, c.s) } else { None };
    for j in 0..ctx.verts.len() {
        if paired == Some(j) { continue; }
        let t = ctx.verts[j];
        let c0 = a0 - (0..3).map(|k| t[k] * es[k].0).sum::<f64>();
        let quick = c0 - as_ - (0..3).map(|k| t[k].abs() * es[k].3).sum::<f64>();
        if quick > tol { continue; }
        let mut lsum = 0.0;
        for i in 0..5 { lsum += (al[i] - (0..3).map(|k| t[k] * es[k].1[i]).sum::<f64>()).abs(); }
        let nl = an + (0..3).map(|k| t[k].abs() * es[k].2).sum::<f64>();
        if c0 - lsum - nl > tol { continue; }
        return false;
    }
    true
}

/// Estimated kernel cost (ms) of a passing candidate under the kernel checker's tiers.
fn kernel_cost(ctx: &Ctx, b: &Bx, bp: &BoxPolys, c: &Cand) -> f64 {
    let w = c.w;
    let alpha: Vec<P> = (0..3).map(|k| bp.no[0][k].scale(w[0]).add(&bp.no[1][k].scale(w[1]))).collect();
    let sv = ctx.verts[c.s];
    let nx = alpha[0].c.len();
    let ny = bp.dr.c.len();
    let mut a = B::zero(nx, ny);
    for k in 0..3 {
        let mut beta = P::zero(3, DY);
        for m in 0..3 { beta = beta.add(&bp.cnr[k][m].scale(sv[m])); }
        a.add_outer(&alpha[k], &beta, 1.0);
    }
    let (a0, al, an) = form_stats(&a);
    let as_ = al.iter().map(|x| x.abs()).sum::<f64>() + an;
    let dabs: f64 = bp.dr.c.iter().map(|x| x.abs()).sum();
    let mut e0 = [0.0; 3];
    let mut es = [0.0; 3];
    for k in 0..3 {
        let aabs: f64 = alpha[k].c.iter().map(|x| x.abs()).sum();
        e0[k] = alpha[k].c[0] * bp.dr.c[0];
        es[k] = aabs * dabs - e0[k].abs();
    }
    let tol = 1e-11 * (w[0].abs() + w[1].abs());
    let paired = if b.blowup() { ctx.pair(b.chart, c.s) } else { None };
    let mut cost = 30.0; // setup + A table + packed quick test
    for j in 0..ctx.verts.len() {
        let t = ctx.verts[j];
        let c0 = a0 - (0..3).map(|k| t[k] * e0[k]).sum::<f64>();
        let quick = c0 - as_ - (0..3).map(|k| t[k].abs() * es[k]).sum::<f64>();
        if quick > tol { continue; }
        if paired == Some(j) { cost += 20.0; continue; } // L tests
        // linear tier with exact x_T
        let mut x = P::zero(2, DX);
        for k in 0..3 { x = x.add(&alpha[k].scale(t[k])); }
        let d = &bp.dr.c;
        let xl = [x.c[1], x.c[3]];
        let el = [xl[0] * d[0], xl[1] * d[0], x.c[0] * d[1], x.c[0] * d[3], x.c[0] * d[9]];
        let xabs: f64 = x.c.iter().map(|v| v.abs()).sum();
        let enl = xabs * dabs - (x.c[0] * d[0]).abs() - el.iter().map(|v| v.abs()).sum::<f64>();
        let lin: f64 = (0..5).map(|i| (al[i] - el[i]).abs()).sum();
        if c0 - lin - (an + enl) > tol { cost += 1.0; } else { cost += 25.0; }
    }
    cost
}

fn check_cand(ctx: &Ctx, b: &Bx, bp: &BoxPolys, c: &Cand) -> (bool, f64, [f64; 5]) {
    if std::env::var("TIERS").is_ok() {
        let r = check_cand_full(ctx, b, bp, c);
        if !r.0 { return r; }
        return (tiers_ok(ctx, b, bp, c), r.1, r.2);
    }
    check_cand_full(ctx, b, bp, c)
}

fn check_cand_full(ctx: &Ctx, b: &Bx, bp: &BoxPolys, c: &Cand) -> (bool, f64, [f64; 5]) {
    let w = c.w;
    let alpha: Vec<P> = (0..3).map(|k| bp.no[0][k].scale(w[0]).add(&bp.no[1][k].scale(w[1]))).collect();
    let sv = ctx.verts[c.s];
    let nx = alpha[0].c.len();
    let ny = bp.dr.c.len();
    let mut a = B::zero(nx, ny);
    for k in 0..3 {
        let mut beta = P::zero(3, DY);
        for m in 0..3 {
            beta = beta.add(&bp.cnr[k][m].scale(sv[m]));
        }
        a.add_outer(&alpha[k], &beta, 1.0);
    }
    let mut worst = f64::INFINITY;
    let paired = if b.blowup() { ctx.pair(b.chart, c.s) } else { None };
    if paired.is_some() {
        let bm = chart(b.chart);
        // L = 2 α·(c×S + ρ c×(c×S))
        let cy = bp.cy.as_ref().unwrap();
        let rho = bp.rho.as_ref().unwrap();
        let s = [P::constant(3, DY, sv[0]), P::constant(3, DY, sv[1]), P::constant(3, DY, sv[2])];
        let cross = |a: &[P; 3], b: &[P; 3]| -> [P; 3] {
            [
                a[1].mul(&b[2]).sub(&a[2].mul(&b[1])),
                a[2].mul(&b[0]).sub(&a[0].mul(&b[2])),
                a[0].mul(&b[1]).sub(&a[1].mul(&b[0])),
            ]
        };
        let cs = cross(cy, &s);
        let ccs = cross(cy, &cs);
        let mut l = B::zero(nx, ny);
        let inner: Vec<P> = (0..3).map(|k| cs[k].add(&ccs[k].mul(rho))).collect();
        for k in 0..3 {
            let mut y = P::zero(3, DY);
            for m in 0..3 {
                if bm[k][m] != 0.0 {
                    y = y.add(&inner[m].scale(bm[k][m]));
                }
            }
            l.add_outer(&alpha[k], &y, 2.0);
        }
        let mut lb = ctx.cx.lower(&l);
        if bern() && lb <= 1e-11 * (w[0].abs() + w[1].abs()) { lb = lb.max(bern_lower(&l.c)); }
        worst = worst.min(lb);
        if lb <= 1e-11 * (w[0].abs() + w[1].abs()) {
            return (false, lb, slack_vars(&l));
        }
    }
    for j in 0..ctx.verts.len() {
        if paired == Some(j) {
            continue;
        }
        let pj = ctx.verts[j];
        let x = alpha[0].scale(pj[0]).add(&alpha[1].scale(pj[1])).add(&alpha[2].scale(pj[2]));
        let mut lb = ctx.cx.lower_minus_outer(&a, &x, &bp.dr);
        if bern() && lb <= 1e-11 * (w[0].abs() + w[1].abs()) {
            let mut m = a.clone();
            m.add_outer(&x, &bp.dr, -1.0);
            lb = lb.max(bern_lower(&m.c));
        }
        worst = worst.min(lb);
        if lb <= 1e-11 * (w[0].abs() + w[1].abs()) {
            let mut m = a.clone();
            m.add_outer(&x, &bp.dr, -1.0);
            return (false, lb, slack_vars(&m));
        }
    }
    (true, worst, [0.0; 5])
}

/// All constraint forms of a gap leaf for inner vertex `s` and direction `w`, materialized.
fn gap_forms(ctx: &Ctx, b: &Bx, bp: &BoxPolys, s: usize, w: [f64; 2]) -> Vec<B> {
    let alpha: Vec<P> = (0..3).map(|k| bp.no[0][k].scale(w[0]).add(&bp.no[1][k].scale(w[1]))).collect();
    let sv = ctx.verts[s];
    let nx = alpha[0].c.len();
    let ny = bp.dr.c.len();
    let mut a = B::zero(nx, ny);
    for k in 0..3 {
        let mut beta = P::zero(3, DY);
        for m in 0..3 {
            beta = beta.add(&bp.cnr[k][m].scale(sv[m]));
        }
        a.add_outer(&alpha[k], &beta, 1.0);
    }
    let mut out = vec![];
    let paired = if b.blowup() { ctx.pair(b.chart, s) } else { None };
    if paired.is_some() {
        let bm = chart(b.chart);
        let cy = bp.cy.as_ref().unwrap();
        let rho = bp.rho.as_ref().unwrap();
        let sp = [P::constant(3, DY, sv[0]), P::constant(3, DY, sv[1]), P::constant(3, DY, sv[2])];
        let cross = |a: &[P; 3], b: &[P; 3]| -> [P; 3] {
            [
                a[1].mul(&b[2]).sub(&a[2].mul(&b[1])),
                a[2].mul(&b[0]).sub(&a[0].mul(&b[2])),
                a[0].mul(&b[1]).sub(&a[1].mul(&b[0])),
            ]
        };
        let cs = cross(cy, &sp);
        let ccs = cross(cy, &cs);
        let mut l = B::zero(nx, ny);
        let inner: Vec<P> = (0..3).map(|k| cs[k].add(&ccs[k].mul(rho))).collect();
        for k in 0..3 {
            let mut y = P::zero(3, DY);
            for m in 0..3 {
                if bm[k][m] != 0.0 {
                    y = y.add(&inner[m].scale(bm[k][m]));
                }
            }
            l.add_outer(&alpha[k], &y, 2.0);
        }
        out.push(l);
    }
    for j in 0..ctx.verts.len() {
        if paired == Some(j) {
            continue;
        }
        let pj = ctx.verts[j];
        let x = alpha[0].scale(pj[0]).add(&alpha[1].scale(pj[1])).add(&alpha[2].scale(pj[2]));
        let mut m = a.clone();
        m.add_outer(&x, &bp.dr, -1.0);
        out.push(m);
    }
    out
}

/// Optimize the direction angle for inner vertex `s` on box `b`: maximize the worst lower bound.
fn optimize_w(ctx: &Ctx, b: &Bx, bp: &BoxPolys, s: usize, th0: f64) -> (f64, f64, B) {
    let f0 = gap_forms(ctx, b, bp, s, [1.0, 0.0]);
    let f1 = gap_forms(ctx, b, bp, s, [0.0, 1.0]);
    let eval = |th: f64| -> (f64, usize) {
        let (c, sn) = (th.cos(), th.sin());
        let mut worst = f64::INFINITY;
        let mut arg = 0;
        for k in 0..f0.len() {
            let mut m = f0[k].clone();
            for (x, y) in m.c.iter_mut().zip(f1[k].c.iter()) {
                *x = c * *x + sn * y;
            }
            let lb = ctx.cx.lower(&m);
            if lb < worst { worst = lb; arg = k; }
        }
        (worst, arg)
    };
    let mut best = (th0, eval(th0));
    let mut step = 0.12;
    for _ in 0..12 {
        let mut improved = false;
        for d in [-step, step] {
            let t = best.0 + d;
            let e = eval(t);
            if e.0 > best.1 .0 { best = (t, e); improved = true; }
        }
        if !improved { step *= 0.5; }
    }
    let (c, sn) = (best.0.cos(), best.0.sin());
    let mut m = f0[best.1 .1].clone();
    for (x, y) in m.c.iter_mut().zip(f1[best.1 .1].c.iter()) { *x = c * *x + sn * y; }
    (best.0, best.1 .0, m)
}

#[derive(Default, Debug, Clone)]
struct Stats {
    domain: usize,
    cert: usize,
    fail: usize,
    nodes: usize,
    cand_checks: usize,
    vol_cert: f64,
    vol_dom: f64,
    affine: usize,
}

/// Try affine-direction certificates for the best few inner vertices (env AFFW).
fn try_affine(ctx: &Ctx, b: &Bx, bp: &BoxPolys) -> Option<(usize, affine::AffW)> {
    if std::env::var("AFFW").is_err() { return None; }
    let na: usize = std::env::var("ANS").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let cl = Classes { x: P::classes(2, affine::DA), y: P::classes(3, affine::DA) };
    for c in candidates_n(ctx, b, na) {
        let th0 = match affine::opt_theta(ctx, b, c.s, [0.0; 5]) { Some(t) => t, None => continue };
        for gain in [1.0, 0.5] {
            let aw = affine::affine_dir(ctx, b, c.s, th0, 0.5, gain);
            if affine::check_affine(ctx, &cl, b, bp, c.s, &aw) { return Some((c.s, aw)); }
        }
    }
    None
}

fn scaled_widths(b: &Bx) -> [f64; 5] {
    let mut w = [0.0; 5];
    for i in 0..2 {
        w[i] = 2.0 * b.h(i);
    }
    if b.blowup() {
        let rho_hi = b.hi[4];
        w[2] = 2.0 * rho_hi * b.h(2);
        w[3] = 2.0 * rho_hi * b.h(3);
        w[4] = 2.0 * b.h(4);
    } else {
        for i in 2..5 {
            let rc = b.c(i);
            w[i] = 2.0 * b.h(i) / (1.0 + rc * rc).sqrt();
        }
    }
    w
}

fn volume(b: &Bx) -> f64 {
    (0..5).map(|i| b.hi[i] - b.lo[i]).product()
}

fn solve_rec(ctx: &Ctx, b: Bx, depth: usize, max_depth: usize, st: &mut Stats, fails: &mut Vec<Bx>, out: &mut String) {
    st.nodes += 1;
    let bp = box_polys(&b);
    if let Some(code) = domain_excluded(ctx, &b, &bp) {
        st.domain += 1;
        st.vol_dom += volume(&b);
        out.push_str(&format!("D{} ", code));
        return;
    }
    if std::env::var("OPTW").is_ok() {
        let ns: usize = std::env::var("NS").ok().and_then(|s| s.parse().ok()).unwrap_or(6);
        let base = candidates_n(ctx, &b, ns);
        let mut best_fail: Option<(f64, B)> = None;
        for c in base.iter() {
            st.cand_checks += 1;
            let th0 = c.w[1].atan2(c.w[0]);
            let (th, lb, form) = optimize_w(ctx, &b, &bp, c.s, th0);
            if lb > 0.0 {
                let q = Cand { s: c.s, w: [(th.cos() * 1024.0).round(), (th.sin() * 1024.0).round()], score: lb };
                if check_cand(ctx, &b, &bp, &q).0 {
                    st.cert += 1;
                    st.vol_cert += volume(&b);
                    out.push_str(&format!("G{}:{}:{} ", q.s, q.w[0] as i64, q.w[1] as i64));
                    return;
                }
            }
            if best_fail.as_ref().map_or(true, |f| lb > f.0) { best_fail = Some((lb, form)); }
        }
        if depth >= max_depth {
            st.fail += 1;
            fails.push(b);
            out.push_str("F ");
            return;
        }
        let w = best_fail.map(|f| slack_vars(&f.1)).unwrap_or_else(|| scaled_widths(&b));
        let mut i = 0;
        for k in 1..5 {
            if w[k] > w[i] {
                i = k;
            }
        }
        let (x, y) = b.split(i);
        out.push_str(&format!("S{} ", i));
        solve_rec(ctx, x, depth + 1, max_depth, st, fails, out);
        solve_rec(ctx, y, depth + 1, max_depth, st, fails, out);
        return;
    }
    let cands = if std::env::var("WIDE").is_ok() {
        let ns: usize = std::env::var("NS").ok().and_then(|s| s.parse().ok()).unwrap_or(8);
        let amax: f64 = std::env::var("AMAX").ok().and_then(|s| s.parse().ok()).unwrap_or(0.2);
        let na: usize = std::env::var("NA").ok().and_then(|s| s.parse().ok()).unwrap_or(3);
        let mut offs = vec![0.0];
        for k in 1..=na { let o = amax * k as f64 / na as f64; offs.push(-o); offs.push(o); }
        candidates_wide(ctx, &b, ns, &offs)
    } else {
        candidates(ctx, &b).into_iter().take(3).collect()
    };
    let mut slack: Option<[f64; 5]> = None;
    let kc: usize = std::env::var("KCOST").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut best: Option<(f64, Cand)> = None;
    let mut npass = 0;
    for c in cands.iter() {
        st.cand_checks += 1;
        let (good, _, sl) = check_cand(ctx, &b, &bp, c);
        if good {
            if kc == 0 {
                st.cert += 1;
                st.vol_cert += volume(&b);
                out.push_str(&format!("G{}:{}:{} ", c.s, c.w[0] as i64, c.w[1] as i64));
                return;
            }
            let k = kernel_cost(ctx, &b, &bp, c);
            if best.map_or(true, |(bk, _)| k < bk) { best = Some((k, *c)); }
            npass += 1;
            if npass >= kc || k <= 31.0 { break; }
        } else if slack.is_none() {
            slack = Some(sl);
        }
    }
    if let Some((_, c)) = best {
        st.cert += 1;
        st.vol_cert += volume(&b);
        out.push_str(&format!("G{}:{}:{} ", c.s, c.w[0] as i64, c.w[1] as i64));
        return;
    }
    if let Some((s, aw)) = try_affine(ctx, &b, &bp) {
        st.cert += 1;
        st.vol_cert += volume(&b);
        st.affine += 1;
        out.push_str(&format!("A{}:{:?} ", s, aw));
        return;
    }
    if depth >= max_depth {
        st.fail += 1;
        fails.push(b);
        out.push_str("F ");
        return;
    }
    let w = slack.unwrap_or_else(|| scaled_widths(&b));
    let mut order = [0usize, 1, 2, 3, 4];
    order.sort_by(|&a, &c| w[c].partial_cmp(&w[a]).unwrap());
    let mut i = order[0];
    if std::env::var("LOOK").is_ok() {
        let nl: usize = std::env::var("NL").ok().and_then(|s| s.parse().ok()).unwrap_or(3);
        let quick = |bb: &Bx| -> bool {
            let bpp = box_polys(bb);
            if domain_excluded(ctx, bb, &bpp).is_some() { return true; }
            let qs: usize = std::env::var("QS").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
            let cs = if qs >= 12 { candidates_wide(ctx, bb, 12, &[0.0, -0.02, 0.02, -0.04, 0.04, -0.06, 0.06, -0.08, 0.08, -0.1, 0.1, -0.12, 0.12]) } else { candidates_wide(ctx, bb, qs, &[0.0, -0.04, 0.04]) };
            cs.iter().any(|c| check_cand(ctx, bb, &bpp, c).0) || try_affine(ctx, bb, &bpp).is_some()
        };
        let mut best = (0usize, i);
        for &d in order.iter().take(nl) {
            let (x, y) = b.split(d);
            let n = quick(&x) as usize + quick(&y) as usize;
            if n > best.0 { best = (n, d); }
            if n == 2 { break; }
        }
        if best.0 == 0 && std::env::var("LOOK2").is_ok() {
            // two-level: for each split, the best number of passing grandchildren per child
            let gc = |bb: &Bx| -> usize {
                let mut m = 0;
                for d2 in 0..5 {
                    let (p, q) = bb.split(d2);
                    let n = quick(&p) as usize + quick(&q) as usize;
                    if n > m { m = n; }
                    if m == 2 { break; }
                }
                m
            };
            let mut b2 = (0usize, i);
            for &d in order.iter().take(nl) {
                let (x, y) = b.split(d);
                let n = gc(&x) + gc(&y);
                if n > b2.0 { b2 = (n, d); }
                if n == 4 { break; }
            }
            best = b2;
        }
        i = best.1;
    }
    let (x, y) = b.split(i);
    out.push_str(&format!("S{} ", i));
    solve_rec(ctx, x, depth + 1, max_depth, st, fails, out);
    solve_rec(ctx, y, depth + 1, max_depth, st, fails, out);
}

#[allow(dead_code)]
fn solve(ctx: &Ctx, root: Bx, max_depth: usize, st: &mut Stats, fails: &mut Vec<Bx>) {
    let mut stack = vec![(root, 0usize)];
    while let Some((b, depth)) = stack.pop() {
        st.nodes += 1;
        let bp = box_polys(&b);
        if domain_excluded(ctx, &b, &bp).is_some() {
            st.domain += 1;
            st.vol_dom += volume(&b);
            continue;
        }
        let cands = candidates(ctx, &b);
        let mut ok = false;
        let mut slack: Option<[f64; 5]> = None;
        for c in cands.iter().take(3) {
            st.cand_checks += 1;
            let (good, _, sl) = check_cand(ctx, &b, &bp, c);
            if good {
                ok = true;
                break;
            }
            if slack.is_none() {
                slack = Some(sl);
            }
        }
        if ok {
            st.cert += 1;
            st.vol_cert += volume(&b);
            continue;
        }
        if depth >= max_depth {
            st.fail += 1;
            fails.push(b);
            continue;
        }
        let w = slack.unwrap_or_else(|| scaled_widths(&b));
        let mut i = 0;
        for k in 1..5 {
            if w[k] > w[i] {
                i = k;
            }
        }
        let (x, y) = b.split(i);
        stack.push((x, depth + 1));
        stack.push((y, depth + 1));
    }
}

fn sample(ctx: &Ctx, n: usize) {
    // xorshift
    let mut s: u64 = 88172645463325252;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s >> 11) as f64 / (1u64 << 53) as f64 };
    let mut hist = vec![0usize; 4];
    let mut margins: Vec<Vec<f64>> = vec![vec![]; 4];
    let z = [[-1.0,0.0,0.0],[0.0,-1.0,0.0],[0.0,0.0,1.0]];
    for _ in 0..n {
        let u = rnd(); let v = rnd() * 0.41;
        if u*u+v*v > 1.0 || v > ctx.m_wedge*u { continue; }
        let ch = (rnd()*4.0) as usize;
        let r = [rnd()*2.0-1.0, rnd()*2.0-1.0, rnd()*2.0-1.0];
        let q = mm(&chart(ch), &cay(r[0], r[1], r[2]));
        let ro = outer(u, v);
        let hn = mm(&transpose(&ro), &mm(&z, &ro));
        let t0 = trace(&q);
        let mut ok = true;
        for k in 0..15 { for e in 0..2 {
            if k==0 && e==0 { continue; }
            let mut x = mm(&q, &ctx.group[k]);
            if e==1 { x = mm(&hn, &x); }
            if trace(&x) > t0 { ok = false; }
        }}
        if !ok { continue; }
        hist[ch] += 1;
        if hist[ch] <= 3 { println!("pt chart {} u {:.3} v {:.3} r {:?}", ch, u, v, r); }
        let b = Bx { chart: if ch==0 {1} else {ch}, face: 0, lo: [u,v,r[0],r[1],r[2]], hi: [u,v,r[0],r[1],r[2]] };
        // use chart-mode candidate scoring at the point
        let b = if ch == 0 { Bx { chart: 4, ..b } } else { b };
        let c = candidates(ctx, &b);
        margins[ch].push(c.first().map(|c| c.score).unwrap_or(-1.0));
    }
    println!("in-domain counts per chart {:?}", hist);
    for ch in 0..4 {
        let mut m = margins[ch].clone();
        m.sort_by(|a,b| a.partial_cmp(b).unwrap());
        if m.is_empty() { continue; }
        let q = |f: f64| m[((m.len()-1) as f64 * f) as usize];
        println!("chart {} n {} margin min {:.2e} p1 {:.2e} p10 {:.2e} p50 {:.2e}", ch, m.len(), q(0.0), q(0.01), q(0.1), q(0.5));
    }
}

fn root_box(i: usize) -> Bx {
    if i < 3 {
        Bx { chart: i + 1, face: 0, lo: [0.0, 0.0, -1.0, -1.0, -1.0], hi: [1.0, 0.5, 1.0, 1.0, 1.0] }
    } else if i < 9 {
        Bx { chart: 0, face: i - 3, lo: [0.0, 0.0, -1.0, -1.0, 0.0], hi: [1.0, 0.5, 1.0, 1.0, 1.0] }
    } else {
        Bx { chart: 4, face: i - 9, lo: [0.0, 0.0, -1.0, -1.0, 0.0], hi: [1.0, 0.5, 1.0, 1.0, 2.0] }
    }
}

fn box_at(root: &Bx, x: &[f64; 5], h: &[f64; 5]) -> Bx {
    let mut b = *root;
    for i in 0..5 {
        b.lo[i] = (x[i] - h[i]).max(root.lo[i]);
        b.hi[i] = (x[i] + h[i]).min(root.hi[i]);
    }
    b
}

fn box_ok(ctx: &Ctx, b: &Bx, cands: &[Cand]) -> bool {
    let bp = box_polys(b);
    cands.iter().any(|c| check_cand(ctx, b, &bp, c).0)
}

/// Largest gradient-shaped box around `x` accepted by the certificate test; returns its volume.
fn opt_box(ctx: &Ctx, root: &Bx, x: &[f64; 5]) -> Option<f64> { opt_box_d(ctx, root, x).map(|d| d.0) }

fn opt_box_d(ctx: &Ctx, root: &Bx, x: &[f64; 5]) -> Option<(f64, [f64; 5], f64, f64)> {
    let tiny = [1e-9; 5];
    let b0 = box_at(root, x, &tiny);
    if domain_excluded(ctx, &b0, &box_polys(&b0)).is_some() {
        return None;
    }
    let wide = std::env::var("WIDE").is_ok();
    let cands: Vec<Cand> = if wide {
        candidates_wide(ctx, &b0, 8, &[0.0, -0.05, 0.05, -0.1, 0.1, -0.2, 0.2])
    } else {
        candidates(ctx, &b0).into_iter().take(3).collect()
    };
    if cands.is_empty() || !box_ok(ctx, &b0, &cands) {
        return Some((0.0, [0.0; 5], 0.0, 0.0));
    }
    if wide {
        let mut best: Option<(f64, [f64; 5], f64, f64)> = None;
        for c in cands.iter() {
            let one = [*c];
            if !box_ok(ctx, &b0, &one) { continue; }
            let r = grow_box(ctx, root, x, &one);
            if best.map_or(true, |b| r.0 > b.0) { best = Some((r.0, r.1, r.2, c.score)); }
        }
        return best;
    }
    let r = grow_box(ctx, root, x, &cands);
    Some((r.0, r.1, r.2, cands[0].score))
}

fn grow_box(ctx: &Ctx, root: &Bx, x: &[f64; 5], cands: &[Cand]) -> (f64, [f64; 5], f64) {
    let tiny = [1e-9; 5];
    // per-axis reach
    let mut reach = [0.0; 5];
    for i in 0..5 {
        let (mut lo, mut hi) = (1e-9, root.hi[i] - root.lo[i]);
        for _ in 0..30 {
            let mid = (lo * hi).sqrt();
            let mut h = tiny;
            h[i] = mid;
            if box_ok(ctx, &box_at(root, x, &h), &cands) { lo = mid } else { hi = mid }
        }
        reach[i] = lo;
    }
    let (mut lo, mut hi) = (1e-6f64, 1.0f64);
    for _ in 0..25 {
        let mid = (lo * hi).sqrt();
        let h = reach.map(|r| r * mid);
        if box_ok(ctx, &box_at(root, x, &h), &cands) { lo = mid } else { hi = mid }
    }
    let b = box_at(root, x, &reach.map(|r| r * lo));
    (volume(&b), reach, lo)
}

fn diag(ctx: Arc<Ctx>, root_i: usize, n: usize) {
    let root = root_box(root_i);
    let out = Arc::new(Mutex::new(vec![]));
    let next = Arc::new(AtomicUsize::new(0));
    let mut hs = vec![];
    for _ in 0..16 {
        let (ctx, next, out) = (ctx.clone(), next.clone(), out.clone());
        hs.push(std::thread::spawn(move || loop {
            let k = next.fetch_add(1, Ordering::SeqCst);
            if k >= n { break; }
            let mut s: u64 = 0x9E3779B97F4A7C15u64.wrapping_mul(k as u64 + 7 + 1000003 * root_i as u64);
            let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s >> 11) as f64 / (1u64 << 53) as f64 };
            let mut x = [0.0; 5];
            for d in 0..5 { x[d] = root.lo[d] + (root.hi[d] - root.lo[d]) * rnd(); }
            if let Some(d) = opt_box_d(&ctx, &root, &x) {
                if d.0 > 0.0 { out.lock().unwrap().push((x, d)); }
            }
        }));
    }
    for h in hs { h.join().unwrap(); }
    let mut v = out.lock().unwrap();
    let vr = volume(&root);
    v.sort_by(|a, b| a.1 .0.partial_cmp(&b.1 .0).unwrap());
    let tot: f64 = v.iter().map(|(_, d)| vr / n as f64 / d.0).sum();
    let mut acc = 0.0;
    for (k, (x, d)) in v.iter().enumerate() {
        acc += vr / n as f64 / d.0;
        if k < 12 || k == v.len() / 100 || k == v.len() / 10 {
            println!("#{} cum {:.2} x {:?} vol {:.2e} margin {:.4} lam {:.3} reach {:?}", k, acc / tot,
                x.map(|t| (t * 1e4).round() / 1e4), d.0, d.3, d.2, d.1.map(|r| (r * 1e4).round() / 1e4));
        }
    }
    // buckets by x[4] (rho or r2)
    let nb = 8;
    let mut cnt = vec![0.0; nb]; let mut num = vec![0usize; nb];
    let mut lam = vec![0.0; nb]; let mut reach = vec![[0.0f64; 5]; nb]; let mut marg = vec![0.0; nb];
    for (x, d) in v.iter() {
        let t = (x[4] - root.lo[4]) / (root.hi[4] - root.lo[4]);
        let b = ((t * nb as f64) as usize).min(nb - 1);
        cnt[b] += vr / n as f64 / d.0; num[b] += 1; lam[b] += d.2.ln(); marg[b] += d.3.ln();
        for i in 0..5 { reach[b][i] += d.1[i].ln(); }
    }
    println!("root {} samples in-domain {}", root_i, v.len());
    for b in 0..nb {
        if num[b] == 0 { continue; }
        let m = num[b] as f64;
        println!("x4 in [{:.3},{:.3}) n {:5} est {:8.0} lambda {:.3} margin {:.4} reach {:?}",
            root.lo[4] + (root.hi[4]-root.lo[4]) * b as f64 / nb as f64,
            root.lo[4] + (root.hi[4]-root.lo[4]) * (b+1) as f64 / nb as f64,
            num[b], cnt[b], (lam[b]/m).exp(), (marg[b]/m).exp(),
            reach[b].map(|r| ((r/m).exp() * 1e4).round() / 1e4));
    }
}

fn optbox(ctx: Arc<Ctx>, n: usize) {
    let mut total = 0.0;
    for i in 0..15 {
        let root = root_box(i);
        let next = Arc::new(AtomicUsize::new(0));
        let acc = Arc::new(Mutex::new((0.0f64, 0usize, 0usize)));
        let mut hs = vec![];
        for _ in 0..16 {
            let (ctx, next, acc) = (ctx.clone(), next.clone(), acc.clone());
            hs.push(std::thread::spawn(move || loop {
                let k = next.fetch_add(1, Ordering::SeqCst);
                if k >= n { break; }
                let mut s: u64 = 0x9E3779B97F4A7C15u64.wrapping_mul(k as u64 + 1 + 1000003 * i as u64);
                let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s >> 11) as f64 / (1u64 << 53) as f64 };
                let mut x = [0.0; 5];
                for d in 0..5 { x[d] = root.lo[d] + (root.hi[d] - root.lo[d]) * rnd(); }
                let r = opt_box(&ctx, &root, &x);
                let mut a = acc.lock().unwrap();
                match r {
                    None => {}
                    Some(v) if v > 0.0 => { a.0 += 1.0 / v; a.1 += 1; }
                    Some(_) => { a.2 += 1; }
                }
            }));
        }
        for h in hs { h.join().unwrap(); }
        let a = acc.lock().unwrap();
        let est = volume(&root) * a.0 / n as f64;
        total += est;
        println!("root {} in-domain {} zero {} est leaves {:.0}", i, a.1, a.2, est);
    }
    println!("TOTAL est {:.0}", total);
}

/// Parse one exported root tree and collect its gap leaves' boxes.
fn leaves_of(root: Bx, toks: &[&str], pos: &mut usize, out: &mut Vec<Bx>) {
    let t = toks[*pos];
    *pos += 1;
    if let Some(d) = t.strip_prefix('S') {
        let (a, b) = root.split(d.parse().unwrap());
        leaves_of(a, toks, pos, out);
        leaves_of(b, toks, pos, out);
    } else if t.starts_with('G') {
        out.push(root);
    }
}

/// Collect the parents of gap leaves.
fn parents_of(root: Bx, toks: &[&str], pos: &mut usize, out: &mut Vec<Bx>) {
    let t = toks[*pos];
    *pos += 1;
    if let Some(d) = t.strip_prefix('S') {
        let (a, b) = root.split(d.parse().unwrap());
        let s0 = *pos;
        parents_of(a, toks, pos, out);
        let s1 = *pos;
        parents_of(b, toks, pos, out);
        if toks[s0].starts_with('G') || toks[s1].starts_with('G') { out.push(root); }
    }
}

fn eval_b(f: &B, cx: usize, tx: &[f64; 2], ty: &[f64; 3], dx: usize, dy: usize) -> f64 {
    let _ = cx;
    let px: Vec<f64> = (0..f.nx).map(|i| {
        let e0 = i % (dx + 1); let e1 = i / (dx + 1);
        tx[0].powi(e0 as i32) * tx[1].powi(e1 as i32)
    }).collect();
    let py: Vec<f64> = (0..f.ny).map(|j| {
        let e0 = j % (dy + 1); let e1 = (j / (dy + 1)) % (dy + 1); let e2 = j / ((dy + 1) * (dy + 1));
        ty[0].powi(e0 as i32) * ty[1].powi(e1 as i32) * ty[2].powi(e2 as i32)
    }).collect();
    let mut s = 0.0;
    for i in 0..f.nx { for j in 0..f.ny { s += f.c[i * f.ny + j] * px[i] * py[j]; } }
    s
}

/// Apply a 3×3 map to axis `ax` of a 3^5 tensor stored as a 9×27 bilinear form.
fn axis_map(c: &[f64], ax: usize, m: &[[f64; 3]; 3]) -> Vec<f64> {
    let stride = [1usize, 3, 27, 81, 243][ax]; // flat = i*27 + j, i = e0 + 3e1, j = e2 + 3e3 + 9e4
    let st = match ax { 0 => 27, 1 => 81, 2 => 1, 3 => 3, _ => 9 };
    let _ = stride;
    let mut out = vec![0.0; 243];
    for f in 0..243 {
        let i = f / 27; let j = f % 27;
        let e = [i % 3, i / 3, j % 3, (j / 3) % 3, j / 9][ax];
        let base = f - e * st;
        for r in 0..3 { out[base + r * st] += m[r][e] * c[f]; }
    }
    out
}

fn degs(f: usize) -> usize { let i = f / 27; let j = f % 27; i % 3 + i / 3 + j % 3 + (j / 3) % 3 + j / 9 }

/// Power(t ∈ [-1,1]) → Bernstein transform of degree n: row k gives b_k from a_0..a_n.
fn bern_mat(n: usize) -> Vec<Vec<f64>> {
    let binom = |a: usize, b: usize| -> f64 { (0..b).fold(1.0, |acc, i| acc * (a - i) as f64 / (i + 1) as f64) };
    // x-power coefficients of t^j = (2x-1)^j
    let mut m = vec![vec![0.0; n + 1]; n + 1];
    for j in 0..=n {
        let xp: Vec<f64> = (0..=n).map(|q| if q <= j { binom(j, q) * 2f64.powi(q as i32) * (-1f64).powi((j - q) as i32) } else { 0.0 }).collect();
        for k in 0..=n {
            let mut b = 0.0;
            for q in 0..=k { b += binom(k, q) / binom(n, q) * xp[q]; }
            m[k][j] = b;
        }
    }
    m
}

/// Min Bernstein coefficient of a dense tensor with per-axis degrees `degs` (axis 0 fastest),
/// given as a flat vector.
fn bern_lower_nd(c: &[f64], degs: &[usize]) -> f64 {
    let mut v = c.to_vec();
    let mut stride = 1;
    for &n in degs {
        let m = bern_mat(n);
        let mut out = vec![0.0; v.len()];
        for f in 0..v.len() {
            if v[f] == 0.0 { continue; }
            let e = (f / stride) % (n + 1);
            let base = f - e * stride;
            for k in 0..=n { out[base + k * stride] += m[k][e] * v[f]; }
        }
        v = out;
        stride *= n + 1;
    }
    v.iter().cloned().fold(f64::INFINITY, f64::min)
}

/// Lower bound of a polynomial: the parity bound, improved by Bernstein under BERND.
fn plow(p: &P) -> f64 {
    let lb = p.lower();
    if lb > 1e-9 || std::env::var("BERND").is_err() { return lb; }
    lb.max(bern_lower_nd(&p.c, &vec![p.d; p.nv]))
}

/// Same for a bilinear form whose X axes have degree `dx` (2 vars) and Y axes `dy` (3 vars).
fn blow(cl: &Classes, f: &B, dx: usize, dy: usize) -> f64 {
    let lb = cl.lower(f);
    if lb > 1e-9 || std::env::var("BERND").is_err() { return lb; }
    // flat = i * ny + j; reorder to Y-fastest is already the layout: j axes then i axes
    lb.max(bern_lower_nd(&f.c, &[dy, dy, dy, dx, dx]))
}

fn bern() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var("BERN").is_ok())
}

fn bern_lower(c: &[f64]) -> f64 {
    let m = [[1.0, -1.0, 1.0], [1.0, 0.0, -1.0], [1.0, 1.0, 1.0]];
    let mut v = c.to_vec();
    for ax in 0..5 { v = axis_map(&v, ax, &m); }
    v.iter().cloned().fold(f64::INFINITY, f64::min)
}

fn corner_lower(c: &[f64]) -> f64 {
    // linear coefficients: flat index of t_ax
    let lin = [27usize, 81, 1, 3, 9];
    let mut v = c.to_vec();
    for ax in 0..5 {
        let sg = if c[lin[ax]] > 0.0 { -1.0 } else { 1.0 }; // corner t_ax = sg minimizes the linear part
        let m = [[1.0, sg, 1.0], [0.0, -sg, -2.0], [0.0, 0.0, 1.0]];
        v = axis_map(&v, ax, &m);
    }
    let mut s = v[0];
    for f in 1..243 { if v[f] < 0.0 { s += v[f] * 2f64.powi(degs(f) as i32); } }
    s
}

/// For parents of gap leaves: does some candidate's certificate polynomial stay positive
/// (sampled true minimum) although the checker's lower bound fails?
fn parentdiag(ctx: Arc<Ctx>, file: &str, nsamp: usize) {
    let text = std::fs::read_to_string(file).unwrap();
    let toks: Vec<&str> = text.split_whitespace().collect();
    let mut pos = 0;
    let mut all: Vec<Bx> = vec![];
    for i in 0..15 { parents_of(root_box(i), &toks, &mut pos, &mut all); }
    println!("gap parents {}", all.len());
    let all = Arc::new(all);
    let next = Arc::new(AtomicUsize::new(0));
    let acc = Arc::new(Mutex::new((0usize, 0usize, 0usize, vec![], vec![], 0usize, 0usize, 0usize)));
    let mut hs = vec![];
    for _ in 0..16 {
        let (ctx, next, acc, all) = (ctx.clone(), next.clone(), acc.clone(), all.clone());
        hs.push(std::thread::spawn(move || loop {
            let k = next.fetch_add(1, Ordering::SeqCst);
            if k >= nsamp { break; }
            let idx = (k as u64).wrapping_mul(0x9E3779B97F4A7C15) as usize % all.len();
            let b = all[idx];
            let bp = box_polys(&b);
            let cands = candidates_wide(&ctx, &b, 12, &[0.0, -0.04, 0.04, -0.08, 0.08, -0.12, 0.12]);
            // grid of sample points
            let g = [-1.0, -0.5, 0.0, 0.5, 1.0];
            let mut best_true = f64::NEG_INFINITY;
            let mut best_bound = f64::NEG_INFINITY;
            let mut ratio = (0.0, 0.0);
            let mut best_corner = f64::NEG_INFINITY;
            let mut best_bern = f64::NEG_INFINITY;
            let mut best_mix = f64::NEG_INFINITY;
            for c in cands.iter() {
                let forms = gap_forms(&ctx, &b, &bp, c.s, c.w);
                let (mut cm, mut bm, mut mm_) = (f64::INFINITY, f64::INFINITY, f64::INFINITY);
                for f in forms.iter() {
                    let a = corner_lower(&f.c); let bb = bern_lower(&f.c); let sy = ctx.cx.lower(f);
                    cm = cm.min(a); bm = bm.min(bb); mm_ = mm_.min(a.max(sy));
                }
                best_corner = best_corner.max(cm); best_bern = best_bern.max(bm); best_mix = best_mix.max(mm_);
                let mut tmin = f64::INFINITY;
                let mut bmin = f64::INFINITY;
                let mut wf = 0;
                for (fi, f) in forms.iter().enumerate() {
                    let lb = ctx.cx.lower(f);
                    if lb < bmin { bmin = lb; wf = fi; }
                }
                // true min only over the constraints (cheap prefilter: forms whose bound < 0)
                for f in forms.iter() {
                    if ctx.cx.lower(f) > 0.0 { continue; }
                    for &a in &g { for &bb in &g { for &cc in &g { for &dd in &g { for &ee in &g {
                        let v = eval_b(f, 0, &[a, bb], &[cc, dd, ee], DX, DY);
                        if v < tmin { tmin = v; }
                    }}}}}
                }
                if tmin > best_true { best_true = tmin; }
                if bmin > best_bound {
                    best_bound = bmin;
                    let (c0, lin, nl) = form_stats(&forms[wf]);
                    let l: f64 = lin.iter().map(|x| x.abs()).sum();
                    ratio = (l / c0, nl / c0);
                }
            }
            let mut a = acc.lock().unwrap();
            a.0 += 1;
            if best_corner > 0.0 { a.5 += 1; }
            if best_bern > 0.0 { a.6 += 1; }
            if best_mix > 0.0 { a.7 += 1; }
            if best_true > 0.0 { a.1 += 1; }
            if best_bound > 0.0 { a.2 += 1; }
            a.3.push(ratio.0); a.4.push(ratio.1);
        }));
    }
    for h in hs { h.join().unwrap(); }
    let mut a = acc.lock().unwrap();
    println!("parents sampled {} true-positive (grid) {} bound-positive {} corner {} bernstein {} max(sym,corner) {}", a.0, a.1, a.2, a.5, a.6, a.7);
    a.3.sort_by(|x, y| x.partial_cmp(y).unwrap()); a.4.sort_by(|x, y| x.partial_cmp(y).unwrap());
    for q in [0.1, 0.5, 0.9] {
        let i = ((a.3.len() - 1) as f64 * q) as usize;
        println!("  q{} lin/c0 {:.3} nonlin/c0 {:.3}", q, a.3[i], a.4[i]);
    }
}

fn leafratio(ctx: Arc<Ctx>, file: &str, nsamp: usize) {
    let text = std::fs::read_to_string(file).unwrap();
    let toks: Vec<&str> = text.split_whitespace().collect();
    let mut pos = 0;
    let mut all: Vec<Bx> = vec![];
    for i in 0..15 {
        leaves_of(root_box(i), &toks, &mut pos, &mut all);
    }
    println!("gap leaves {}", all.len());
    let all = Arc::new(all);
    let next = Arc::new(AtomicUsize::new(0));
    let acc = Arc::new(Mutex::new(vec![]));
    let mut hs = vec![];
    for _ in 0..16 {
        let (ctx, next, acc, all) = (ctx.clone(), next.clone(), acc.clone(), all.clone());
        hs.push(std::thread::spawn(move || loop {
            let k = next.fetch_add(1, Ordering::SeqCst);
            if k >= nsamp { break; }
            let idx = (k as u64).wrapping_mul(0x9E3779B97F4A7C15) as usize % all.len();
            let b = all[idx];
            let root = if b.chart == 0 { root_box(3 + b.face) } else if b.chart == 4 { root_box(9 + b.face) } else { root_box(b.chart - 1) };
            let x = [b.c(0), b.c(1), b.c(2), b.c(3), b.c(4)];
            if let Some(v) = opt_box(&ctx, &root, &x) {
                if v > 0.0 { acc.lock().unwrap().push((volume(&b) / v, b.chart)); }
            }
        }));
    }
    for h in hs { h.join().unwrap(); }
    let mut r = acc.lock().unwrap().clone();
    let mean: f64 = r.iter().map(|x| x.0).sum::<f64>() / r.len() as f64;
    r.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    println!("samples {} mean leaf/opt {:.3} -> ideal est {:.0}", r.len(), mean, mean * all.len() as f64);
    for q in [0.1, 0.25, 0.5, 0.75, 0.9] { println!("  q{} {:.3}", q, r[((r.len() - 1) as f64 * q) as usize].0); }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let verts = vertices();
    let ctx = Ctx {
        verts,
        group: group(),
        cx: Classes { x: P::classes(2, DX), y: P::classes(3, DY) },
        cxh: Classes { x: P::classes(2, DXH), y: P::classes(3, DY) },
        m_wedge: 57.0 / 128.0,
        pair4: vec![],
        delta: std::env::var("DELTA").map(|s| s.parse().unwrap()).unwrap_or(0.125),
    };
    let mut ctx = ctx;
    let t = tau();
    ctx.pair4 = ctx.verts.iter().map(|v| {
        let w = mv(&t, v);
        ctx.verts.iter().position(|x| (0..3).all(|i| (x[i] - w[i]).abs() < 1e-9))
    }).collect();
    eprintln!("tau pairs: {}", ctx.pair4.iter().filter(|x| x.is_some()).count());
    if args[1] == "minimize" {
        let f = |i: usize| args[i].parse::<f64>().unwrap();
        let ch: usize = args[2].parse().unwrap();
        let mut x = [f(3),f(4),f(5),f(6),f(7)];
        let marg = |x: &[f64;5]| -> f64 {
            let ro = outer(x[0],x[1]);
            let ri = mm(&ro, &mm(&chart(ch), &cay(x[2],x[3],x[4])));
            let p = proj_pts(&ro, &ctx.verts); let q = proj_pts(&ri, &ctx.verts);
            let h = hull(&p);
            let mut best = f64::NEG_INFINITY;
            for s in 0..q.len() { let mut m = f64::NEG_INFINITY;
                for e in 0..h.len() { let a=p[h[e]]; let bb=p[h[(e+1)%h.len()]];
                    let nx = bb[1]-a[1]; let ny = -(bb[0]-a[0]); let l=(nx*nx+ny*ny).sqrt();
                    let d = ((q[s][0]-a[0])*nx + (q[s][1]-a[1])*ny)/l; if d>m {m=d;} }
                if m > best { best = m; } }
            best };
        let mut fx = marg(&x);
        let mut step = 1e-3;
        let mut seed: u64 = 12345;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; (seed >> 11) as f64 / (1u64 << 53) as f64 - 0.5 };
        for it in 0..400000 {
            let mut y = x; for i in 0..5 { y[i] += step * rnd(); }
            let fy = marg(&y);
            if fy < fx { x = y; fx = fy; }
            if it % 20000 == 19999 { step *= 0.6; }
        }
        println!("min margin {:.3e} at {:?}", fx, x);
        return;
    }
    if args[1] == "probe" {
        let f = |i: usize| args[i].parse::<f64>().unwrap();
        let b = Bx { chart: args[2].parse().unwrap(), face: 0, lo: [f(3),f(4),f(5),f(6),f(7)], hi: [f(3),f(4),f(5),f(6),f(7)] };
        // exact best separation: max over S of distance to outer hull, fine
        let u=b.c(0); let v=b.c(1); let r=b.r_at([0.0;3]);
        let ro = outer(u,v);
        let ri = mm(&ro, &mm(&chart(b.chart), &cay(r[0],r[1],r[2])));
        let p = proj_pts(&ro, &ctx.verts); let q = proj_pts(&ri, &ctx.verts);
        let h = hull(&p);
        let mut best = f64::NEG_INFINITY; let mut bs = 0;
        for s in 0..q.len() {
            // signed max edge violation
            let mut m = f64::NEG_INFINITY;
            for e in 0..h.len() { let a=p[h[e]]; let bb=p[h[(e+1)%h.len()]];
                let nx = bb[1]-a[1]; let ny = -(bb[0]-a[0]); let l=(nx*nx+ny*ny).sqrt();
                let d = ((q[s][0]-a[0])*nx + (q[s][1]-a[1])*ny)/l; if d>m {m=d;} }
            if m > best { best = m; bs = s; }
        }
        println!("best edge-violation {:.3e} at S {} hull size {}", best, bs, h.len());
        return;
    }
    if args[1] == "parentdiag" { parentdiag(Arc::new(ctx), &args[2], args[3].parse().unwrap()); return; }
    if args[1] == "leafratio" { leafratio(Arc::new(ctx), &args[2], args[3].parse().unwrap()); return; }
    if args[1] == "diag" { diag(Arc::new(ctx), args[2].parse().unwrap(), args[3].parse().unwrap()); return; }
    if args[1] == "optbox" { optbox(Arc::new(ctx), args[2].parse().unwrap()); return; }
    if args[1] == "sample" { sample(&ctx, args[2].parse().unwrap()); return; }
    // args: chart face u0 u1 v0 v1 y00 y01 y10 y11 y20 y21 maxdepth splitdepth
    let f = |i: usize| args[i].parse::<f64>().unwrap();
    let chart: usize = args[1].parse().unwrap();
    let face: usize = args[2].parse().unwrap();
    let root = Bx {
        chart,
        face,
        lo: [f(3), f(5), f(7), f(9), f(11)],
        hi: [f(4), f(6), f(8), f(10), f(12)],
    };
    let max_depth: usize = args[13].parse().unwrap();
    let split_depth: usize = args.get(14).map(|s| s.parse().unwrap()).unwrap_or(6);
    let out_path = std::env::var("OUT").ok();
    let (text, t) = run_root(Arc::new(ctx), root, max_depth, split_depth);
    if let Some(p) = out_path {
        std::fs::write(p, &text).unwrap();
    }
    let _ = t;
}

enum Sk {
    Leaf(usize),
    Node(usize, Box<Sk>, Box<Sk>),
}

fn build_sk(b: Bx, d: usize, work: &mut Vec<Bx>) -> Sk {
    if d == 0 {
        work.push(b);
        return Sk::Leaf(work.len() - 1);
    }
    let w = scaled_widths(&b);
    let mut i = 0;
    for k in 1..5 {
        if w[k] > w[i] {
            i = k;
        }
    }
    let (x, y) = b.split(i);
    let l = build_sk(x, d - 1, work);
    let r = build_sk(y, d - 1, work);
    Sk::Node(i, Box::new(l), Box::new(r))
}

fn emit(sk: &Sk, res: &[String], out: &mut String) {
    match sk {
        Sk::Leaf(i) => out.push_str(&res[*i]),
        Sk::Node(d, l, r) => {
            out.push_str(&format!("S{} ", d));
            emit(l, res, out);
            emit(r, res, out);
        }
    }
}

fn run_root(ctx: Arc<Ctx>, root: Bx, max_depth: usize, split_depth: usize) -> (String, Stats) {
    let mut work = vec![];
    let sk = build_sk(root, split_depth, &mut work);
    let n = work.len();
    let work = Arc::new(work);
    let next = Arc::new(AtomicUsize::new(0));
    let total = Arc::new(Mutex::new(Stats::default()));
    let fails = Arc::new(Mutex::new(vec![]));
    let results = Arc::new(Mutex::new(vec![String::new(); n]));
    let t0 = Instant::now();
    let nth = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    let mut hs = vec![];
    for _ in 0..nth {
        let (work, next, total, fails, ctx, results) =
            (work.clone(), next.clone(), total.clone(), fails.clone(), ctx.clone(), results.clone());
        hs.push(std::thread::spawn(move || loop {
            let i = next.fetch_add(1, Ordering::SeqCst);
            if i >= work.len() {
                break;
            }
            let mut st = Stats::default();
            let mut fl = vec![];
            let mut out = String::new();
            solve_rec(&ctx, work[i], split_depth, max_depth, &mut st, &mut fl, &mut out);
            results.lock().unwrap()[i] = out;
            let mut t = total.lock().unwrap();
            t.domain += st.domain;
            t.cert += st.cert;
            t.fail += st.fail;
            t.nodes += st.nodes;
            t.cand_checks += st.cand_checks;
            t.vol_cert += st.vol_cert;
            t.vol_dom += st.vol_dom;
            t.affine += st.affine;
            fails.lock().unwrap().extend(fl);
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let t = total.lock().unwrap().clone();
    let el = t0.elapsed().as_secs_f64();
    println!(
        "nodes {} domain {} cert {} (affine {}) fail {} candchecks {} vol_cert {:.3e} vol_dom {:.3e} time {:.1}s",
        t.nodes, t.domain, t.cert, t.affine, t.fail, t.cand_checks, t.vol_cert, t.vol_dom, el
    );
    let fl = fails.lock().unwrap();
    for b in fl.iter().step_by((fl.len() / 25).max(1)) {
        println!("FAIL {:?}", b);
    }
    let mut out = String::new();
    emit(&sk, &results.lock().unwrap(), &mut out);
    (out, t)
}
