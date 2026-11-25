//! Dense multivariate polynomials with a per-variable degree cap, evaluated
//! on the normalized box `[-1,1]^nv`.

#[derive(Clone, Debug)]
pub struct P {
    pub nv: usize,
    pub d: usize,
    pub c: Vec<f64>,
}

impl P {
    pub fn zero(nv: usize, d: usize) -> P {
        P { nv, d, c: vec![0.0; (d + 1).pow(nv as u32)] }
    }
    pub fn constant(nv: usize, d: usize, x: f64) -> P {
        let mut p = P::zero(nv, d);
        p.c[0] = x;
        p
    }
    /// `center + half * t_i`
    pub fn var(nv: usize, d: usize, i: usize, center: f64, half: f64) -> P {
        let mut p = P::constant(nv, d, center);
        p.c[(d + 1).pow(i as u32)] = half;
        p
    }
    pub fn exps(&self, mut idx: usize) -> [usize; 6] {
        let mut e = [0; 6];
        for i in 0..self.nv {
            e[i] = idx % (self.d + 1);
            idx /= self.d + 1;
        }
        e
    }
    pub fn add(&self, o: &P) -> P {
        let mut r = self.clone();
        for (a, b) in r.c.iter_mut().zip(o.c.iter()) {
            *a += b;
        }
        r
    }
    pub fn sub(&self, o: &P) -> P {
        let mut r = self.clone();
        for (a, b) in r.c.iter_mut().zip(o.c.iter()) {
            *a -= b;
        }
        r
    }
    pub fn scale(&self, s: f64) -> P {
        P { nv: self.nv, d: self.d, c: self.c.iter().map(|x| x * s).collect() }
    }
    pub fn add_const(&self, s: f64) -> P {
        let mut r = self.clone();
        r.c[0] += s;
        r
    }
    pub fn mul(&self, o: &P) -> P {
        let mut r = P::zero(self.nv, self.d);
        let b = self.d + 1;
        for (i, &a) in self.c.iter().enumerate() {
            if a == 0.0 {
                continue;
            }
            let ei = self.exps(i);
            for (j, &bb) in o.c.iter().enumerate() {
                if bb == 0.0 {
                    continue;
                }
                let ej = o.exps(j);
                let mut idx = 0;
                let mut m = 1;
                for k in 0..self.nv {
                    let e = ei[k] + ej[k];
                    assert!(e <= self.d, "degree overflow");
                    idx += e * m;
                    m *= b;
                }
                r.c[idx] += a * bb;
            }
        }
        r
    }
    /// Parity class of each slot: 0 = constant, 1 = all exponents even, 2 = some odd.
    pub fn classes(nv: usize, d: usize) -> Vec<u8> {
        let p = P::zero(nv, d);
        (0..p.c.len())
            .map(|i| {
                let e = p.exps(i);
                if i == 0 {
                    0
                } else if e[..nv].iter().all(|x| x % 2 == 0) {
                    1
                } else {
                    2
                }
            })
            .collect()
    }
    pub fn lower(&self) -> f64 {
        let cl = P::classes(self.nv, self.d);
        lower_with(&self.c, &cl)
    }
    pub fn upper(&self) -> f64 {
        -self.scale(-1.0).lower()
    }
}

#[inline]
pub fn lower_with(c: &[f64], cl: &[u8]) -> f64 {
    let mut s = 0.0;
    for (x, k) in c.iter().zip(cl.iter()) {
        match k {
            0 => s += x,
            1 => {
                if *x < 0.0 {
                    s += x
                }
            }
            _ => s -= x.abs(),
        }
    }
    s
}

/// A bilinear form `Σ X_m ⊗ Y_m'`, stored densely as `nx × ny`.
#[derive(Clone, Debug)]
pub struct B {
    pub nx: usize,
    pub ny: usize,
    pub c: Vec<f64>,
}

impl B {
    pub fn zero(nx: usize, ny: usize) -> B {
        B { nx, ny, c: vec![0.0; nx * ny] }
    }
    pub fn add_outer(&mut self, x: &P, y: &P, s: f64) {
        for (i, &a) in x.c.iter().enumerate() {
            if a == 0.0 {
                continue;
            }
            let row = &mut self.c[i * self.ny..(i + 1) * self.ny];
            for (r, &b) in row.iter_mut().zip(y.c.iter()) {
                *r += s * a * b;
            }
        }
    }
}

pub struct Classes {
    pub x: Vec<u8>,
    pub y: Vec<u8>,
}

impl Classes {
    /// Lower bound of `A - x ⊗ y` on the box (without materializing it).
    pub fn lower_minus_outer(&self, a: &B, x: &P, y: &P) -> f64 {
        let mut s = 0.0;
        for i in 0..a.nx {
            let xi = x.c[i];
            let cx = self.x[i];
            let row = &a.c[i * a.ny..(i + 1) * a.ny];
            for j in 0..a.ny {
                let v = row[j] - xi * y.c[j];
                let cy = self.y[j];
                let k = if cx == 0 && cy == 0 {
                    0
                } else if cx <= 1 && cy <= 1 {
                    1
                } else {
                    2
                };
                match k {
                    0 => s += v,
                    1 => {
                        if v < 0.0 {
                            s += v
                        }
                    }
                    _ => s -= v.abs(),
                }
            }
        }
        s
    }
    pub fn lower(&self, a: &B) -> f64 {
        let zx = P::zero(1, 0);
        let _ = zx;
        let mut s = 0.0;
        for i in 0..a.nx {
            let cx = self.x[i];
            for j in 0..a.ny {
                let v = a.c[i * a.ny + j];
                let cy = self.y[j];
                if cx == 0 && cy == 0 {
                    s += v
                } else if cx <= 1 && cy <= 1 {
                    if v < 0.0 {
                        s += v
                    }
                } else {
                    s -= v.abs()
                }
            }
        }
        s
    }
}
