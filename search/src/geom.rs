//! Noperthedron geometry in Cayley / stereographic coordinates (floating point).

use std::f64::consts::PI;

pub type V3 = [f64; 3];
pub type M3 = [[f64; 3]; 3];

pub fn vertices() -> Vec<V3> {
    let c1 = [152024884.0 / 259375205.0, 0.0, 210152163.0 / 259375205.0];
    let c2 = [0.6632738028, 0.6106948881, 0.3980949609];
    let c3 = [0.8193990033, 0.5298215096, 0.1230614493];
    let cs = [c1, c2, c3];
    let mut out = vec![];
    // index order: k (15) × ℓ (2) × i (3), matching VertexIndex lexicographically
    for k in 0..15 {
        let th = 2.0 * PI * k as f64 / 15.0;
        let (s, c) = th.sin_cos();
        for l in 0..2 {
            let sg = if l == 0 { 1.0 } else { -1.0 };
            for p in cs.iter() {
                out.push([
                    sg * (c * p[0] - s * p[1]),
                    sg * (s * p[0] + c * p[1]),
                    sg * p[2],
                ]);
            }
        }
    }
    out
}

pub fn rz(th: f64) -> M3 {
    let (s, c) = th.sin_cos();
    [[c, -s, 0.0], [s, c, 0.0], [0.0, 0.0, 1.0]]
}

pub fn group() -> Vec<M3> {
    (0..15).map(|k| rz(2.0 * PI * k as f64 / 15.0)).collect()
}

/// Cayley numerator (same convention as `cayleyNumeratorMatrix`).
pub fn cay_num(x: f64, y: f64, z: f64) -> M3 {
    [
        [1.0 + x * x - y * y - z * z, 2.0 * (x * y - z), 2.0 * (x * z + y)],
        [2.0 * (x * y + z), 1.0 - x * x + y * y - z * z, 2.0 * (y * z - x)],
        [2.0 * (x * z - y), 2.0 * (y * z + x), 1.0 - x * x - y * y + z * z],
    ]
}

pub fn cay(x: f64, y: f64, z: f64) -> M3 {
    let d = 1.0 + x * x + y * y + z * z;
    let n = cay_num(x, y, z);
    let mut m = [[0.0; 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            m[i][j] = n[i][j] / d;
        }
    }
    m
}

pub fn mm(a: &M3, b: &M3) -> M3 {
    let mut m = [[0.0; 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            for k in 0..3 {
                m[i][j] += a[i][k] * b[k][j];
            }
        }
    }
    m
}

pub fn mv(a: &M3, v: &V3) -> V3 {
    let mut r = [0.0; 3];
    for i in 0..3 {
        for k in 0..3 {
            r[i] += a[i][k] * v[k];
        }
    }
    r
}

/// The half-turn symmetry of the C3 orbit: minus the reflection in the
/// vertical plane through C3.
pub fn tau() -> M3 {
    let (x, y) = (0.8193990033f64, 0.5298215096f64);
    let n = x * x + y * y;
    let c2 = (x * x - y * y) / n;
    let s2 = 2.0 * x * y / n;
    [[-c2, -s2, 0.0], [-s2, c2, 0.0], [0.0, 0.0, -1.0]]
}

pub fn chart(j: usize) -> M3 {
    if j == 4 {
        return tau();
    }
    let d = match j {
        0 => [1.0, 1.0, 1.0],
        1 => [1.0, -1.0, -1.0],
        2 => [-1.0, 1.0, -1.0],
        3 => [-1.0, -1.0, 1.0],
        _ => [1.0, 1.0, 1.0],
    };
    [[d[0], 0.0, 0.0], [0.0, d[1], 0.0], [0.0, 0.0, d[2]]]
}

/// Outer rotation for stereographic view coordinates `(u, v)`.
pub fn outer(u: f64, v: f64) -> M3 {
    cay(v, -u, 0.0)
}

pub fn trace(a: &M3) -> f64 {
    a[0][0] + a[1][1] + a[2][2]
}

/// Convex hull (counterclockwise), returning indices.
pub fn hull(pts: &[[f64; 2]]) -> Vec<usize> {
    let mut idx: Vec<usize> = (0..pts.len()).collect();
    idx.sort_by(|&a, &b| {
        pts[a][0]
            .partial_cmp(&pts[b][0])
            .unwrap()
            .then(pts[a][1].partial_cmp(&pts[b][1]).unwrap())
    });
    let cross = |o: [f64; 2], a: [f64; 2], b: [f64; 2]| {
        (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    };
    let mut lower: Vec<usize> = vec![];
    for &i in idx.iter() {
        while lower.len() >= 2
            && cross(pts[lower[lower.len() - 2]], pts[lower[lower.len() - 1]], pts[i]) <= 0.0
        {
            lower.pop();
        }
        lower.push(i);
    }
    let mut upper: Vec<usize> = vec![];
    for &i in idx.iter().rev() {
        while upper.len() >= 2
            && cross(pts[upper[upper.len() - 2]], pts[upper[upper.len() - 1]], pts[i]) <= 0.0
        {
            upper.pop();
        }
        upper.push(i);
    }
    lower.pop();
    upper.pop();
    lower.extend(upper);
    lower
}

pub fn transpose(a: &M3) -> M3 {
    let mut m = [[0.0; 3]; 3];
    for i in 0..3 { for j in 0..3 { m[i][j] = a[j][i]; } }
    m
}
