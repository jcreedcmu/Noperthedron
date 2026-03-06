#!/usr/bin/env python3
"""Generate nopertListQ: 90 rational vertex approximations for Lean.

Each coordinate is floor(exact * 10^16) / 10^16, matching the Python
verification in the original Steininger-Yurkevich code.

Vertex indexing: index = k + 15*i + 45*ell
  - k in 0..14  (rotation index)
  - i in 0..2   (C1, C2, C3)
  - ell in 0..1 (sign flip)
"""
import mpmath

mpmath.mp.dps = 50  # 50 decimal places of precision

# Base vertices from Nopert.lean (exact rationals)
C1 = [mpmath.mpf(152024884) / 259375205,
      mpmath.mpf(0),
      mpmath.mpf(210152163) / 259375205]

C2 = [mpmath.mpf(6632738028) / 10**10,
      mpmath.mpf(6106948881) / 10**10,
      mpmath.mpf(3980949609) / 10**10]

C3 = [mpmath.mpf(8193990033) / 10**10,
      mpmath.mpf(5298215096) / 10**10,
      mpmath.mpf(1230614493) / 10**10]

Cs = [C1, C2, C3]


def rz(theta, v):
    """Rotation around z-axis by angle theta."""
    c, s = mpmath.cos(theta), mpmath.sin(theta)
    return [c * v[0] - s * v[1],
            s * v[0] + c * v[1],
            v[2]]


scale = mpmath.mpf(10) ** 16


def floor_approx(x):
    """floor(x * 10^16) as a Python int."""
    return int(mpmath.floor(x * scale))


# Generate all 90 vertices in the same order as nopertList
# nopertList := do
#   let ell <- List.range 2
#   let i <- [0, 1, 2]
#   let k <- List.range 15
#   pure (nopertPt k ell i)
verts = []
for ell in range(2):
    for i in range(3):
        for k in range(15):
            theta = 2 * mpmath.pi * k / 15
            v = rz(theta, Cs[i])
            sign = (-1) ** ell
            v = [sign * x for x in v]
            verts.append(v)

assert len(verts) == 90

# Print as Lean array literal using helper function v(a, b, c)
print("private def d : ℚ := 10^16")
print("")
print("private def v (a b c : ℤ) : Fin 3 → ℚ :=")
print("  fun | 0 => ↑a / d | 1 => ↑b / d | 2 => ↑c / d")
print("")
print("def nopertListQ : Array (Fin 3 → ℚ) := #[")
for idx, v in enumerate(verts):
    coords = [floor_approx(c) for c in v]
    # Decode index
    ell = idx // 45
    rem = idx % 45
    i = rem // 15
    k = rem % 15
    comment = f"-- [{idx}] ℓ={ell} i={i} k={k}"
    comma = "," if idx < 89 else ""
    line = f"  v {coords[0]:>20} {coords[1]:>20} {coords[2]:>20}{comma} {comment}"
    print(line)
print("]")

# Sanity checks
print("")
print("-- Sanity checks:")
# k=0, ell=0, i=0: should be C1 itself
v0 = verts[0]
print(f"-- Vertex 0 (C1): ({floor_approx(v0[0])}/{int(scale)}, {floor_approx(v0[1])}/{int(scale)}, {floor_approx(v0[2])}/{int(scale)})")
# Check: C1[0] = 152024884/259375205 ≈ 0.5862...
c1_0_exact = mpmath.mpf(152024884) / 259375205
print(f"-- C1[0] exact = {c1_0_exact}")
print(f"-- C1[0] approx = {floor_approx(c1_0_exact)}/10^16 = {mpmath.mpf(floor_approx(c1_0_exact)) / scale}")
print(f"-- Error = {c1_0_exact - mpmath.mpf(floor_approx(c1_0_exact)) / scale}")
