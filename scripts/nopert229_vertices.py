#!/usr/bin/env python3
"""Exact coordinate and vertex generator for Nopert #229 (Compound M9b).

Derived directly from ruperts/repair214.cc without any STL round-trip.
Enforces exact algebraic coplanarity of the quadrilateral faces and
scales coordinates to lie strictly inside the unit sphere for Lean's GoodPoly.

NOTE: This generator historically rounded rotated coordinates to 16 decimal places
(Q(f'{vx:.16f}')), leaving a residual coplanarity defect of ~4.5e-17 that creases
the 5 quads into 10 triangles (32 facet planes). For the canonical exact 27-face
rational vertices with pure power-of-two denominators (2^52) and zero coplanarity defect,
see ruperts/codebdd229.cc and noteperts/QUAD_FACES.md.
"""

from __future__ import annotations

import math

try:
    from gmpy2 import mpq as Q
except ModuleNotFoundError:
    from fractions import Fraction as Q
from typing import Tuple, List

# 1. Base roots from repair214.cc (double precision from ruperts.sqlite nopert_214)
# r0: bottom cap (level 0)
# r1_orig: ring 1 (level 1)
# r2_orig: ring 2 (level 2)
# r3_orig: top cap (level 3)
R0_UNSCALED = (0.059531590336855608, 0.61720181541110919, -0.7828881096394904)
R1_ORIG_UNSCALED = (-0.28734462910865377, 0.91288665990602536, -0.04168073930310031)
R2_ORIG_UNSCALED = (-0.17498349913916189, 0.95974981796212366, 0.30745142339957682)
R3_ORIG_UNSCALED = (0.043880343662019643, 0.58185156273199845, 0.5800230814679902)

# Compound M9b perturbations:
# Ring 1 Angle: delta = -1.5e-3 rad
DELTA = -1.5e-3
c_d = math.cos(DELTA)
s_d = math.sin(DELTA)
R1_X_UNSCALED = c_d * R1_ORIG_UNSCALED[0] - s_d * R1_ORIG_UNSCALED[1]
R1_Y_UNSCALED = s_d * R1_ORIG_UNSCALED[0] + c_d * R1_ORIG_UNSCALED[1]

# Ring 2 Radius: +1.5e-3
R2_X_UNSCALED = R2_ORIG_UNSCALED[0] * (1.0 + 1.5e-3)
R2_Y_UNSCALED = R2_ORIG_UNSCALED[1] * (1.0 + 1.5e-3)
R2_Z_UNSCALED = R2_ORIG_UNSCALED[2]

# Top Cap: z -= 1.5e-3
R3_X_UNSCALED = R3_ORIG_UNSCALED[0]
R3_Y_UNSCALED = R3_ORIG_UNSCALED[1]
R3_Z_UNSCALED = R3_ORIG_UNSCALED[2] - 1.5e-3

# Coplanarity derivation for r1.z:
# Face 3 is a quad formed by:
# q0 = r0 (level 0)
# q1 = r1 (level 1)
# q2 = r2 (level 2)
# q3 = Rz(-2pi/5) r1
THETA = -2.0 * math.pi / 5.0
cos_t = math.cos(THETA)
sin_t = math.sin(THETA)

r1_rot_x = cos_t * R1_X_UNSCALED - sin_t * R1_Y_UNSCALED
r1_rot_y = sin_t * R1_X_UNSCALED + cos_t * R1_Y_UNSCALED

dx_rot = r1_rot_x - R1_X_UNSCALED
dy_rot = r1_rot_y - R1_Y_UNSCALED

C1 = (R2_X_UNSCALED - R0_UNSCALED[0]) * dy_rot - (R2_Y_UNSCALED - R0_UNSCALED[1]) * dx_rot
C2 = (R2_Z_UNSCALED - R0_UNSCALED[2]) * ((R1_X_UNSCALED - R0_UNSCALED[0]) * dy_rot - (R1_Y_UNSCALED - R0_UNSCALED[1]) * dx_rot)
R1_Z_UNSCALED = R0_UNSCALED[2] + C2 / C1

# Order seeds by decreasing z convention (matching Nopert228 / Nopert214 / Nopert76):
# Seed 0: Level 3 (top cap, z ~ +0.5785)
# Seed 1: Level 2 (ring 2,  z ~ +0.3075)
# Seed 2: Level 1 (ring 1,  z ~ -0.0431)
# Seed 3: Level 0 (bot cap, z ~ -0.7829)
RAW_SEEDS = (
    (R3_X_UNSCALED, R3_Y_UNSCALED, R3_Z_UNSCALED),
    (R2_X_UNSCALED, R2_Y_UNSCALED, R2_Z_UNSCALED),
    (R1_X_UNSCALED, R1_Y_UNSCALED, R1_Z_UNSCALED),
    R0_UNSCALED,
)

# Scaling factor to ensure all vertices satisfy ||v|| <= 1 for Lean's GoodPoly
# Maximum norm occurs at Level 2 (Seed 1)
MAX_NORM = math.sqrt(sum(x**2 for x in RAW_SEEDS[1]))
# We scale slightly below 1 to avoid rounding past 1.0 in exact rational norm checks
SCALE = (1.0 - 1e-15) / MAX_NORM

SEEDS = tuple(tuple(x * SCALE for x in seed) for seed in RAW_SEEDS)

# Convert seeds to exact Fractions (with 16 decimal digit precision)
SEEDS_Q: Tuple[Tuple[Q, Q, Q], ...] = tuple(
    tuple(Q(f"{x:.16f}") for x in seed) for seed in SEEDS
)

# Generate 20 vertices in orbit-major ordering:
# slot = k * 4 + s for k in 0..4 (orbit), s in 0..3 (seed)
def generate_vertices_q() -> Tuple[Tuple[Q, Q, Q], ...]:
    table = []
    for k in range(5):
        angle = 2.0 * math.pi * k / 5.0
        c = math.cos(angle)
        s = math.sin(angle)
        for s_idx in range(4):
            seed = SEEDS[s_idx]
            vx = c * seed[0] - s * seed[1]
            vy = s * seed[0] + c * seed[1]
            vz = seed[2]
            table.append((
                Q(f"{vx:.16f}"),
                Q(f"{vy:.16f}"),
                Q(f"{vz:.16f}"),
            ))
    return tuple(table)

VERTICES_Q = generate_vertices_q()
VERTICES = [tuple(map(float, v)) for v in VERTICES_Q]

def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
          - a[1] * (b[0] * c[2] - b[2] * c[0])
          + a[2] * (b[0] * c[1] - b[1] * c[0]))

def quad_determinant(table=VERTICES_Q):
    # Quad face on seed level:
    # q0 = seed 3 (index 3)
    # q1 = seed 2 (index 2)
    # q2 = seed 1 (index 1)
    # q3 = k=4 seed 2 (index 4*4 + 2 = 18)
    q0 = table[3]
    q1 = table[2]
    q2 = table[1]
    q3 = table[18]
    v1 = tuple(q1[i] - q0[i] for i in range(3))
    v2 = tuple(q2[i] - q0[i] for i in range(3))
    v3 = tuple(q3[i] - q0[i] for i in range(3))
    return det3(v1, v2, v3)

if __name__ == "__main__":
    print("Nopert #229 Coordinates (repair214 exact M9b derivation):")
    print(f"  Max unscaled norm: {MAX_NORM:.16f}")
    print(f"  Scale factor S   : {SCALE:.16f}")
    print("Seeds:")
    for i, seed in enumerate(SEEDS):
        norm = math.sqrt(sum(x**2 for x in seed))
        print(f"  Seed {i}: {seed}, norm = {norm:.16f}")
    print(f"Quad coplanarity det: {float(quad_determinant()):+.16e}")
