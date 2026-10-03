#!/usr/bin/env python3
"""Exact vertices of the current Nopert polyhedron (#231).

The vertices come from the generated `vertices231_exact27.json` in the
sibling nopert229 checkout (written by `codebdd231 --root_file=...` from
nopert229/nopert231_root.txt): 2^52 denominators, exactly planar quads,
strictly inside the unit sphere. Vertices 0..3 are the Lean seeds (top cap,
ring at z ~ 0.3, ring at z ~ -0.04, bottom cap); vertex 4k+s is seed s
rotated by 2*pi*k/5 (rationally approximated).
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Tuple

try:
    from gmpy2 import mpq as Q
except ModuleNotFoundError:
    from fractions import Fraction as Q


def load_exact27_vertices() -> Tuple[Tuple[Q, Q, Q], ...]:
    json_path = Path(__file__).resolve().parent.parent.parent / "nopert229" / "vertices231_exact27.json"
    if not json_path.exists():
        json_path = Path("/root/quad/nopert229/vertices231_exact27.json")
    with open(json_path) as f:
        data = json.load(f)
    return tuple((Q(item["x"]), Q(item["y"]), Q(item["z"])) for item in data["vertices"])


VERTICES_Q = load_exact27_vertices()
VERTICES = [tuple(map(float, v)) for v in VERTICES_Q]
NUM_SEEDS = len(VERTICES_Q) // 5  # vertex S k + s is seed s rotated by 2 pi k / 5
SEEDS_Q = VERTICES_Q[:NUM_SEEDS]
SEEDS = VERTICES[:NUM_SEEDS]

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
    print("Nopert #231 exact vertices (vertices231_exact27.json):")
    print("Seeds:")
    for i, seed in enumerate(SEEDS):
        norm = math.sqrt(sum(x**2 for x in seed))
        print(f"  Seed {i}: {seed}, norm = {norm:.16f}")
    print(f"Quad coplanarity det: {float(quad_determinant()):+.16e}")
