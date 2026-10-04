#!/usr/bin/env python3
"""Exact vertices of the model.

The vertices come from the generated `model_vertices.json` in the C++
pipeline directory ($MODEL_DIR; written by codebdd from the model file):
multiples of 2^-52, non-triangular faces exactly planar, strictly inside the
unit sphere. Vertex S k + s is seed s rotated by 2*pi*k/5 (rationally
approximated), S = number of seeds.
"""

from __future__ import annotations

import json
import math
import os
from pathlib import Path
from typing import Tuple

try:
    from gmpy2 import mpq as Q
except ModuleNotFoundError:
    from fractions import Fraction as Q


def model_dir() -> Path:
    """The C++ pipeline directory (codebdd's outputs and the model files):
    $MODEL_DIR, which rebuild.sh sets."""
    d = os.environ.get("MODEL_DIR")
    if not d:
        raise SystemExit("set MODEL_DIR to the C++ pipeline directory (or pass --model_dir)")
    return Path(d)


def load_model_vertices() -> Tuple[Tuple[Q, Q, Q], ...]:
    with open(model_dir() / "model_vertices.json") as f:
        data = json.load(f)
    return tuple((Q(item["x"]), Q(item["y"]), Q(item["z"])) for item in data["vertices"])


VERTICES_Q = load_model_vertices()
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
    print("Model vertices (model_vertices.json):")
    print("Seeds:")
    for i, seed in enumerate(SEEDS):
        norm = math.sqrt(sum(x**2 for x in seed))
        print(f"  Seed {i}: {seed}, norm = {norm:.16f}")
    print(f"Quad coplanarity det: {float(quad_determinant()):+.16e}")
