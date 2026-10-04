#!/usr/bin/env python3
"""Exact rational vertices of the model (Nopert #231).

The vertices come from `model_vertices.json` in the C++ pipeline directory
(written by `codebdd --root_file=nopert231_root.txt`): 2^52 denominators,
exactly planar quads, strictly inside the unit sphere. Vertices 0..3 are the
Lean seeds (top cap, ring at z ~ 0.3, ring at z ~ -0.04, bottom cap); vertex
4k+s is seed s rotated by 2*pi*k/5 (rationally approximated).

The C++ pipeline directory is given by --model_dir (scripts that import this
module pass theirs to `load_model_vertices`) or the MODEL_DIR environment
variable, which the C++ pipeline's rebuild.sh sets.
"""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
from typing import Optional, Tuple

try:
    from gmpy2 import mpq as Q
except ModuleNotFoundError:
    from fractions import Fraction as Q


def model_dir(flag: Optional[Path] = None) -> Path:
    """The C++ pipeline directory: the --model_dir flag if given, else $MODEL_DIR."""
    if flag is not None:
        return flag
    d = os.environ.get("MODEL_DIR")
    if not d:
        raise SystemExit("pass --model_dir or set MODEL_DIR to the C++ pipeline directory")
    return Path(d)


def add_model_dir_argument(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--model_dir", type=Path, default=None,
                        help="the C++ pipeline directory (default: $MODEL_DIR)")


def load_model_vertices(directory: Optional[Path] = None) -> Tuple[Tuple[Q, Q, Q], ...]:
    with open(model_dir(directory) / "model_vertices.json") as f:
        data = json.load(f)
    return tuple((Q(item["x"]), Q(item["y"]), Q(item["z"])) for item in data["vertices"])


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
          - a[1] * (b[0] * c[2] - b[2] * c[0])
          + a[2] * (b[0] * c[1] - b[1] * c[0]))

def quad_determinant(table):
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
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    add_model_dir_argument(parser)
    args = parser.parse_args()
    vertices_q = load_model_vertices(args.model_dir)
    seeds = [tuple(map(float, v)) for v in vertices_q[:4]]
    print("Exact model vertices (model_vertices.json):")
    print("Seeds:")
    for i, seed in enumerate(seeds):
        norm = math.sqrt(sum(x**2 for x in seed))
        print(f"  Seed {i}: {seed}, norm = {norm:.16f}")
    print(f"Quad coplanarity det: {float(quad_determinant(vertices_q)):+.16e}")
