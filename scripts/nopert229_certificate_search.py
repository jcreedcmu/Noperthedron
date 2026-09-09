#!/usr/bin/env python3
"""Certificate search for Tom 7's Nopert #229.

Thin wrapper over ``nopert214_certificate_search``: the search, atlas, and
exact-checker machinery there reads the vertex tables through module
globals, so retargeting it to another 4-seed fivefold solid only requires
installing the new tables in the same orbit-major layout
(``VERTICES_Q[k*4+j] ~= Rz(2*pi*k/5) . seed_j``).

Unlike #214 which reads rounded decimals from an STL file, the
vertices here are computed directly from the exact repair214 root
construction to ensure the quadrilateral faces remain exactly planar.
"""
from __future__ import annotations

import math
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

if os.environ.get("NOPERT_GMPY2"):
    from gmpy2 import mpq as Q  # noqa: F811 (see nopert214_certificate_search)

sys.path.insert(0, str(Path(__file__).resolve().parent))
import nopert214_certificate_search as base
import snub_certificate_search as exact_certificate
from nopert229_vertices import SEEDS_Q, VERTICES_Q

# Install the #229 tables into the shared machinery.
base.SEEDS_Q = SEEDS_Q
base.VERTICES_Q = VERTICES_Q
base.VERTICES = [tuple(map(float, vertex)) for vertex in VERTICES_Q]
exact_certificate.VERTICES_Q = [list(vertex) for vertex in VERTICES_Q]

base.PROJECTIVE_LOCAL_VERTEX_ERROR = Q(2, 10**15)
base.PROJECTIVE_SUPPORT_ERROR = 10 * base.PROJECTIVE_LOCAL_VERTEX_ERROR


def main():
    base.main()


if __name__ == "__main__":
    main()
