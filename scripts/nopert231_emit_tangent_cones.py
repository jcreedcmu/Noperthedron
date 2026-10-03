#!/usr/bin/env python3
"""Emit exact tangent-cone certificates for the Nopert #229 checker model.

For each ordered pair of distinct vertices ``(base, target)``, find at most
three incident edge directions at ``base`` whose nonnegative rational
combination is exactly ``target - base``.  We additionally require the sum
of the coefficients to be at least one; this preserves the strict support
margin used by the local certificate checker.

All discovery and validation in this script uses ``fractions.Fraction``.
The emitted Lean theorem is then checked again by exact rational reduction.
"""

from __future__ import annotations

import argparse
import itertools
from fractions import Fraction
from pathlib import Path

from nopert231_vertices import VERTICES_Q


def hull_adjacency():
    """Neighbors of each vertex along hull edges, from the exact facet planes
    of the code database (codebdd231.json, written with the vertices): two
    vertices are adjacent when they lie on two common facets. Sorted, so the
    order is reproducible."""
    import json
    path = Path(__file__).resolve().parent.parent.parent / "nopert229" / "codebdd231.json"
    if not path.exists():
        path = Path("/root/quad/nopert229/codebdd231.json")
    planes = [set(p["face_vertices"]) for p in json.load(open(path))["planes"]]
    n = len(VERTICES_Q)
    adjacency = []
    for a in range(n):
        row = [b for b in range(n) if b != a and sum(1 for f in planes if a in f and b in f) >= 2]
        adjacency.append(tuple(row))
    return tuple(adjacency)


ADJACENCY = hull_adjacency()
NUM_VERTICES = len(VERTICES_Q)
# SparseSupport.supportGenerator has rows of this width (padded with the vertex).
GENERATOR_WIDTH = 7
assert max(len(row) for row in ADJACENCY) <= GENERATOR_WIDTH

def sub(u, v):
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])


def add(u, v):
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def scale(c, v):
    return (c * v[0], c * v[1], c * v[2])


def det(columns):
    a, b, c = columns
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - b[0] * (a[1] * c[2] - a[2] * c[1])
            + c[0] * (a[1] * b[2] - a[2] * b[1]))


def solve(columns, target):
    denominator = det(columns)
    if denominator == 0:
        return None
    return tuple(det(columns[:i] + (target,) + columns[i + 1:]) /
                 denominator for i in range(3))


def complexity(indices, coefficients):
    """Prefer small emitted numerators and denominators, then sparse rows."""
    bits = [max(abs(value.numerator).bit_length(),
                value.denominator.bit_length()) for value in coefficients]
    return (max(bits), sum(bits), sum(value != 0 for value in coefficients),
            indices)


def find_combination(base, target):
    if base == target:
        return (0, 0, 0), (Fraction(0),) * 3

    neighbors = ADJACENCY[base]
    if target in neighbors:
        position = neighbors.index(target)
        return (position, position, position), (Fraction(1), Fraction(0),
                                                Fraction(0))

    directions = tuple(sub(VERTICES_Q[vertex], VERTICES_Q[base])
                       for vertex in neighbors)
    delta = sub(VERTICES_Q[target], VERTICES_Q[base])
    candidates = []
    for indices in itertools.combinations(range(len(neighbors)), 3):
        coefficients = solve(tuple(directions[i] for i in indices), delta)
        if coefficients is None or any(value < 0 for value in coefficients):
            continue
        if sum(coefficients, Fraction(0)) < 1:
            continue
        candidates.append((complexity(indices, coefficients), indices,
                           coefficients))
    if not candidates:
        raise ValueError(f"no tangent combination for ({base}, {target})")
    _, indices, coefficients = min(candidates)
    return indices, coefficients


def validate(base, target, indices, coefficients):
    if any(value < 0 for value in coefficients):
        raise AssertionError("negative tangent coefficient")
    if sum(coefficients, Fraction(0)) < 1:
        raise AssertionError("coefficient sum does not preserve margin")
    directions = tuple(sub(VERTICES_Q[ADJACENCY[base][i]], VERTICES_Q[base])
                       for i in indices)
    reconstructed = (Fraction(0), Fraction(0), Fraction(0))
    for coefficient, direction in zip(coefficients, directions):
        reconstructed = add(reconstructed, scale(coefficient, direction))
    if reconstructed != sub(VERTICES_Q[target], VERTICES_Q[base]):
        raise AssertionError("incorrect tangent reconstruction")


def lean_rat(value):
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator} / {value.denominator} : ℚ)"


def lean_combination(indices, coefficients):
    return ("{ generator := ![" + ", ".join(map(str, indices)) +
            "], coefficient := ![" +
            ", ".join(lean_rat(value) for value in coefficients) + "] }")


def emit(destination: Path):
    table = []
    max_bits = 0
    for base in range(NUM_VERTICES):
        row = []
        for target in range(NUM_VERTICES):
            indices, coefficients = find_combination(base, target)
            if base != target:
                validate(base, target, indices, coefficients)
            for value in coefficients:
                max_bits = max(max_bits, abs(value.numerator).bit_length(),
                               value.denominator.bit_length())
            row.append((indices, coefficients))
        table.append(row)

    lines = [
        "module", "",
        "public import Noperthedron.Nopert231.SparseSupport",
        "public meta import Noperthedron.Nopert231.SparseSupport", "",
        "@[expose] public section", "",
        "namespace Noperthedron.Nopert231.GeneratedTangentCones", "",
        "set_option linter.unusedTactic false",
        "set_option linter.unreachableTactic false",
        "set_option linter.unnecessarySeqFocus false",
        # `table b t` unfolds two `![…]` lookups, whose depth grows with b + t
        # (base + target >= 69 exceeds the default 512 at 60 vertices).
        "set_option maxRecDepth 8192", "",
        "open SparseSupport", "",
    ]
    for base, row in enumerate(table):
        for target, (indices, coefficients) in enumerate(row):
            lines.extend([
                f"def combination_{base}_{target} : TangentCombination :=",
                f"  {lean_combination(indices, coefficients)}", "",
            ])

    lines.extend([
        "abbrev table : VertexIndex → VertexIndex → TangentCombination := ![",
    ])
    for base, row in enumerate(table):
        suffix = "," if base + 1 < len(table) else ""
        lines.append("  ![")
        for target, _ in enumerate(row):
            entry_suffix = "," if target + 1 < len(row) else ""
            lines.append(f"    combination_{base}_{target}{entry_suffix}")
        lines.append(f"  ]{suffix}")
    lines.extend(["]", ""])

    for base in range(NUM_VERTICES):
        for target in range(NUM_VERTICES):
            if base == target:
                continue
            name = f"combination_{base}_{target}"
            lines.extend([
                f"private theorem valid_{base}_{target} :",
                f"    {name}.Valid {base} {target} := by",
                "  unfold TangentCombination.Valid",
                "  constructor",
                "  · intro l",
                f"    fin_cases l <;> simp [{name}] <;> norm_num",
                "  constructor",
                f"  · simp [{name}, Fin.sum_univ_three] <;> norm_num",
                "  constructor",
                "  · intro l hnonzero",
                f"    fin_cases l <;> simp [{name}, supportGenerator]",
                "  · funext coordinate",
                "    fin_cases coordinate <;>",
                f"      simp [{name}, supportGenerator, rationalVertex,",
                "        rationalVertices, Fin.sum_univ_three] <;> norm_num",
                "",
            ])

    # Assemble per base vertex: one fin_cases over all pairs nests
    # NUM_VERTICES^2 goals, which exceeds the recursion limit at 60 vertices.
    for base in range(NUM_VERTICES):
        lines.extend([
            f"private theorem row_valid_{base} (target : VertexIndex) (htarget : target ≠ {base}) :",
            f"    (table {base} target).Valid {base} target := by",
            "  fin_cases target",
        ])
        for target in range(NUM_VERTICES):
            if base == target:
                lines.append("  · exact (htarget rfl).elim")
            else:
                lines.append(f"  · exact valid_{base}_{target}")
        lines.append("")
    lines.extend([
        "theorem table_valid_kernel : TangentTableValid table := by",
        "  intro base target htarget",
        "  fin_cases base",
    ])
    for base in range(NUM_VERTICES):
        lines.append(f"  · exact row_valid_{base} target htarget")
    lines.extend(["",
        "end Noperthedron.Nopert231.GeneratedTangentCones", "", "end", "",
    ])
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(lines), encoding="utf-8")
    print(f"wrote {destination} ({destination.stat().st_size} bytes; "
          f"maximum rational component {max_bits} bits)")


def write_support_generator(sparse_support: Path):
    """Rewrites the body of `supportGenerator` in SparseSupport.lean: row
    `base` lists ADJACENCY[base], padded with `base` to GENERATOR_WIDTH."""
    import re
    rows = []
    for base, row in enumerate(ADJACENCY):
        padded = list(row) + [base] * (GENERATOR_WIDTH - len(row))
        rows.append("  ![" + ", ".join(map(str, padded)) + "]")
    header = f"def supportGenerator : VertexIndex → Fin {GENERATOR_WIDTH} → VertexIndex := !["
    text = sparse_support.read_text(encoding="utf-8")
    pattern = re.compile(re.escape(header) + r"\n.*?\n\]", re.S)
    text, k = pattern.subn(lambda _: header + "\n" + ",\n".join(rows) + "\n]", text, count=1)
    if k != 1:
        raise SystemExit(f"{sparse_support}: no supportGenerator definition")
    sparse_support.write_text(text, encoding="utf-8")
    print(f"updated {sparse_support} ({NUM_VERTICES} rows)")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--sparse_support", type=Path,
                        default=Path(__file__).resolve().parent.parent / "Noperthedron" /
                        "Nopert231" / "SparseSupport.lean")
    args = parser.parse_args()
    write_support_generator(args.sparse_support)
    emit(args.output)


if __name__ == "__main__":
    main()
