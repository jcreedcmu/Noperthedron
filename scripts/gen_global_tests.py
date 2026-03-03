#!/usr/bin/env python3
"""Generate Lean smoke tests for global rows from solution_tree_300.csv."""
import csv
import sys

CSV_PATH = "data/solution_tree_300.csv"
MAX_ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 30

rows = []
with open(CSV_PATH) as f:
    reader = csv.DictReader(f)
    for r in reader:
        if r["nodeType"] == "1":
            rows.append(r)
        if len(rows) >= MAX_ROWS:
            break

def intfield(r, k):
    v = r.get(k, "")
    return int(v) if v else 0

print(f"-- Auto-generated from {CSV_PATH} ({len(rows)} global rows)")
print(f"-- To regenerate: python3 scripts/gen_global_tests.py {MAX_ROWS}")
print()

for i, r in enumerate(rows):
    rid = r["ID"]
    print(f"private def testRow{rid} : Row := {{")
    print(f"  ID := {rid}, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,")
    t1min = intfield(r, "T1_min")
    t1max = intfield(r, "T1_max")
    v1min = intfield(r, "V1_min")
    v1max = intfield(r, "V1_max")
    t2min = intfield(r, "T2_min")
    t2max = intfield(r, "T2_max")
    v2min = intfield(r, "V2_min")
    v2max = intfield(r, "V2_max")
    amin  = intfield(r, "A_min")
    amax  = intfield(r, "A_max")
    print(f"  interval := {{ min := fun | .θ₁ => {t1min} | .φ₁ => {v1min} | .θ₂ => {t2min}")
    print(f"                            | .φ₂ => {v2min} | .α => {amin},")
    print(f"                max := fun | .θ₁ => {t1max} | .φ₁ => {v1max} | .θ₂ => {t2max}")
    print(f"                            | .φ₂ => {v2max} | .α => {amax} }},")
    sidx = intfield(r, "S_index")
    wx = intfield(r, "wx_nominator")
    wy = intfield(r, "wy_nominator")
    wd = intfield(r, "w_denominator")
    print(f"  S_index := ⟨{sidx}, by omega⟩,")
    print(f"  wx_numerator := {wx}, wy_numerator := {wy},")
    print(f"  w_denominator := {wd},")
    print(f"  P1_index := 0, P2_index := 0, P3_index := 0,")
    print(f"  Q1_index := 0, Q2_index := 0, Q3_index := 0,")
    print(f"  r := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩")
    print(f"}}")
    print()

ids = [r["ID"] for r in rows]
print(f"private def globalTestRows : Array Row := #[")
for i, rid in enumerate(ids):
    comma = "," if i < len(ids) - 1 else ""
    print(f"  testRow{rid}{comma}")
print("]")
print()
print(f"/-- info: All {len(rows)} global rows pass -/")
print("#guard_msgs in")
print("#eval do")
print("  let mut failures : Array Nat := #[]")
print("  for row in globalTestRows do")
print("    unless checkGlobal row do")
print("      failures := failures.push row.ID")
print(f'  if failures.isEmpty then IO.println "All {len(rows)} global rows pass"')
print(f'  else IO.println s!"FAILED rows: {{failures}}"')
