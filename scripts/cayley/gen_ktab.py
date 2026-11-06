#!/usr/bin/env python3
"""Generate Cayley/Checker/KTab.lean from the vertex table `vtxI` in Cayley/Checker/KGap.lean.

Each of the 90 vertices gets a 640-bit slot; with offset B = 2^170,
  tp{x,y,z} = Σ_t (B + c_t) 2^(640 t),
  tn{x,y,z} = Σ_t (B - c_t) 2^(640 t),
  ta{x,y,z} = Σ_t (B - |c_t|) 2^(640 t),
  onesT     = Σ_t 2^(640 t).
The theorems `tpx_eq` … `onesT_eq` in Cayley/Soundness/KVtx.lean check the output against `vtxI`.

Usage (from the repo root):
  python3 scripts/cayley/gen_ktab.py           # rewrite Cayley/Checker/KTab.lean
  python3 scripts/cayley/gen_ktab.py --check   # exit 1 if the file is out of date
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
KGAP = ROOT / "Cayley/Checker/KGap.lean"
KTAB = ROOT / "Cayley/Checker/KTab.lean"

NVERTS = 90
SLOT = 640
B = 2**170

HEADER = """\
module

@[expose] public section

/-!
# Packed vertex tables for the kernel gap checker

These generated literals encode the 90 integer vertices in `vtxI`
(`Cayley/Checker/KGap.lean`); see `scripts/cayley/gen_ktab.py` for the formulas.
For vertex index `t = 0, …, 89`, slot `t` occupies bits `640*t` through
`640*t + 639`, so a table with entries `d_t` is `Σ_t d_t * 2^(640*t)`.
Vertex 0 is in the least significant slot. Write `B = 2^170` and
`(x_t, y_t, z_t) = vtxI[t]`.

There are three tables per coordinate: `tp` stores `B + coordinate`, `tn`
stores `B - coordinate`, and `ta` stores `B - |coordinate|`. The offset keeps
all entries nonnegative. The tenth table, `onesT`, contains 1 in every slot.

`quickV` in `Cayley/Checker/KPack.lean` uses arithmetic on these large naturals
to compute quick gap tests for all 90 vertices at once. It selects `tn` or `tp`
according to a coefficient's sign and uses `ta` for absolute-value error terms.
The 640-bit spacing leaves room for intermediate results; `pGapOK` checks
bounds that prevent carries between slots. Multiplying `onesT` by a constant
puts that constant in every slot, and shifting it left by 639 produces the
mask `signT` used to read each test's result bit.

`slot` extracts an entry by shifting and masking; for example,
`slot tpx t - B` recovers `x_t`. `vS` uses this to avoid indexing the vertex
list during kernel evaluation. The theorems `tpx_eq` through `onesT_eq` in
`Cayley/Soundness/KVtx.lean` verify these literals against `vtxI`.
-/

namespace Cayley.K
"""

FOOTER = """
end Cayley.K

end
"""


def read_vertices(path: Path) -> list[tuple[int, int, int]]:
    src = path.read_text()
    m = re.search(r"^def vtxI : List \(Int × Int × Int\) := \[\n(.*?)^\]", src, re.S | re.M)
    if m is None:
        sys.exit(f"could not find `def vtxI` in {path}")
    verts = [tuple(int(c) for c in t)
             for t in re.findall(r"\((-?\d+), (-?\d+), (-?\d+)\)", m.group(1))]
    if len(verts) != NVERTS:
        sys.exit(f"expected {NVERTS} vertices in vtxI, found {len(verts)}")
    return verts


def pack(entries: list[int]) -> int:
    for d in entries:
        # Entries must be nonnegative and leave the sign bit (bit 639) clear.
        assert 0 <= d < 2**(SLOT - 1), d
    return sum(d << (SLOT * t) for t, d in enumerate(entries))


def render(verts: list[tuple[int, int, int]]) -> str:
    out = [HEADER]
    for i, axis in enumerate("xyz"):
        cs = [v[i] for v in verts]
        for name, sign, entries in [
            ("p", "B + ", [B + c for c in cs]),
            ("n", "B - ", [B - c for c in cs]),
            ("a", "B - |", [B - abs(c) for c in cs]),
        ]:
            close = "|" if name == "a" else ""
            out.append(f"/-- Packed {axis}-coordinate table: slot `t` contains "
                       f"`{sign}{axis}_t{close}`, where `B = 2^170`. -/")
            out.append(f"def t{name}{axis} : Nat := {pack(entries)}")
    out.append("")
    out.append(f"/-- One in each of the {NVERTS} slots: `Σ_{{t=0}}^{{{NVERTS - 1}}} 2^(640*t)`. "
               "Used to broadcast constants")
    out.append("and to form the result-bit mask `signT = onesT <<< 639`. -/")
    out.append(f"def onesT : Nat := {pack([1] * NVERTS)}")
    return "\n".join(out) + "\n" + FOOTER


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="don't write; fail if KTab.lean differs from the generated output")
    args = ap.parse_args()

    sys.set_int_max_str_digits(0)
    text = render(read_vertices(KGAP))
    if args.check:
        if KTAB.read_text() != text:
            sys.exit(f"{KTAB.relative_to(ROOT)} is out of date; rerun scripts/cayley/gen_ktab.py")
        print(f"{KTAB.relative_to(ROOT)} is up to date")
    else:
        KTAB.write_text(text)
        print(f"wrote {KTAB.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
