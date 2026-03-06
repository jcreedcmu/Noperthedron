# Solution table certificate formats (draft)

This document sketches the data-only formats for external certificate generators.
Lean-side proof terms are *not* serialized; the intended workflow is to import
this data, then construct proofs in Lean that the data satisfies the relevant
inequalities.

Rational values use the JSON object form:

```
{"num": <int>, "den": <int>}
```

with `den > 0` and interpreted as `num/den`.

## Local precheck row certificates

A local precheck certificate is an array indexed by row ID (length = table size).
Each entry provides the numeric data that underlies the inequality proofs in
`RationalLocalCheck.lean` (see `BoundRℚCert`, `BoundDeltaℚCert`, `AεℚCert`,
`κSpanningCert`, `BεℚCert`).

```
{
  "rows": [
    {
      "bound_r": { "lower": [rat, rat, rat] },
      "bound_delta": { "upper": [rat, rat, rat] },
      "ae1": { "sigma": int, "bounds": [rat, rat, rat] },
      "ae2": { "sigma": int, "bounds": [rat, rat, rat] },
      "span1": { "bounds": [rat, rat, rat] },
      "span2": { "bounds": [rat, rat, rat] },
      "be": { "bounds": [rat, rat, rat] }
    },
    ...
  ]
}
```

Notes:
- The `rows` list is aligned to `row.ID`; entry `rows[i]` is intended for the
  row with `ID = i`.
- The current Lean bridge `LocalPrecheckRowCerts.toCertificate` uses `true`
  for all boolean flags, so a separate `*_ok` array is unnecessary if you
  supply row certificates.

## Global precheck row certificates (draft witness format)

Global certificates currently require a choice of `S` (a vertex of
`Nopert.poly.vertices`) together with an `exceeds` inequality proof. A draft
data shape is:

```
{
  "rows": [
    {
      "S": [rat, rat, rat],
      "exceeds": { "g_lower": rat, "h_upper": rat }
    },
    ...
  ]
}
```

The intended meaning is that `g_lower <= Gℚ` and `maxHℚ <= h_upper`, and then a
Lean proof shows `g_lower > h_upper`. This is a placeholder until we formalize
the comparison lemmas needed to discharge those bounds.
In Lean, this corresponds to `GlobalExceedsWitness` in
`Noperthedron/SolutionTable/RationalGlobalCheck.lean`, with the inequality
packaged by `exceeds_of_bounds`.
For concrete values, `GlobalExceedsRealData.ofRow` computes the real
`Gℚ`/`maxHℚ` pair; external code can then choose rational bounds around those.
`ratLower`/`ratUpper` provide one standard floor/ceil discretization in Lean,
parameterized by a denominator `n`.

See `docs/solution_table_certificates.example.json` for a concrete example.

## Computable precheck data arrays

For fast `native_decide`-style checking, the Lean side exposes Bool-only
prechecks that use arrays of booleans. These correspond to
`LocalPrecheckCertificateData` and `GlobalPrecheckCertificateData`.

Lean usage example:

```lean
def ok := Solution.solutionTablePrecheckBool tab data
```

Local:

```
{
  "bound_r_ok": [bool, ...],
  "bound_delta_ok": [bool, ...],
  "ae1_ok": [bool, ...],
  "ae2_ok": [bool, ...],
  "span1_ok": [bool, ...],
  "span2_ok": [bool, ...],
  "be_ok": [bool, ...]
}
```

Global:

```
{
  "S": [[rat, rat, rat], ...],
  "exceeds_ok": [bool, ...]
}
```

Lean loader stub:

```lean
def parsed := Solution.parsePrecheckData json
```

End-to-end example:

```
lake env lean --run scripts/precheck_example.lean docs/solution_table_certificates.example.json
```

The combined JSON also includes a `congruence_ok` array for local rows; the CLI
uses it to gate local rows in the Bool precheck.
