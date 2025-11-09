# NegativeRupert

The purpose of this repository is to sketch out the Lean proof steps
that would be required to complete a proof that the Noperthedron does
not have the Rupert property.

The citation `[SY25]` in the body of the Lean code refers to
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich.

## Blueprint

Install [leanblueprint](https://github.com/PatrickMassot/leanblueprint) with something like
```
pip install leanblueprint
```
Build all HTML and PDF content and check correspondence of blueprint decls (i.e. uses of `\lean`) with
actual lean identifiers by doing
```
leanblueprint all
```
To run a server hosting the html, run
```
leanblueprint serve
```
