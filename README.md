# NegativeRupert

The goal of this project is to formalize the main result of
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich (cited as `[SY25]` herein).

That is, we aim to write a Lean 4 proof that the Noperthedron does not "fit through itself".

<img src="./home_page/assets/noperthedron.png" width="200" alt="noperthedron">

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
