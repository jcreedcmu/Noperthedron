# Noperthedron

The goal of this project is to formalize the main result of
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich (cited as `[SY25]` herein).

That is, we aim to write a Lean 4 proof that the Noperthedron does not "fit through itself".

<p align="center">
<img src="./home_page/assets/noperthedron.png" width="200" alt="noperthedron">
</p>

An important piece of the proof will involve constructing a large tree object and verifying that it has certain properties.
The original authors [performed their version of this computation using Sagemath](https://github.com/Jakob256/Rupert).
We plan to perform the computation in Lean, first as a compiled program that emits a value of a carefully crafted type,
and maybe later (as a stretch goal!) in the Lean kernel itself, avoiding the need to trust the compiler.

However, our first goal is to formalize the *rest* of the math in the paper.

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
