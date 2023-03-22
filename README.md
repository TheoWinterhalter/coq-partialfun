# PartialFun — A simple Coq library for composable partial functions

This library lets you write dependent partial functions in monadic style to be
able to prove things about all terminating outputs, including proving which
inputs are terminating, but also execute them and extract them.

The development is found in the `theories` folder.
`PartialFun.v` contains the definition of the library while `Examples.v`
contains some examples (integer division and untyped λ-calculus for now).

This is very early-stage for now but it should work with Coq 8.16 and the
corresponding Equations version.