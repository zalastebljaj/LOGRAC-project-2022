# Formal Power Series

In this repository we are using Agda to formalize [formal power series](https://en.wikipedia.org/wiki/Formal_power_series) and formal differentiation over arbitrary commutative rings.

## Structure of this repository

This repository is set up as an Agda library and it contains:

* `lograc-project.agda-lib`: the library configuration file which contains the list of file system paths that Agda should include

* `agda-stdlib/`: Agda standard library as a git submodule

* `project/`: the top-level source code directory for our Agda code

  * `project/PowerSeries.agda` contains implementation of formal power series and operations on them, together with proofs of their properties.

## Contents

This project defines the `PowerSeries` module parameterized by a `CommutativeRing` structure (from the `Algebra` package). It implements the following:

* `FPS`: the type of formal power series

* `_≈_`, `_+_`, `-_`, `_*ₛ_`, `_*_`: basic operations on `FPS` (equivalence, addition, negation, scalar multiplication, multiplication)

* `deriv`: the formal differentiation operator

* proof that these operations form an `F`-algebra over the given commutative ring `F`

* proof that `deriv` is a [derivation](https://en.wikipedia.org/wiki/Derivation_(differential_algebra)) (i.e. is linear and satisfies the Leibniz rule)
