# Optimal Online Stochastic Matching

This repository provides a Lean 4 formal verification of the optimal competitive ratio for unweighted online stochastic matching with known Poisson arrival rates, as established in:

Paul Dütting, Michal Feldman, and Mathieu Molina, [*Optimal Online Stochastic Matching*](https://arxiv.org/abs/2610.19866).

The repository accompanies the paper and allows independent checking of the formal proof.

## Scope

The formalization proves both achievability and optimality of the competitive ratio

```math
1-\frac{e}{e^e}\approx 0.8206259213,
```



with respect to the expected size of a maximum matching. The main result is `StochasticMatching.optimalPoissonCompetitiveRatio_eq` in [`Matching/PoissonOptimalRatio.lean`](Matching/PoissonOptimalRatio.lean).

The scope is the Poisson arrival model.

## Checking the proof

The project pins Lean 4.19.0 and mathlib v4.19.0. With Lean installed, run the following commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The final command audits the theorem dependencies and permits only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
