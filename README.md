# Lean Formalization Portfolio

[![Lean build and axiom audit](https://github.com/xiao-zong/lean-formalization-portfolio/actions/workflows/lean.yml/badge.svg)](https://github.com/xiao-zong/lean-formalization-portfolio/actions/workflows/lean.yml)

A collection of Lean 4 formalizations in finite network theory, exact probability bounds, and entropy projection. The emphasis is reusable mathematical definitions, explicit assumptions, boundary cases, and reproducible proof checking.

Maintained by **Qingwei Liu**. AI tools were used during proof development and repository preparation. The mathematical claims are represented by Lean declarations and checked against the pinned Lean/mathlib environment.

## At a glance

| Development | Main entry point | What is proved |
| --- | --- | --- |
| Kron reduction | [`Kron/Reduction.lean`](Kron/Reduction.lean) | Harmonic extension, energy minimization, boundary response, and composition of network reduction |
| Exact probability certificates | [`Sharp/Certificate.lean`](Sharp/Certificate.lean) | Soundness and completeness of rational certificates for finite conditional-probability bounds |
| Entropy projection and matrix scaling | [`IPF/Projection.lean`](IPF/Projection.lean) | KL projection, boundary-safe IPF convergence, sharp projective contraction, and quantitative stopping bounds |

The repository contains **28 main results** selected for the axiom audit, together with their supporting definitions and lemmas. The two single-file developments retain their original checked organization; the IPF development is split into focused modules.

## Build and inspect

Prerequisites: Git and [elan](https://github.com/leanprover/elan), the Lean toolchain manager. VS Code with the [Lean 4 extension](https://github.com/leanprover/vscode-lean4) is useful for interactive proof inspection.

```bash
git clone https://github.com/xiao-zong/lean-formalization-portfolio.git
cd lean-formalization-portfolio
lake exe cache get
lake build
lake env lean Examples.lean
lake env lean Verification.lean
```

`lean-toolchain` selects **Lean 4.35.0**. `lake-manifest.json` pins mathlib and its transitive Git dependencies; the mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`.

For a smaller build, select an entry module:

```bash
lake build Kron.Reduction
lake build Sharp.Certificate
lake build IPF.Projection
```

On a memory-constrained machine, set `LEAN_NUM_THREADS=1` before invoking Lake. CI uses this setting. Existing deprecation and style warnings do not affect proof acceptance.

## 1. Kron reduction of finite weighted networks

A conductance network has symmetric nonnegative real edge weights and a zero diagonal. Connectivity refers to its strictly positive support. The Laplacian is the diagonal matrix of row sums minus the conductance matrix.

The formalization develops an exact boundary-equivalent reduction and proves that elimination in stages agrees with direct elimination.

Representative declarations:

- `Kron.laplacian_energy`: the Laplacian quadratic form equals the weighted edge-energy sum.
- `Kron.dirichlet_posDef`: connectivity and a nonempty retained boundary imply positive definiteness of the interior block.
- `Kron.harmonic_extension_unique`: the harmonic extension is unique.
- `Kron.harmonic_energy_min` and `Kron.harmonic_energy_eq_iff`: the extension uniquely minimizes energy.
- `Kron.response_kernel`: the response kernel consists of constant boundary potentials.
- `Kron.reducedNetwork_exists`: the response is the Laplacian of a connected reduced conductance network.
- `Kron.network_response_composition`: staged and direct reductions agree under the specified reindexing.

The proofs permit a singular full Laplacian, zero conductances, singleton boundaries, and empty eliminated vertex types. The connected-network reduction requires a nonempty boundary.

## 2. Exact conditional-probability certificates

This development studies arbitrary finite state spaces with rational linear moment constraints. A joint law may have real probabilities. Conditional quantities are ratios of expectations, with strictly positive conditioning mass when the ratio is used.

The two main interfaces are:

- `Sharp.certificate_soundness`: feasible witnesses and exact dual certificates imply their asserted bounds, infeasibility, or null conditioning.
- `Sharp.certificate_completeness`: the required rational witnesses and certificates exist for every instance covered by the definitions.

Supporting results establish rational/real feasibility equivalence, rational Farkas certificates, attainment of rational linear optima, exact conditional extrema, and rational sparsification. The complete classification covers infeasible models, necessarily null conditioning, and sharp lower/upper endpoints. Endpoint laws have support size at most the number of moment constraints plus three.

Degenerate feasible faces and zero-conditioning laws are included. Full-rank assumptions, strict feasibility, and a uniform positive lower bound on conditioning mass are unnecessary. The endpoint classification assumes the supplied finite rational model with pointwise `0 ≤ N ≤ D`.

This library formalizes existence and correctness of certificates. An executable optimizer or JSON certificate interface is outside this repository's scope.

## 3. Entropy projection and iterative proportional fitting

A finite nonnegative seed table is adjusted to prescribed probability margins. Feasibility requires a coupling supported on the seed; strict positivity is unnecessary in the boundary theory.

The development includes:

- A unique KL-minimizing coupling, an exact support characterization, and the Pythagorean equality.
- Convergence of the whole row-then-column IPF sequence, including structural zeros, zero margins, and entries forced to disappear at the limit.
- The least global Hilbert projective contraction coefficient for each strictly positive rectangular matrix.
- A contraction bound for the nonlinear scaling cycle and an explicit L1 stopping certificate for strictly positive seeds and margins.
- An exact triangular example with polynomial convergence, showing why geometric rates and finite positive diagonal factors cannot be assumed throughout the boundary regime.

Start with `IPF.exists_unique_projection`, `IPF.iterates_converge`, `IPF.projective_contraction_optimal`, and `IPF.certified_stopping_bound`.

For a positive matrix with maximal cross ratio `R`, the least linear projective coefficient is `(sqrt R - 1) / (sqrt R + 1)`. A complete scaling cycle has the proved squared-coefficient upper bound; least-constant optimality is asserted for the linear matrix action.

For the triangular seed `[[1, 1], [0, 1]]` with equal margins, the upper-right entry is `1 / (4n + 2)` after `n ≥ 1` complete cycles. The boundary theorems prove its polynomial asymptotic and the failure of a global geometric upper bound.

## Proof integrity and CI

`lake build` checks the proof terms through Lean's standard kernel. [`Verification.lean`](Verification.lean) additionally examines the **transitive axiom dependencies** of all 28 selected results and fails on any axiom outside:

```text
propext
Classical.choice
Quot.sound
```

The source developments contain no `sorry` or `admit` placeholders. These formalizations use exact rational and real mathematics. Their scope and assumptions are those of the linked Lean declarations.

The [GitHub Actions workflow](.github/workflows/lean.yml) builds all three libraries, separately checks them with `leanchecker`, checks the examples, and runs the axiom audit. Action revisions, the Lean toolchain, and mathematical dependencies are pinned.

## Development focus

The collection demonstrates organizing mathematical specifications into Lean APIs, combining linear algebra with real analysis, handling degenerate cases, integrating longer proof developments, and validating the result with reproducible builds and explicit axiom audits.

[`Examples.lean`](Examples.lean) shows imports and small uses of the public interfaces. The Lean files provide the complete arguments behind the statements summarized here.
