# Superdiffusion

A machine-checked **Lean 4** formalization of the paper

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> [*Superdiffusion and anomalous regularization in self-similar random incompressible flows*](https://arxiv.org/abs/2601.22142),
> arXiv:2601.22142v2.

All three main theorems of the paper are proved, in the form in which its
introduction states them. The development is built on
[mathlib](https://github.com/leanprover-community/mathlib4) and on two public
libraries: the
[CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining)
homogenization library of Armstrong and Kuusi, its analytic base, and the
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess) library of
continuous-time Markov processes.

[![CI](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/build.yml)
[![Comparator audit](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/comparator.yml/badge.svg)](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/comparator.yml)

## What is proved

The paper studies a diffusion in a random, self-similar, incompressible drift
whose stream matrix is a sum of independent shells over all scales. Its three
main results, formalized here as stated in the introduction, are:

- **Theorem A, superdiffusivity.** For every time `t > 0` and every moment
  `p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻⁶]`, the deviation of the quenched mean square
  displacement at time `t` from `2 d R̃(t)²` has `Lᵖ` norm over the
  disorder bounded by `C (√p + √|log γ|) √γ |log γ|⁴ R̃(t)²`, and the squared
  quenched mean displacement has `Lᵖ` norm over the disorder bounded by
  `C (p + |log γ|) γ |log γ|⁷ R̃(t)²`. Here
  `R̃(t) = ((ν t)^{2−γ} + c⋆ γ⁻¹ t²)^{1/(2(2−γ))}` is the intrinsic length
  scale. Equivalently, the raw `p`-th absolute moments are bounded by the
  respective displayed amplitudes raised to `p`. The particle spreads like
  `R̃(t)`, superdiffusively beyond the crossover time, and has a controlled quenched mean displacement.
- **Theorem B, renormalization of the generator.** At every scale `m` there
  are an effective diffusivity `σ̄_m`, within relative error `C √γ |log γ|` of
  the profile `(ν² + c⋆ γ⁻¹ 3^{2γm})^{1/2}`, and a random error `E_B` with
  `Lᵖ` norm over the disorder bounded by `C (√p + √|log γ|) √γ |log γ|³` for
  `p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻¹]`, such that almost surely the Dirichlet problem
  for the random operator on the cube `□_m` is comparable, in `L^∞` and in
  energy, to the homogenized problem with constant coefficient `σ̄_m` and the
  same data, with relative error `E_B`.
- **Theorem C, anomalous regularity.** For every Hölder exponent
  `α ∈ (0, 1 − C √γ]` there is a random minimal scale `X_m(α)` with
  exponentially decaying tails, `P[X_m(α) ≥ N] ≤ C exp(−(1 − α)² (N − C) / (C γ))`,
  such that solutions of the random Dirichlet problem on `□_m` satisfy the
  excess-decay estimate `3^{(1−α)(m−n)}` between any two scales `n ≤ m` with
  `X_m(α) ≤ m − n`, uniformly over `C^{0,1/2}` forcing and `C^{1,1/2}`
  boundary data and uniformly in the molecular diffusivity `ν`.

The three theorems are stated in full in
[`Algsuperdiff/MainTheorems.lean`](Algsuperdiff/MainTheorems.lean) as
`Algsuperdiff.superdiffusivity`, `Algsuperdiff.generator_renormalization` and
`Algsuperdiff.anomalous_regularity`; each is proved by direct application of
its verified counterpart, so the statements displayed there are exactly the
verified ones.

Sections 1 to 5 of the paper are formalized in full: every proposition and
lemma that the proofs of the three theorems use, including the
renormalization of the effective diffusivity across scales, the coarse-graining
estimates, the large-scale regularity theory, and the theory of the diffusion
process of the divergence-form generator. Two more general statements are
part of the public surface: Theorems B and C for the infrared cutoffs `a_L`
of the coefficient field, uniformly in the cutoff
(`Algsuperdiff.Frozen.Section4.generator_renormalization`,
`Algsuperdiff.Frozen.Section4.anomalous_regularity`), from which the
introduction's statements follow by letting `L → ∞`, and the quantitative
diffusivity asymptotics of Section 3
(`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`).

One construction is deliberately absent: no instance of the model structure
`ABKModel d` is built here, so the theorems are certified for every model that
satisfies the paper's assumptions; the paper's Gaussian example is such a
model, and its construction is not formalized. The paper-to-Lean
correspondence is in [`CORRESPONDENCE.md`](CORRESPONDENCE.md).

## Guarantees

- **No `sorry`** in the library. The three comparator challenges under
  `SuperdiffusionAudit/` each contain one intentional statement-level `sorry`,
  which the corresponding solution file proves.
- **No custom axiom.** The three main theorems depend only on mathlib's
  standard axioms `propext`, `Classical.choice` and `Quot.sound`.
  [`Algsuperdiff/Meta/AxiomsAudit.lean`](Algsuperdiff/Meta/AxiomsAudit.lean)
  prints their axiom dependencies, and the axiom-audit step of the CI workflow
  fails on `sorryAx` or on any other axiom.
- **Independent check of the statements.** Each main theorem is restated, with
  the model rebuilt from mathlib primitives alone, in
  [`SuperdiffusionAudit/Superdiffusivity/Challenge.lean`](SuperdiffusionAudit/Superdiffusivity/Challenge.lean),
  [`SuperdiffusionAudit/GeneratorRenormalization/Challenge.lean`](SuperdiffusionAudit/GeneratorRenormalization/Challenge.lean)
  and
  [`SuperdiffusionAudit/AnomalousRegularity/Challenge.lean`](SuperdiffusionAudit/AnomalousRegularity/Challenge.lean).
  The CI workflow submits each challenge and its solution to
  [leanprover/comparator](https://github.com/leanprover/comparator), which
  checks that the restatement is proved from the library through an
  independent implementation of the Lean kernel. See
  [`SuperdiffusionAudit/README.md`](SuperdiffusionAudit/README.md).
- **Pinned toolchain.** Lean `v4.33.0`, mathlib `v4.33.0`, and the
  `CoarseGraining` and `MarkovProcess` libraries at fixed revisions, recorded
  in [`lake-manifest.json`](lake-manifest.json).

Where a statement file under `Algsuperdiff/Frozen/` cites the paper's TeX
source (arXiv:2601.22142v2), it does so by theorem and label or by file and
line range; the TeX files themselves are not part of this repository.

## Size

About 590,000 lines of Lean in 2,136 modules, of which about 410,000 lines
are code once comments and blank lines are removed, on top of the
CoarseGraining library (about 1,600 modules, about 560,000 lines of code) and
the MarkovProcess library (about 250 modules).

## Building

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) and managed by
[elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The two library dependencies have no olean cache and are compiled from source
on the first build, as is the project itself; expect several hours. Afterwards
`import Algsuperdiff` loads the whole development and
`import Algsuperdiff.MainTheorems` the three theorems.

## Repository layout

```
Algsuperdiff/
  MainTheorems.lean   Theorems A, B and C, stated in full
  Assumptions/        the model: shells, gates, the random flow
  Probability/        concentration and independence tools
  Section24/          the coarse matrix derivative and sensitivity estimates
  Section3/           renormalization of the diffusivity (Section 3 of the paper)
  Section4/           Theorems B and C (Section 4)
  Section5/           Theorem A (Section 5)
  StochasticProcess/  the diffusion process of the divergence-form generator
  Process/            the paper's process theory over the MarkovProcess library
  Frozen/             the verified statement surface (introduction, Sections 2.4 to 5)
  Meta/               AxiomsAudit.lean, the CI axiom report
Algsuperdiff.lean     the root module, importing the whole library
SuperdiffusionAudit/  the mathlib-only restatements and their solutions
```

## How this was built

The Lean code was written mostly by Claude (Fable 5 and Opus 5), with
contributions by GPT-5.6 (Sol and Terra), under the close supervision of the
authors. Models, tooling, cost and review status are disclosed in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors, citation, acknowledgements

The Lean development is by **Scott Armstrong** and **Tuomo Kuusi**. To cite it,
use [`CITATION.cff`](CITATION.cff). The authors were supported by the European
Research Council (ERC) under the European Union's Horizon Europe research and
innovation programme, grant agreement No. 101200828.

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
