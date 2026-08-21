# Superdiffusion

A machine-checked **Lean 4** formalization of the PDE theory of the paper
[*Superdiffusion and anomalous regularization in self-similar random
incompressible flows*](https://arxiv.org/abs/2601.22142) (Scott Armstrong,
Ahmed Bou-Rabee, and Tuomo Kuusi, arXiv:2601.22142).
It is built on [`mathlib`](https://github.com/leanprover-community/mathlib4)
and imports the public
[`CoarseGraining`](https://github.com/scottnarmstrong/CoarseGraining)
homogenization library — itself a 600k+-line formalization by the same
authors — as its analytic base.

[![CI](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/build.yml)
[![Comparator audit](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/comparator.yml/badge.svg)](https://github.com/scottnarmstrong/Superdiffusion/actions/workflows/comparator.yml)

## What this is

This repository gives complete formalizations of the **PDE statements** of
the paper: the renormalization of the effective diffusivity across scales,
the renormalization of the generator (quantitative homogenization of the
Dirichlet problem at every scale), and the anomalous large-scale regularity
theory for the associated elliptic equation, whose diffusivity degenerates at
small scales as the coupling constant tends to zero.

In terms of the paper's structure: **Sections 1–4 are formalized; Section 5
is not yet.**  Among the main results stated in the introduction, **Theorem B
and Theorem C are proved**; **Theorem A is not yet formalized**.  Theorem A
concerns the diffusion process itself, and it is a relatively direct
consequence of the formalized material: given Theorem B and the diffusivity
asymptotics, it follows by classical arguments about diffusion processes.
The mathematical core of the paper — the renormalization group scheme, the
coarse-graining estimates, and the anomalous regularity theory — lies in
those inputs, and that is precisely what is formalized here.  The remaining
step awaits a theory of diffusion processes in Mathlib, which does not yet
exist; no other obstruction separates the formalized material from
Theorem A.

- **No `sorry`** anywhere in the library.  (Each Mathlib-only comparator
  challenge in `Audit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.**  The public theorems reduce to `mathlib`'s three
  standard foundational axioms — `propext`, `Classical.choice`, `Quot.sound` —
  verified by
  [`Algsuperdiff/Meta/AxiomsAudit.lean`](Algsuperdiff/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.26.0`, `mathlib` `v4.26.0`, and `CoarseGraining` at a
  fixed revision.

## Main results

The headline theorems are stated in full in
[`Algsuperdiff/MainTheorems.lean`](Algsuperdiff/MainTheorems.lean), each
proved by direct application to its certified counterpart, so the statements
displayed there are byte-faithful to the verified ones.

* **`Algsuperdiff.generator_renormalization`** (Theorem B of the paper) —
  renormalization of the generator: at every scale the Dirichlet problem for
  the random operator is comparable, in `L^∞` and in energy, to the
  homogenized problem with the renormalized coefficient, with a random error
  whose `p`-th moments are bounded by `C (√p + √|log γ|) √γ |log γ|³`.
* **`Algsuperdiff.anomalous_regularity`** (Theorem C of the paper) —
  anomalous large-scale regularity: a quantitative excess-decay estimate for
  solutions of the random Dirichlet problem, down to a random minimal scale
  with stretched-exponential tails, uniformly over `C^{0,1/2}` forcing and
  `C^{1,1/2}` boundary data.
* **`Algsuperdiff.diffusivity_asymptotics`** — the two-sided asymptotics of
  the effective diffusivity, the quantitative core of the paper's Section 3:
  at every triadic scale `3^m` the renormalized diffusivity tracks the
  superdiffusive profile `(ν² + c⋆ γ⁻¹ 3^{2γm})^{1/2}`, with relative error
  `C √γ |log γ|`.

Theorem B and the diffusivity asymptotics together are the PDE inputs to
Theorem A, and they carry the paper's real content: passing from them to
Theorem A is a comparatively routine probabilistic step, not yet formalized
for the reasons above.

## Scope and faithfulness

Every PDE statement of the paper that the theorems above depend on is
formalized.  Statements are rendered at the generality at which the paper
proves them: the paper establishes its estimates for the cutoff fields
`a_L`, uniformly in the cutoff, and obtains the statements for the original
field by letting `L → ∞`; the formalized Theorems B and C are these
uniform-in-cutoff statements.  The paper-to-Lean map is
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

## Verified against a Mathlib-only statement

The full development is large — about 540k lines in this repository, on top
of the 600k+-line `CoarseGraining` library it imports.  So that the central
claims can be checked without trusting either development, Theorems B and C
are restated using **only Mathlib** — no project definitions from either
library — in
[`Audit/GeneratorRenormalization/Challenge.lean`](Audit/GeneratorRenormalization/Challenge.lean)
and
[`Audit/AnomalousRegularity/Challenge.lean`](Audit/AnomalousRegularity/Challenge.lean);
each challenge rebuilds the model (the self-similar random shell flow, its
coefficient law, the Dirichlet problems, the norms) from Mathlib primitives
and contains one intentional statement-level `sorry`, which the corresponding
`Solution.lean` fills from the library, checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator)
(see [`Audit/README.md`](Audit/README.md)).

## Building

The project uses [`elan`](https://github.com/leanprover/elan) and Lake; the
toolchain is pinned in [`lean-toolchain`](lean-toolchain).

```bash
# from the repository root
lake exe cache get   # prebuilt mathlib oleans (avoids a multi-hour mathlib build)
lake build           # compile the CoarseGraining dependency and the project
```

`lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json), which pins the exact dependency
revisions.  The `CoarseGraining` dependency is built from source on the first
build (about 4,600 jobs); the project itself is about 10,900 jobs.

To use the library, `import Algsuperdiff` pulls in the whole development; the
main results are in `import Algsuperdiff.MainTheorems`.

## Repository layout

```
Algsuperdiff/
  MainTheorems.lean   the headline theorems, stated in full
  Assumptions/        the model: shells, gates, the random flow
  Probability/        concentration, independence, Gaussian tools
  Section24/          the coarse matrix derivative and sensitivity estimates
  Section3/           the diffusivity renormalization (Section 3 of the paper)
  Section4/           Theorems B and C (Section 4 of the paper)
  Frozen/             the certified statement surface (Sections 3, 4, 2.4)
  Meta/               AxiomsAudit.lean
Algsuperdiff.lean     the root module (imports the whole library)
Audit/                Mathlib-only comparator challenges and solutions
```

## How this was built

The Lean code in this repository was written mostly by Claude (Fable 5 and
Opus 5), with some contributions by GPT-5.6 (Sol and Terra), under the
close supervision of the authors.  The models, tooling, cost, and review
status are disclosed in full in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Scott Armstrong** and **Tuomo Kuusi**.  If you
use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong and Tuomo Kuusi were supported by the European Research Council
(ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828.

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).
