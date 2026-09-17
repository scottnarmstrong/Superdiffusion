# SuperdiffusionAudit Comparator Surface

This directory contains Mathlib-only comparator challenges for the three main
theorems of the formalization of *Superdiffusion and anomalous regularization in
self-similar random incompressible flows* (Armstrong–Bou-Rabee–Kuusi): Theorem A (quenched
superdiffusivity), Theorem B (renormalization of the generator) and Theorem C
(anomalous large-scale regularity).  Each comparator lives in its own
subdirectory:

| Directory | Checked theorem |
| --- | --- |
| `Superdiffusivity/` | `Algsuperdiff.StatementAudit.Superdiffusivity.superdiffusivity` |
| `GeneratorRenormalization/` | `Algsuperdiff.StatementAudit.GeneratorRenormalization.generator_renormalization` |
| `AnomalousRegularity/` | `Algsuperdiff.StatementAudit.AnomalousRegularity.anomalous_regularity` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem — the antisymmetric `C²` shell-field
carrier and its compact-open Borel structure, the exact shell transformations
(translation, triadic scaling, negation, signed-permutation conjugation), the
regular-coefficient-field carrier with its joint pointwise/entry-test
σ-algebra, the (J2) weighted cube observable, the stationary
potential-corrector Hilbert machinery behind the (J4) constant `cstar`, the
flat standing model, the lower-infinite scale cutoff and its sample carrier,
the full stream field `k(x) = ∑_{n ∈ ℤ} (j_n(x) - j_n(0))` with the
full-tail carrier on which it converges, and the weak-`H¹`
Dirichlet-problem vocabulary on triadic cubes — states the theorem, and ends
with one `sorry`, the proof being checked.

## What Is Checked

All three theorems quantify over the full standing model: a probability law on
bi-infinite sequences of `C²` antisymmetric shell fields with independent
shells, exact triadic marginal scaling, (J1) mean-zero / stationarity /
`√d`-range of dependence, (J2) strict Gaussian tails for the weighted `C²`
cube norms, (J3) hyperoctahedral and negation invariance, and (J4) the
stationary potential-corrector non-degeneracy, whose corrector energy is
`cstar · log 3` in every unit direction.  The random environment is the
coefficient field of the introduction: the whole stream coefficient
`a = ν·Id + k` with `k(x) = ∑_{n ∈ ℤ} (j_n(x) - j_n(0))`, read on the
full-tail carrier `FullSample` on which both tails of the scale decomposition
converge.  No infrared cutoff enters the checked statements; the forms with a
cutoff `L ≥ m`, uniform in `L`, stay part of the public surface as
`Algsuperdiff.Frozen.Section4.generator_renormalization` and
`Algsuperdiff.Frozen.Section4.anomalous_regularity`.

- **`Superdiffusivity`** (Theorem A): for `gamma ≤ gamma0`, every time
  `t > 0` and every moment `p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻⁶]`, every sample carries
  a diffusion of its stream field, and every such diffusion started at the
  origin has quenched mean square displacement at time `t` within
  `C (√p + √|log γ|) √γ |log γ|⁴ R(t)²` of `2 d R(t)²`, and quenched mean
  displacement of squared size at most `C (p + |log γ|) γ |log γ|⁷ R(t)²`,
  both as `Lᵖ`-norm bounds over the disorder (the raw `p`-th moments
  are bounded by the displayed amplitudes raised to `p`); `R(t)` is the
  intrinsic length scale.  The process is not constructed in the challenge but characterized:
  a family of laws on continuous paths in `ℝ^d`, one per starting point, is
  *the* diffusion of a coefficient field when each law is a probability law
  starting where it is told and the Laplace transform in time of its one-point
  marginals is the minimal resolvent of `∇·a∇` — the increasing limit, along
  the cubic exhaustion, of the zero-trace Dirichlet resolvents. The
  characterization explicitly requires such a resolvent family to exist for
  every positive Laplace parameter and every admissible test function. It also
  requires a measurable family of path laws, the Markov restart identity
  conditional on every past event, and strongly continuous Feller transition
  operators. These clauses constrain the full temporal law.
- **`GeneratorRenormalization`** (Theorem B): for `gamma ≤ gamma0` and every
  scale `m` there are a scalar `sigmaBarM > 0` tracking the superdiffusive
  profile `sqrt (ν² + cstar·γ⁻¹·3^{2γm})` up to relative error
  `C √γ |log γ|`, and a random error amplitude `EB ≥ 0` with a
  Gaussian-type moment bound, such that almost surely the solution of the
  random Dirichlet problem on the origin cube of side `3^m` and the solution
  of the homogenized problem `sigmaBarM·Id` with the same data differ
  uniformly by at most `EB` times the natural `C^{0,1/2}` data norms, and
  their Dirichlet energies agree to the corresponding square.
- **`AnomalousRegularity`** (Theorem C): for `gamma ≤ gamma0`, every Hölder
  exponent `0 < alpha ≤ 1 - C√γ`, and every scale `m` there are a scalar
  `sigmaBarM` with the same profile display and a random minimal depth `X`
  with an exponential tail, such that almost surely, above depth `X`, every
  Dirichlet solution with `C^{0,1/2}` force and `C^{1,1/2}` boundary datum
  satisfies the `C^{0,alpha}` excess-decay estimate `3^{(1-alpha)(m-n)}`
  between the cube and any centered window of scale `n ≤ m`.

Where the repository statement names a canonical constructed object — the
(J4) constant `Disorder.cstar M` and, in Theorem C, the running diffusivity
`Annealed.sigmaBar M m`, both selected by unique choice from proved
characterizations — the challenge quantifies a scalar existentially together
with its characterizing display (the corrector energy identity for `cstar`;
Theorem B's profile band for `sigmaBar`).  Every such presentation delta is
enumerated in the module docstring of the corresponding `Challenge.lean`
("Presentation deltas"), and the bridge obligations for the solutions are
inventoried in [`DESIGN.md`](DESIGN.md).

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorem surfaces.

| Challenge declaration | Repository source |
| --- | --- |
| `Vec`, `Mat`, vector/matrix operations, `vecNorm`, `matrixOperatorNorm`, `IsSignedPermutationMatrix` | CoarseGraining modules `Homogenization.Ambient.Basic`, `Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm`, `Homogenization.Geometry.SignedPermutation` |
| `TriadicCube`, `openCubeSet`, `originCube` | CoarseGraining module `Homogenization.Geometry.TriadicCube` |
| `ShellField`, its topology/Borel structure and coordinate API | `Algsuperdiff/Frozen/Assumptions/ShellField.lean`, `Algsuperdiff/Frozen/Assumptions/ShellFieldCompactOpenTopology.lean`, `Algsuperdiff/Frozen/Assumptions/ShellFieldBorelMeasurableSpace.lean`, `Algsuperdiff/Assumptions/ShellField/Basic.lean` |
| shell transformations and their measurability | `Algsuperdiff/Assumptions/ShellField/Actions.lean` |
| `ShellSeq`, marginal laws, sequence transformations | `Algsuperdiff/Assumptions/ShellField/SequenceLaw.lean` |
| `RegCoeffField`, probes, `entryTestR`, the carrier σ-algebras, `translateReg` | CoarseGraining modules `Homogenization.Probability.RegCoeffField`, `Homogenization.Probability.RegCoeffField.Sigma`, `Homogenization.Probability.RegCoeffField.Endomorphisms` |
| `lihLocalSigma`, `forgetShell` | `Algsuperdiff/Assumptions/ShellField/LIHLocalSigma.lean`, `Algsuperdiff/Assumptions/ShellField/Basic.lean` |
| the (J2) observable `j2Observable` and its cube norms | `Algsuperdiff/Assumptions/ShellField/J2Observable.lean` |
| the stationary potential corrector and `RealizesCstar` | `Algsuperdiff/Probability/StationaryProjection.lean`, `Algsuperdiff/Probability/StationaryValueProjection.lean`, `Algsuperdiff/Section3/Disorder/Cstar.lean` |
| the flat `Model` | `Algsuperdiff/Section3/Model.lean` and the frozen assumption files |
| `LowerTailGood`, `CutoffSample`, `cutoffSampleMeasure` | `Algsuperdiff/Section3/Cutoff/Control.lean`, `Algsuperdiff/Section3/Cutoff/Carrier.lean`, `Algsuperdiff/Section3/Cutoff/Finite.lean`, `Algsuperdiff/Section3/Cutoff/Limit.lean` |
| `ShellField.translate`, the shell gradient gauges, `FullTailGood`, `FullSample`, `fullSampleMeasure`, `streamField`, `streamCoefficient` | `Algsuperdiff/Assumptions/ShellField/Actions.lean`, `Algsuperdiff/Section3/Provider/Stream/ShellDerivativeControl.lean`, `Algsuperdiff/Section3/Provider/Stream/LargeCubeW1Inf.lean`, `Algsuperdiff/Section4/Support/ShellNorms.lean`, `Algsuperdiff/Section5/Field/TailGauge.lean`, `Algsuperdiff/Section5/Field/Carrier.lean`, `Algsuperdiff/Section5/Field/StreamField.lean` |
| `wholeSpaceCube`, `IsResolventSolutionOn`, `IsCubeResolvent`, `IsResolventTest`, the path instances, `IsDiffusionOf`, `intrinsicScale` | `Algsuperdiff/StochasticProcess/Common/DivergenceForm/WholeSpace/Cubes.lean`, `Algsuperdiff/StochasticProcess/Common/DivergenceForm/WholeSpace/Minimal.lean`, `Algsuperdiff/StochasticProcess/Common/DivergenceForm/AlphaShiftedWeakSolution.lean`, MarkovProcess module `MarkovProcess.Path.Basic`, `Algsuperdiff/Section5/Support/IntrinsicScale.lean` |
| `H1Function`, `H10Function`, weak gradients | CoarseGraining modules `Homogenization.Sobolev.H1.Definitions`, `Homogenization.Sobolev.WeakDerivatives` |
| `IsDirichletSolutionOn`, `HolderSeminormBoundOn`, `HasGradientOn`, `normalizedVolumeMeasureOn` | `Algsuperdiff/Section4/Support/Dirichlet.lean`, `Algsuperdiff/Section4/Support/ClassicalGradient.lean` |
| `volumeAverage` | CoarseGraining module `Homogenization.CoarseGraining.Definitions` |

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash SuperdiffusionAudit/check_standalone.sh SuperdiffusionAudit/Superdiffusivity/Challenge.lean
bash SuperdiffusionAudit/check_standalone.sh SuperdiffusionAudit/GeneratorRenormalization/Challenge.lean
bash SuperdiffusionAudit/check_standalone.sh SuperdiffusionAudit/AnomalousRegularity/Challenge.lean
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per file.

**Status.** All three comparator pairs are complete. The `Superdiffusivity`
solution
`SuperdiffusionAudit/Superdiffusivity/Solution.lean` imports the repository and
proves the byte-identical challenge statement through the bridges in
`SuperdiffusionAudit/Support/` (`SuperdiffusivityBridge.lean`,
`SuperdiffusivityCarrierMeasurability.lean`, `LaplaceUniqueness.lean`,
`SuperdiffusivityResolvent.lean`, `SuperdiffusivityLiveLaw.lean`,
`SuperdiffusivityMarginal.lean`); `#print axioms` on the solution theorem gives
exactly `propext`, `Classical.choice`, `Quot.sound`. The Theorem B and Theorem C
challenges state the field versions printed in the introduction, for the
coefficient field of the sample rather than an infrared cutoff. Their
`Solution.lean` files prove those exact challenges through
`Algsuperdiff.Frozen.Introduction.generator_renormalization` and
`Algsuperdiff.Frozen.Introduction.anomalous_regularity`, respectively. The
[comparator workflow](../.github/workflows/comparator.yml) is configured to
check all three challenge/solution pairs.
