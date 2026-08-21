# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the two main
theorems of the formalization of *Anomalous diffusion in critical
environments* (Armstrong–Bou-Rabee–Kuusi): Theorem B (renormalization of the
generator) and Theorem C (anomalous large-scale regularity).  Each comparator
lives in its own subdirectory:

| Directory | Checked theorem |
| --- | --- |
| `GeneratorRenormalization/` | `Algsuperdiff.StatementAudit.GeneratorRenormalization.generator_renormalization` |
| `AnomalousRegularity/` | `Algsuperdiff.StatementAudit.AnomalousRegularity.anomalous_regularity` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem — the antisymmetric `C²` shell-field
carrier and its compact-open Borel structure, the exact shell transformations
(translation, triadic scaling, negation, signed-permutation conjugation), the
regular-coefficient-field carrier with its joint pointwise/entry-test
σ-algebra, the (J2) weighted cube observable, the stationary
potential-corrector Hilbert machinery behind the (J4) constant `cstar`, the
flat standing model, the lower-infinite infrared cutoff and its sample
carrier, and the weak-`H¹` Dirichlet-problem vocabulary on triadic cubes —
states the theorem, and ends with one `sorry`, the proof being checked.

## What Is Checked

Both theorems quantify over the full standing model: a probability law on
bi-infinite sequences of `C²` antisymmetric shell fields with independent
shells, exact triadic marginal scaling, (J1) mean-zero / stationarity /
`√d`-range of dependence, (J2) strict Gaussian tails for the weighted `C²`
cube norms, (J3) hyperoctahedral and negation invariance, and (J4) the
stationary potential-corrector non-degeneracy, whose corrector energy is
`cstar · log 3` in every unit direction.  The random environment is the
truncated stream coefficient `a_L = ν·Id + ∑_{k ≤ L} j_k` on the
lower-tail-convergent sample carrier.

- **`GeneratorRenormalization`** (Theorem B): for `gamma ≤ gamma0` and every
  scale `m` there are a scalar `sigmaBarM > 0` tracking the superdiffusive
  profile `sqrt (ν² + cstar·γ⁻¹·3^{2γm})` up to relative error
  `C √γ |log γ|`, and a random error amplitude `EB ≥ 0` with a
  Gaussian-type moment bound, such that almost surely, for all `L ≥ m`, the
  solution of the random Dirichlet problem on the origin cube of side `3^m`
  and the solution of the homogenized problem `sigmaBarM·Id` with the same
  data differ uniformly by at most `EB` times the natural `C^{0,1/2}` data
  norms, and their Dirichlet energies agree to the corresponding square.
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
| `Vec`, `Mat`, vector/matrix operations, `vecNorm`, `matrixOperatorNorm`, `IsSignedPermutationMatrix` | LIH `Homogenization/Ambient/Basic.lean`, `Homogenization/Book/Ch02/Theorems/MatrixOperatorNorm.lean`, `Homogenization/Geometry/SignedPermutation.lean` |
| `TriadicCube`, `openCubeSet`, `originCube` | LIH `Homogenization/Geometry/TriadicCube.lean` |
| `ShellField`, its topology/Borel structure and coordinate API | `Algsuperdiff/Frozen/Assumptions/ShellField*.lean`, `Algsuperdiff/Assumptions/ShellField/Basic.lean` |
| shell transformations and their measurability | `Algsuperdiff/Assumptions/ShellField/Actions.lean` |
| `ShellSeq`, marginal laws, sequence transformations | `Algsuperdiff/Assumptions/ShellField/SequenceLaw.lean` |
| `RegCoeffField`, probes, `entryTestR`, the carrier σ-algebras, `translateReg` | LIH `Homogenization/Probability/RegCoeffField.lean`, `.../RegCoeffField/{Sigma,Endomorphisms}.lean` |
| `lihLocalSigma`, `forgetShell` | `Algsuperdiff/Assumptions/ShellField/{LIHLocalSigma,Basic}.lean` |
| the (J2) observable `j2Observable` and its cube norms | `Algsuperdiff/Assumptions/ShellField/J2Observable.lean` |
| the stationary potential corrector and `RealizesCstar` | `Algsuperdiff/Probability/{StationaryProjection,StationaryValueProjection}.lean`, `Algsuperdiff/Section3/Disorder/Cstar.lean` |
| the flat `Model` | `Algsuperdiff/Section3/Model.lean` and the frozen assumption files |
| `LowerTailGood`, `CutoffSample`, `cutoffSampleMeasure`, `coefficientCutoff` | `Algsuperdiff/Section3/Cutoff/{Control,Carrier,Finite,Limit}.lean` |
| `H1Function`, `H10Function`, weak gradients | LIH `Homogenization/Sobolev/{H1/Definitions,WeakDerivatives}.lean` |
| `IsDirichletSolutionOn`, `HolderSeminormBoundOn`, `HasGradientOn`, `normalizedVolumeMeasureOn` | `Algsuperdiff/Section4/Support/{Dirichlet,ClassicalGradient}.lean` |
| `volumeAverage` | LIH `Homogenization/CoarseGraining/Definitions.lean` |

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/GeneratorRenormalization/Challenge.lean
bash Audit/check_standalone.sh Audit/AnomalousRegularity/Challenge.lean
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per file.

**Status.**  Both comparators are checked and passing.  Each
`Audit/*/Solution.lean` imports the repository and proves the byte-identical
challenge statement through the bridges in `Audit/Support/`;
`leanprover/comparator` (commit `5756749`, with `lean4export` at its
`v4.26.0` tag, commit `3e1cdfe206ec3f54bae4a548d814ce9b2c1bb43d`) confirms
identical elaborated statements, walks the full dependency closure of each
challenge theorem constant-by-constant, replays the solution through the
Lean kernel, and prints its acceptance line — `Your solution is okay!` —
for both pairs, with the permitted axioms exactly
`propext`, `Classical.choice`, `Quot.sound`.
