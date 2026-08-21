# Comparator design memo — bridge inventory for the Solution packet

Written by the challenge author (CL7, 2026-08-20) for whoever writes
`Audit/*/Solution.lean` and `SolutionBasic.lean`.  The two challenge files
share sections 1–10 byte-for-byte (the Anomalous Regularity file was
assembled from the Generator Renormalization file's lines 86–1213); section
11 differs only in `volumeAverage` (B) vs `normalizedVolumeMeasureOn` (C),
and section 12 is the theorem.

## 0. Solution architecture (LIH pattern)

Per the LIH comparators: `SolutionBasic.lean` must be a verbatim copy of the
challenge's vocabulary (sections 1–11) importing **only Mathlib** — a
repository import there changes instance elaboration inside the vocabulary
and fails the comparator's constant-by-constant closure check even when every
proxy check passes.  `Solution.lean` imports the repository plus
`SolutionBasic` and proves the byte-identical theorem via private bridges.

## 1. Defeq-shared vocabulary (bridges expected to be `rfl`/`show`-level)

All of the following challenge declarations are `def`s (not structures) whose
bodies mirror the repository/LIH bodies token-for-token, over carriers that
are themselves shared Mathlib types after delta-reduction.  In particular the
challenge's `ShellField d` delta-reduces to the same subtype as
`Algsuperdiff.Frozen.Assumptions.ShellField d`, so everything built on it is
expected to be definitionally equal to the repository object:

| Challenge | Repository/LIH object | Notes |
| --- | --- | --- |
| `ShellField`, its topology/Borel instances | frozen `ShellField`, `shellFieldCompactOpenTopology/BorelMeasurableSpace` | same subtype, same `inferInstance` route; see uncertainty U1 |
| `ShellField.deriv/secondDeriv/skew_entry` | `Assumptions/ShellField/Basic.lean` | projections |
| `scale/translate/spatialScale/rescale/triadicScale/negate/rotate` | `Assumptions/ShellField/Actions.lean` | identical bodies incl. the private CLM helpers |
| `ShellSeq`, `shellMarginalLaw`, `zeroShellLaw`, `negateSequence`, `rotateSequence` | `Assumptions/ShellField/SequenceLaw.lean` | measurability proofs differ but are proof-irrelevant |
| `LowerTailGood`, `CutoffSample` | `Section3/Cutoff/Control.lean`, `Carrier.lean` | whole chain (`localCubeControl → unitCubeValueNorm → …`) is defs over shared carriers |
| `cutoffSampleMeasure M.P` | `(Cutoff.cutoffSampleLaw M).toMeasure` | iota-reduces to the same `Measure.comap Subtype.val` |
| `cutoffValue`, `coefficientCutoff nu L omega` | `(Cutoff.coefficientCutoff nu L omega).toCoeffField` | unfold `RegCoeffField` addition + `constRegCoeffField`; at worst a `funext`-`rfl` |
| `j2Observable` and the cube norms | `Assumptions/ShellField/J2Observable.lean` | the private `…AtIndex` helpers are inlined ranges; `sSup (Set.range …)` matches after unfolding `…ValueSet` |
| `zeroShellRegMeasure P` | `(zeroShellRegLaw P).toMeasure` | repo lemma `zeroShellRegLaw_toMeasure_eq_map_forgetShell`; the function `forgetShell ∘ (· 0)` unfolds to the challenge's lambda |
| `vecNorm`, `matrixOperatorNorm`, `IsSignedPermutationMatrix`, `basisVec`, `vecDot/vecNormSq/matVecMul/matTranspose`, `volumeAverage` | LIH `Ambient/Basic`, `Book/Ch02`, `Geometry/SignedPermutation`, `CoarseGraining/Definitions` | identical bodies |
| `openCubeSet (originCube d m)` | LIH's | the **set** is defeq (iota on the structure literal) even though `TriadicCube` is a structure copy |

## 2. Structure copies (mechanical iso transport)

New inductive types in the challenge; the Solution must convert both ways by
field shuffling.  All proposition fields are stated over the defeq-shared
vocabulary above, so the conversions are constructor applications:

- `TriadicCube` ↔ `Homogenization.TriadicCube` (only ever consumed through
  `openCubeSet (originCube d m)`, which is set-level defeq — the iso may not
  even be needed).
- `H1Function U` / `H10Function U` ↔ LIH's, at
  `U = openCubeSet (originCube d m)`.  Statement position: universally
  quantified solution/test data.  Both directions are needed (universal
  binders in hypotheses AND in the `IsDirichletSolutionOn` definition's
  `H10Function` test quantifier — note the challenge's Dirichlet predicate
  quantifies over challenge `H10Function`s, the repo's over repo ones; the
  equivalence of the two predicates is a two-way test-function transport).
- `RegCoeffField` ↔ LIH `RegCoeffField` — see item 3; this is the only
  structure copy where the transport is more than field shuffling, because
  measures and `Lp` spaces are built on it.
- `Model d` ↔ `Algsuperdiff.Section3.ABKModel d` — field shuffling into
  `ShellLawPrefix`/`J1`/`J2`/`J3` plus item 4 for `J4`.
- `IsProbeR` ↔ LIH `IsProbeR` (Prop structure; three-field iff).

## 3. THE deep bridge: the corrector norm identity across the carrier iso

`RealizesCstar d P cstar` must be proved equivalent (given the other model
fields) to `Disorder.cstar M = cstar`.  Chain:

1. `e : RegCoeffField_chal d ≃ RegCoeffField_LIH d` by field shuffling; show
   it is a measurable equiv for the joint σ-algebras (both sides are
   `pointwise ⊔ entryTest` over the same probes/generators — the generating
   sets correspond under `e` literally).
2. `Measure.map e (zeroShellRegMeasure_chal P) = (zeroShellRegLaw P).toMeasure`
   (both are pushforwards of `P` along maps intertwined by `e`).
3. `e` intertwines `translateReg_chal z` with LIH `translateReg z` (defeq on
   values) and `originForcing_chal` with the repo `originForcing`
   (`HilbertVec.ofVec = WithLp.toLp 2` — defeq).
4. The induced `Lp`-isometry
   `Lp (HilbertVec d) 2 μ_chal ≃ₗᵢ Lp (HilbertVec d) 2 μ_repo`
   (via `Lp.compMeasurePreservingₗᵢ` along `e⁻¹`) intertwines the two
   Koopman families (proof irrelevance handles the different
   `MeasurePreserving` witnesses), hence maps
   `HasHorizontalGradient`-pairs to `HasHorizontalGradient`-pairs **in both
   directions** (needed: the isometry is invertible, so images of gradients
   are gradients — use the inverse isometry for the converse), hence maps
   `horizontalGradientRange` onto the repo's, hence (isometries preserve
   closures) `stationaryPotentialSubspace` onto the repo's, hence commutes
   with `starProjection` (`Submodule.starProjection` is characterized by
   membership + orthogonal-complement membership, both isometry-stable —
   use `eq_starProjection_of_mem_orthogonal`), hence
   `‖corrector_chal‖ = ‖corrector_repo‖`.
5. Conclude both directions of the `cstar` tie via
   `Disorder.cstar_characterization` (existence + uniqueness).  The
   universally quantified proof arguments in `RealizesCstar` are discharged
   with `zeroShellRegLaw_stationary_of_zeroShellLaw_stationary` and
   `memLp_originForcing_of_j2_tail` (transported through `e`); proof
   irrelevance collapses the remaining differences.

This is the Solution packet's principal work item.  Estimated as the analog
of LIH's QuenchedComparison law-transport bridges (A/B) plus one genuinely
new Hilbert-space step (the projection intertwining, step 4).

## 4. J4 / model equivalence

Challenge `Model.nondegenerate : ∃ cstar > 0, RealizesCstar d P cstar` vs
repo `ShellLawJ4.nondegenerate`.  Same mechanism as item 3 (it IS the same
display, quantified over unit vectors).  The challenge presents unit vectors
as `(e : Vec d) → vecNorm e = 1 → …` where the repo uses the subtype
`{e // vecNorm e = 1}`; trivial to convert.  Direction repo → challenge also
needs the two universally quantified proof-props to be *inhabited* only when
instantiating — they are, by the two repo lemmas named above.

## 5. Theorem-level bridges

- **B**: apply `Algsuperdiff.Frozen.Section4.generator_renormalization` at
  the transported model; pick the same `gamma0, C`; every display clause
  transports through items 1–2 (`EB` is literally reusable: `CutoffSample`
  is defeq-shared).
- **C**: apply `Algsuperdiff.Frozen.Section4.anomalous_regularity` AND
  `…generator_renormalization` (for the `sigmaBarM` witness = the canonical
  `Annealed.sigmaBar M m` with its profile bound).  Take
  `gamma0 := min gamma0_C gamma0_B`, `C := max C_C C_B` and check
  monotonicity of every clause in `C`:
  - tail bound `C·exp(-((1-α)²(N-C))/(Cγ))` is monotone increasing in `C`
    (for `N ≥ 0`, `C' ≥ C > 0`: `N/C' ≤ N/C`);
  - the α-window `alpha ≤ 1 - C√γ` shrinks as `C` grows (hypothesis side —
    correct direction);
  - the excess prefactor and the profile band grow with `C`.
  A subtlety: Theorem B's existential `sigmaBarM` is not *stated* to be the
  canonical one; if the provider-side lemma proving the profile bound for
  `Annealed.sigmaBar M m` (it is instantiated as such in
  `Section4/Provider/Homogenization/HomSeamProviderFinal.lean`) is not
  exported at a convenient surface, the C-solution needs uniqueness-free
  gluing: the challenge only demands SOME `sigmaBarM` with the profile bound
  such that the C-display holds with it — so the C-solution must obtain the
  profile bound for the exact scalar appearing in the repo C-display,
  i.e. for the canonical `Annealed.sigmaBar M m`.  Locate/export that lemma
  (work item; it exists inside the B provider spine).

## 6. Strength-delta list (author-facing summary)

Recorded verbatim in each challenge's module docstring ("Presentation
deltas").  Summary with fidelity judgments:

| # | Delta | Direction | Judgment |
| --- | --- | --- | --- |
| D1 | `Disorder.cstar M = cstar` → corrector energy display (`RealizesCstar`) | equivalent | faithful (repo's own characterization theorem) |
| D2 (C only) | canonical `Annealed.sigmaBar M m` → `∃ sigmaBarM` with Theorem B's profile band; witness formally allowed to depend on `alpha` | challenge strictly weaker | author-approved pattern ("the challenge asserts the existence of a scalar with the stated properties; the library proves it for the canonical one") |
| D3 | nested assumption structures → flat `Model` | equivalent | faithful |
| D4 | J4/corrector proof arguments universally quantified | equivalent (proof irrelevance; props are theorems of the model) | faithful |
| D5 | instance-driven corrector construction → hypothesis-explicit | same construction, proof-irrelevant witnesses | faithful |
| D6 | `cutoffSampleLaw` as bare comap `Measure` (probability property not asserted) | same measure; challenge does not assert `IsProbabilityMeasure` | faithful for the displays (all are measure-level); the probability property is repo-proved |
| D7 | `coefficientCutoff …​ .toCoeffField` → bare function | definitional | faithful |
| D8 | `zeroShellRegLaw` as bare `Measure.map` | definitional (repo lemma) | faithful |
| D9 | unit vectors as `e` + `vecNorm e = 1` hypothesis (J4/`RealizesCstar`) instead of subtype | equivalent | faithful |

## 7. Uncertainties

- **U1 (instance environments).**  The challenges import all of Mathlib; the
  repository files import slices.  If any relevant instance (topology on
  `Mat d`, norm-induced vs strong topology on the CLM carriers, the
  `MeasurableSpace (Mat d)` declared in both places) resolves differently in
  the two environments, the "defeq-shared" claims of item 1 degrade to
  propositional bridges.  This will surface as failing `rfl`s in the
  Solution packet; no such failure is *known*, and the LIH comparators
  survived the same risk.
- **U2.**  `Lp.compMeasurePreservingₗᵢ`-based intertwining (item 3 step 4)
  has not been prototyped; if `Submodule.starProjection` interacts poorly
  with the isometry, fall back to the characterization lemma
  (`eq_starProjection_of_mem_orthogonal`) as sketched.
- **U3.**  The C-solution's constant-monotonicity chores (item 5) assume
  `N ≥ 0` (true: `N : ℕ`) and `C > 0`; verified on paper only.
- **U4.**  Resolved: the `Audit` library is declared in `lakefile.lean`
  (`lake build Audit`), and each challenge can also be elaborated standalone
  via `Audit/check_standalone.sh`.
