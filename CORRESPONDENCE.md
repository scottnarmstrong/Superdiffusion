# Correspondence: paper ↔ Lean

This document maps the certified statement surface of the formalization to
the paper *Superdiffusion and anomalous regularization in self-similar random
incompressible flows* (Armstrong–Bou-Rabee–Kuusi), so a reader of the paper
can locate where each result is proved.

**Conventions.**
- Lean names are given relative to the `Algsuperdiff` namespace root; file
  paths are relative to the repository root.
- The **source** column gives the paper's own statement label when one is
  available, and otherwise a stable descriptive label for a supporting anchor.
- **Status**: `proved` — formalized and proved as stated;
  `definition` — a definition or predicate anchor rather than a theorem.
- Sections 1-5 of the paper are formalized, and Theorems A, B and C are proved.
- The three main results — Theorems A, B and C, in their introduction-level
  forms
  for the coefficient field `a = ν I + k` — are additionally exposed, stated
  in full, in
  [`Algsuperdiff/MainTheorems.lean`](Algsuperdiff/MainTheorems.lean), and all
  three have comparator challenge/solution pairs covered by the public workflow (see
  [`SuperdiffusionAudit/`](SuperdiffusionAudit/)).

Descriptive source labels below identify supporting definitions and lemmas
that do not carry a stable paper statement number; the main results and named
lemmas retain the paper's own labels.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| `definition: bounded matrix field on a set` | `Frozen.Section24.LInfMatrixFieldOn` | `Algsuperdiff/Frozen/Section24/LInfMatrixFieldOn.lean` | definition |
| `existence and uniqueness of the coarse-matrix derivative` | `Frozen.Section24.existsUnique_coarseMatrixDerivative` | `Algsuperdiff/Frozen/Section24/ExistsUniqueCoarseMatrixDerivative.lean` | proved |
| `definition: coarse-matrix derivative` | `Frozen.Section24.coarseMatrixDerivative` | `Algsuperdiff/Frozen/Section24/CoarseMatrixDerivative.lean` | definition |
| `characterization of the coarse-matrix derivative` | `Frozen.Section24.coarseMatrixDerivative_characterization` | `Algsuperdiff/Frozen/Section24/CoarseMatrixDerivativeCharacterization.lean` | proved |
| `definition: shell-field carrier` | `Frozen.Assumptions.ShellField` | `Algsuperdiff/Frozen/Assumptions/ShellField.lean` | definition |
| `compact-open topology on shell fields` | `Frozen.Assumptions.shellFieldCompactOpenTopology` | `Algsuperdiff/Frozen/Assumptions/ShellFieldCompactOpenTopology.lean` | definition |
| `Borel measurable structure on shell fields` | `Frozen.Assumptions.shellFieldBorelMeasurableSpace` | `Algsuperdiff/Frozen/Assumptions/ShellFieldBorelMeasurableSpace.lean` | definition |
| `definition: shell-law standing assumptions` | `Frozen.Assumptions.ShellLawPrefix` | `Algsuperdiff/Frozen/Assumptions/ShellLawPrefix.lean` | definition |
| `definition: shell-law condition J1` | `Frozen.Assumptions.ShellLawJ1` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ1.lean` | definition |
| `definition: shell-law condition J2` | `Frozen.Assumptions.ShellLawJ2` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ2.lean` | definition |
| `definition: shell-law condition J3` | `Frozen.Assumptions.ShellLawJ3` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ3.lean` | definition |
| `definition: shell-law condition J4` | `Frozen.Assumptions.ShellLawJ4` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ4.lean` | definition |
| `definition: bounded skew-matrix field on a set` | `Frozen.Section24.LInfSkewMatrixFieldOn` | `Algsuperdiff/Frozen/Section24/LInfSkewMatrixFieldOn.lean` | definition |
| `definition: matrix-derivative norm` | `Frozen.Section24.matrixDerivativeNorm` | `Algsuperdiff/Frozen/Section24/MatrixDerivativeNorm.lean` | definition |
| `definition: second matrix-derivative norm` | `Frozen.Section24.matrixSecondDerivativeNorm` | `Algsuperdiff/Frozen/Section24/MatrixSecondDerivativeNorm.lean` | definition |
| `definition: unit-cube skew-field W²∞ control` | `Frozen.Section24.UnitCubeSkewW2Infinity` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity.lean` | definition |
| `definition: unit-cube W¹∞ control` | `Frozen.Section24.UnitCubeSkewW2Infinity.w1Infinity` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity/W1Infinity.lean` | definition |
| `definition: unit-cube gradient W¹∞ control` | `Frozen.Section24.UnitCubeSkewW2Infinity.gradientW1Infinity` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity/GradientW1Infinity.lean` | definition |
| `definition: unit-cube value L² control` | `Frozen.Section24.UnitCubeSkewW2Infinity.valueL2` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity/ValueL2.lean` | definition |
| `definition: coefficient perturbation on a set` | `Frozen.Section24.perturbCoeffOn` | `Algsuperdiff/Frozen/Section24/PerturbCoeffOn.lean` | definition |
| `existence and uniqueness of unit-cube lambda` | `Frozen.Section24.existsUnique_unitCubeLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/Lambda/ExistsUniqueUnitCubeLambda.lean` | proved |
| `definition: unit-cube lambda` | `Frozen.Section24.unitCubeLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/Lambda/UnitCubeLambda.lean` | definition |
| `characterization of unit-cube lambda` | `Frozen.Section24.unitCubeLambda_characterization` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/Lambda/UnitCubeLambdaCharacterization.lean` | proved |
| `existence and uniqueness of unit-cube big lambda` | `Frozen.Section24.existsUnique_unitCubeBigLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/BigLambda/ExistsUniqueUnitCubeBigLambda.lean` | proved |
| `definition: unit-cube big lambda` | `Frozen.Section24.unitCubeBigLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/BigLambda/UnitCubeBigLambda.lean` | definition |
| `characterization of unit-cube big lambda` | `Frozen.Section24.unitCubeBigLambda_characterization` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/BigLambda/UnitCubeBigLambdaCharacterization.lean` | proved |
| `existence and uniqueness of unit-cube homogenization error` | `Frozen.Section24.existsUnique_unitCubeHomogenizationError` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/HomogenizationError/ExistsUniqueUnitCubeHomogenizationError.lean` | proved |
| `definition: unit-cube homogenization error` | `Frozen.Section24.unitCubeHomogenizationError` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/HomogenizationError/UnitCubeHomogenizationError.lean` | definition |
| `characterization of unit-cube homogenization error` | `Frozen.Section24.unitCubeHomogenizationError_characterization` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/HomogenizationError/UnitCubeHomogenizationErrorCharacterization.lean` | proved |
| `derivative formula for the response functional` | `Frozen.Section24.responseJ_derivative` | `Algsuperdiff/Frozen/Section24/ResponseJDerivative.lean` | proved |
| `bound for the coarse-matrix derivative` | `Frozen.Section24.coarseMatrixDerivative_bound` | `Algsuperdiff/Frozen/Section24/CoarseMatrixDerivativeBound.lean` | proved |
| `sensitivity of unit-cube lambda` | `Frozen.Section24.lambda_sensitivity` | `Algsuperdiff/Frozen/Section24/LambdaSensitivity.lean` | proved |
| `sensitivity of the response functional` | `Frozen.Section24.responseJ_sensitivity` | `Algsuperdiff/Frozen/Section24/ResponseJSensitivity.lean` | proved |
| `sensitivity of unit-cube big lambda` | `Frozen.Section24.bigLambda_sensitivity` | `Algsuperdiff/Frozen/Section24/BigLambdaSensitivity.lean` | proved |
| `sensitivity of unit-cube big lambda at fixed perturbation` | `Frozen.Section24.bigLambda_sensitivity_at_delta` | `Algsuperdiff/Frozen/Section24/BigLambdaSensitivityAtDelta.lean` | proved |
| `unconditional sensitivity of unit-cube lambda` | `Frozen.Section24.lambda_sensitivity_unconditional` | `Algsuperdiff/Frozen/Section24/LambdaSensitivityUnconditional.lean` | proved |
| `unconditional sensitivity of the response functional` | `Frozen.Section24.responseJ_sensitivity_unconditional` | `Algsuperdiff/Frozen/Section24/ResponseJSensitivityUnconditional.lean` | proved |
| `d.mathcalS.def` | `Frozen.Section3.inductionState` | `Algsuperdiff/Frozen/Section3/InductionState.lean` | definition |
| `e.xi.delta1.condition and e.propagation.of.indyhyp` | `Frozen.Section3.induction_step` | `Algsuperdiff/Frozen/Section3/InductionStep.lean` | proved |
| `p.induction.bounds` | `Frozen.Section3.induction_bounds` | `Algsuperdiff/Frozen/Section3/InductionBounds.lean` | proved |
| `large-cube Lᵖ stream-increment bound` | `Frozen.Section3.stream_increment_lp_large_cube_bound` | `Algsuperdiff/Frozen/Section3/StreamIncrementLpLargeCube.lean` | proved |
| `e.km.kn.L2.exact/e.km.kn.L2.bound` | `Frozen.Section3.stream_increment_l2_large_cube_bound` | `Algsuperdiff/Frozen/Section3/StreamIncrementL2LargeCube.lean` | proved |
| `e.W.1.inf.bound` | `Frozen.Section3.stream_derivative_sum_bound` | `Algsuperdiff/Frozen/Section3/StreamDerivativeSumBound.lean` | proved |
| `e.km.kn.Lp` | `Frozen.Section3.stream_increment_lp_norm_sq_large_cube_bound` | `Algsuperdiff/Frozen/Section3/StreamIncrementLpNormSqLargeCube.lean` | proved |
| `l.km.kn.Lp.estimates` | `Frozen.Section3.stream_increment_estimates` | `Algsuperdiff/Frozen/Section3/StreamIncrementEstimates.lean` | proved |
| `p.base.case` | `Frozen.Section3.base_case` | `Algsuperdiff/Frozen/Section3/BaseCase.lean` | proved |
| `p.tail.bounds` | `Frozen.Section3.tail_bounds` | `Algsuperdiff/Frozen/Section3/TailBounds.lean` | proved |
| `p.cg.ellipticity.bounds` | `Frozen.Section3.coarse_ellipticity_bounds` | `Algsuperdiff/Frozen/Section3/CoarseEllipticityBounds.lean` | proved |
| `e.good.local.events` | `Frozen.Section3.goodLocalEventAt` | `Algsuperdiff/Frozen/Section3/GoodLocalEventAt.lean` | definition |
| `p.propagate.diffusivity.lower.bound` | `Frozen.Section3.diffusivity_asymptotics` | `Algsuperdiff/Frozen/Section3/DiffusivityAsymptotics.lean` | proved |
| `p.homogenization.step` | `Frozen.Section3.homogenization_step` | `Algsuperdiff/Frozen/Section3/HomogenizationStep.lean` | proved |
| `p.multiscale.estimate` | `Frozen.Section3.multiscale_estimate` | `Algsuperdiff/Frozen/Section3/MultiscaleEstimate.lean` | proved |
| `external Calderón–Zygmund estimate` | `Frozen.External.calderon_zygmund` | `Algsuperdiff/Frozen/External/CalderonZygmund.lean` | proved |
| `external cube Schauder estimate` | `Frozen.External.cube_schauder` | `Algsuperdiff/Frozen/External/CubeSchauder.lean` | proved |
| `l.bad.event.lemma` | `Frozen.Section3.bad_event_estimate` | `Algsuperdiff/Frozen/Section3/BadEventEstimate.lean` | proved |
| `d.good.event.for.lambda` | `Frozen.Section4.goodEventAt` | `Algsuperdiff/Frozen/Section4/GoodEvents.lean` | definition |
| `p.mathcalE.annular.decomp` | `Frozen.Section4.annular_decomposition` | `Algsuperdiff/Frozen/Section4/AnnularDecomposition.lean` | proved |
| `p.minimal.scale.separation.sec4` | `Frozen.Section4.minimal_scale_separation` | `Algsuperdiff/Frozen/Section4/MinimalScaleSeparation.lean` | proved |
| `p.independence.between.scales` | `Frozen.Section4.proportion_of_good_scales` | `Algsuperdiff/Frozen/Section4/ProportionGoodScales.lean` | proved |
| `l.bounds.mathcal.E.aL` | `Frozen.Section4.bounds_mathcal_E_aL` | `Algsuperdiff/Frozen/Section4/BoundsMathcalEaL.lean` | proved |
| `l.iteration.lemma` | `Frozen.Section4.iteration_lemma` | `Algsuperdiff/Frozen/Section4/IterationLemma.lean` | proved |
| `l.harmonic.approximation.good.scales; E-retaining form` | `Frozen.Section4.harmonic_approximation_good_scales` | `Algsuperdiff/Frozen/Section4/HarmonicApproximation.lean` | proved |
| `t.regularity` | `Frozen.Introduction.anomalous_regularity` | `Algsuperdiff/Frozen/Introduction/AnomalousRegularity.lean` | proved |
| `t.regularity`; the general form, for the infrared cutoffs `a_L` of the coefficient field and uniform in the cutoff | `Frozen.Section4.anomalous_regularity` | `Algsuperdiff/Frozen/Section4/AnomalousRegularity.lean` | proved |
| `t.homogenization` | `Frozen.Introduction.generator_renormalization` | `Algsuperdiff/Frozen/Introduction/GeneratorRenormalization.lean` | proved |
| `t.homogenization`; the general form, for the infrared cutoffs `a_L` of the coefficient field and uniform in the cutoff | `Frozen.Section4.generator_renormalization` | `Algsuperdiff/Frozen/Section4/GeneratorRenormalization.lean` | proved |
| `t.superdiffusivity` | `Frozen.Section5.superdiffusivity_v2` | `Algsuperdiff/Frozen/Section5/SuperdiffusivityV2.lean` | proved |

## Section 5 support results

Theorem A above is the certified statement of the paper's Section 5.  The
results below are proved local results of the same development, listed so that
a reader of the section can find them.  The survival estimate is proved from
the two expected-exit-time bounds, which are hypotheses of its statement rather
than results of this development.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| `e.survival.probability` | `Section5.Provider.survivalProbabilityConstant_le_measure_le_exitTime_on` | `Algsuperdiff/Section5/Provider/OnePointChainLaplace.lean` | proved |
