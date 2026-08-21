# Correspondence: paper ↔ Lean

This document maps the certified statement surface of the formalization to
the paper *Superdiffusion and anomalous regularization in self-similar random
incompressible flows* (Armstrong–Bou-Rabee–Kuusi), so a reader of the paper
can locate where each result is proved.

**Conventions.**
- Lean names are given relative to the `Algsuperdiff` namespace root; file
  paths are relative to the repository root.
- The **source** column gives the paper's own statement label.
- **Status**: `proved` — formalized and proved as stated;
  `definition` — a definition or predicate anchor rather than a theorem.
- Sections 1-4 of the paper are formalized; Section 5 and Theorem A (the
  diffusion process) are not yet -- see the README.
- The main results are additionally exposed, stated in full, in
  [`Algsuperdiff/MainTheorems.lean`](Algsuperdiff/MainTheorems.lean), and
  Theorems B and C are comparator-checked (see [`Audit/`](Audit/)).

**Note.**  Rows marked *(statement number at release)* correspond to
definitions and lemmas whose paper statement numbers will be filled in when
the paper's numbering is final; the main results and the named lemmas carry
the paper's own labels.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| `(statement number at release)` | `Frozen.Section24.LInfMatrixFieldOn` | `Algsuperdiff/Frozen/Section24/LInfMatrixFieldOn.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.existsUnique_coarseMatrixDerivative` | `Algsuperdiff/Frozen/Section24/ExistsUniqueCoarseMatrixDerivative.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.coarseMatrixDerivative` | `Algsuperdiff/Frozen/Section24/CoarseMatrixDerivative.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.coarseMatrixDerivative_characterization` | `Algsuperdiff/Frozen/Section24/CoarseMatrixDerivativeCharacterization.lean` | proved |
| `(statement number at release)` | `Frozen.Assumptions.ShellField` | `Algsuperdiff/Frozen/Assumptions/ShellField.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.shellFieldCompactOpenTopology` | `Algsuperdiff/Frozen/Assumptions/ShellFieldCompactOpenTopology.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.shellFieldBorelMeasurableSpace` | `Algsuperdiff/Frozen/Assumptions/ShellFieldBorelMeasurableSpace.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.ShellLawPrefix` | `Algsuperdiff/Frozen/Assumptions/ShellLawPrefix.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.ShellLawJ1` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ1.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.ShellLawJ2` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ2.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.ShellLawJ3` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ3.lean` | definition |
| `(statement number at release)` | `Frozen.Assumptions.ShellLawJ4` | `Algsuperdiff/Frozen/Assumptions/ShellLawJ4.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.LInfSkewMatrixFieldOn` | `Algsuperdiff/Frozen/Section24/LInfSkewMatrixFieldOn.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.matrixDerivativeNorm` | `Algsuperdiff/Frozen/Section24/MatrixDerivativeNorm.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.matrixSecondDerivativeNorm` | `Algsuperdiff/Frozen/Section24/MatrixSecondDerivativeNorm.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.UnitCubeSkewW2Infinity` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.UnitCubeSkewW2Infinity.w1Infinity` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity/W1Infinity.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.UnitCubeSkewW2Infinity.gradientW1Infinity` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity/GradientW1Infinity.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.UnitCubeSkewW2Infinity.valueL2` | `Algsuperdiff/Frozen/Section24/UnitCubeSkewW2Infinity/ValueL2.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.perturbCoeffOn` | `Algsuperdiff/Frozen/Section24/PerturbCoeffOn.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.existsUnique_unitCubeLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/Lambda/ExistsUniqueUnitCubeLambda.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.unitCubeLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/Lambda/UnitCubeLambda.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.unitCubeLambda_characterization` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/Lambda/UnitCubeLambdaCharacterization.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.existsUnique_unitCubeBigLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/BigLambda/ExistsUniqueUnitCubeBigLambda.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.unitCubeBigLambda` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/BigLambda/UnitCubeBigLambda.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.unitCubeBigLambda_characterization` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/BigLambda/UnitCubeBigLambdaCharacterization.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.existsUnique_unitCubeHomogenizationError` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/HomogenizationError/ExistsUniqueUnitCubeHomogenizationError.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.unitCubeHomogenizationError` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/HomogenizationError/UnitCubeHomogenizationError.lean` | definition |
| `(statement number at release)` | `Frozen.Section24.unitCubeHomogenizationError_characterization` | `Algsuperdiff/Frozen/Section24/UnitCubeMultiscale/HomogenizationError/UnitCubeHomogenizationErrorCharacterization.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.responseJ_derivative` | `Algsuperdiff/Frozen/Section24/ResponseJDerivative.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.coarseMatrixDerivative_bound` | `Algsuperdiff/Frozen/Section24/CoarseMatrixDerivativeBound.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.lambda_sensitivity` | `Algsuperdiff/Frozen/Section24/LambdaSensitivity.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.responseJ_sensitivity` | `Algsuperdiff/Frozen/Section24/ResponseJSensitivity.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.bigLambda_sensitivity` | `Algsuperdiff/Frozen/Section24/BigLambdaSensitivity.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.bigLambda_sensitivity_at_delta` | `Algsuperdiff/Frozen/Section24/BigLambdaSensitivityAtDelta.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.lambda_sensitivity_unconditional` | `Algsuperdiff/Frozen/Section24/LambdaSensitivityUnconditional.lean` | proved |
| `(statement number at release)` | `Frozen.Section24.responseJ_sensitivity_unconditional` | `Algsuperdiff/Frozen/Section24/ResponseJSensitivityUnconditional.lean` | proved |
| `d.mathcalS.def` | `Frozen.Section3.inductionState` | `Algsuperdiff/Frozen/Section3/InductionState.lean` | definition |
| `e.xi.delta1.condition and e.propagation.of.indyhyp` | `Frozen.Section3.induction_step` | `Algsuperdiff/Frozen/Section3/InductionStep.lean` | proved |
| `p.induction.bounds` | `Frozen.Section3.induction_bounds` | `Algsuperdiff/Frozen/Section3/InductionBounds.lean` | proved |
| `(statement number at release)` | `Frozen.Section3.stream_increment_lp_large_cube_bound` | `Algsuperdiff/Frozen/Section3/StreamIncrementLpLargeCube.lean` | proved |
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
| `p.multiscale.estimate; adopted Section 3.6 proof correction` | `Frozen.Section3.multiscale_estimate` | `Algsuperdiff/Frozen/Section3/MultiscaleEstimate.lean` | proved |
| `(statement number at release)` | `Frozen.External.calderon_zygmund` | `Algsuperdiff/Frozen/External/CalderonZygmund.lean` | proved |
| `(statement number at release)` | `Frozen.External.cube_schauder` | `Algsuperdiff/Frozen/External/CubeSchauder.lean` | proved |
| `l.bad.event.lemma` | `Frozen.Section3.bad_event_estimate` | `Algsuperdiff/Frozen/Section3/BadEventEstimate.lean` | proved |
| `d.good.event.for.lambda` | `Frozen.Section4.goodEventAt` | `Algsuperdiff/Frozen/Section4/GoodEvents.lean` | definition |
| `p.mathcalE.annular.decomp` | `Frozen.Section4.annular_decomposition` | `Algsuperdiff/Frozen/Section4/AnnularDecomposition.lean` | proved |
| `p.minimal.scale.separation.sec4` | `Frozen.Section4.minimal_scale_separation` | `Algsuperdiff/Frozen/Section4/MinimalScaleSeparation.lean` | proved |
| `p.independence.between.scales` | `Frozen.Section4.proportion_of_good_scales` | `Algsuperdiff/Frozen/Section4/ProportionGoodScales.lean` | proved |
| `l.bounds.mathcal.E.aL` | `Frozen.Section4.bounds_mathcal_E_aL` | `Algsuperdiff/Frozen/Section4/BoundsMathcalEaL.lean` | proved |
| `l.iteration.lemma` | `Frozen.Section4.iteration_lemma` | `Algsuperdiff/Frozen/Section4/IterationLemma.lean` | proved |
| `l.harmonic.approximation.good.scales; the E-retention successor per the author rulings 2026-08-19 (Variant A)` | `Frozen.Section4.harmonic_approximation_good_scales` | `Algsuperdiff/Frozen/Section4/HarmonicApproximation.lean` | proved |
| `t.regularity` | `Frozen.Section4.anomalous_regularity` | `Algsuperdiff/Frozen/Section4/AnomalousRegularity.lean` | proved |
| `t.homogenization` | `Frozen.Section4.generator_renormalization` | `Algsuperdiff/Frozen/Section4/GeneratorRenormalization.lean` | proved |
