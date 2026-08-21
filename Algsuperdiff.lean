/- ## Main results

`Algsuperdiff/MainTheorems.lean` states the three headline theorems in full
and proves each by direct application to its certified counterpart. -/

import Algsuperdiff.MainTheorems

import Algsuperdiff.Assumptions
import Algsuperdiff.Probability
import Algsuperdiff.Section24.CoarseMatrixDerivative
import Algsuperdiff.Section24.Sensitivity
import Algsuperdiff.Section24.Sensitivity.Provider
import Algsuperdiff.Section24.Sensitivity.Vocabulary
import Algsuperdiff.Section3

/- ## Main results — the Section 3 frozen surface

The three Section 3 root theorems, followed by the rest of the frozen
statement surface.  Importing them here keeps every build re-compiling
the main results themselves; every file below is sorry-free.
-/

import Algsuperdiff.Frozen.Section3.MultiscaleEstimate
import Algsuperdiff.Frozen.Section3.InductionStep
import Algsuperdiff.Frozen.Section3.InductionBounds

import Algsuperdiff.Frozen.Section3.BadEventEstimate
import Algsuperdiff.Frozen.Section3.BaseCase
import Algsuperdiff.Frozen.Section3.CoarseEllipticityBounds
import Algsuperdiff.Frozen.Section3.DiffusivityAsymptotics
import Algsuperdiff.Frozen.Section3.GoodLocalEventAt
import Algsuperdiff.Frozen.Section3.HomogenizationStep
import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Frozen.Section3.StreamDerivativeSumBound
import Algsuperdiff.Frozen.Section3.StreamIncrementEstimates
import Algsuperdiff.Frozen.Section3.StreamIncrementL2LargeCube
import Algsuperdiff.Frozen.Section3.StreamIncrementLpLargeCube
import Algsuperdiff.Frozen.Section3.StreamIncrementLpNormSqLargeCube
import Algsuperdiff.Frozen.Section3.TailBounds

/- ## Main results — the Section 4 frozen surface

The two Section 4 root theorems (Theorem C, `anomalous_regularity`, and
Theorem B, `generator_renormalization`), followed by the rest of the
frozen Section 4 surface.  Importing them here keeps every build
re-compiling the main results themselves; every file below is sorry-free.
-/

import Algsuperdiff.Frozen.Section4.AnomalousRegularity
import Algsuperdiff.Frozen.Section4.GeneratorRenormalization

import Algsuperdiff.Frozen.Section4.AnnularDecomposition
import Algsuperdiff.Frozen.Section4.BoundsMathcalEaL
import Algsuperdiff.Frozen.Section4.GoodEvents
import Algsuperdiff.Frozen.Section4.HarmonicApproximation
import Algsuperdiff.Frozen.Section4.IterationLemma
import Algsuperdiff.Frozen.Section4.MinimalScaleSeparation
import Algsuperdiff.Frozen.Section4.ProportionGoodScales

/-!
# ABK26 superdiffusion formalization

This is the deliberately small root of the clean formalization. Project modules
live below `Algsuperdiff/`; mathematical infrastructure is imported only from
Mathlib and `Homogenization`.
-/
