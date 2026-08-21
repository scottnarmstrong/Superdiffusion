import Algsuperdiff.Section3.Cutoff.LawCarrier
import Algsuperdiff.Section3.Cutoff.RangeNormalization
import Algsuperdiff.Section3.Cutoff.Symmetry

/-!
# Structural law of the normalized coefficient cutoff

This file packages the structural properties of the canonically normalized
coefficient-cutoff law.  Stationarity, isotropy, and adjoint invariance are
transported separately through CoarseGraining's triadic normalization.
Unit-range dependence comes from the direct restriction-sigma-algebra proof for
the normalized cutoff law; no unit-range property of the unnormalized law is
assumed.

## Main results

* `cutoffNormalization_structuralLaw`: the normalized cutoff law satisfies the
  four Chapter 4 structural assumptions.
-/

namespace Algsuperdiff.Section3.Cutoff

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The canonically normalized genuine cutoff law has exactly the Chapter 4
structural package. The three symmetry fields are transported independently;
the unit-range field is the direct normalized-law theorem. -/
theorem cutoffNormalization_structuralLaw (M : ABKModel d) (m : ℤ) :
    Ch04.RestrictionStructuralLaw
      (Ch04.restrictionScaleNormalizedLaw (cutoffNormalizationDepth d m)
        (coefficientCutoffLaw M m)) where
  stationary :=
    Ch04.RestrictionStationaryLaw.scaleNormalized
      (coefficientCutoffLaw_stationary M m)
      (cutoffNormalizationDepth d m)
  unit_range := cutoffNormalization_unitRangeDependentLaw M m
  isotropic :=
    Ch04.RestrictionIsotropicLaw.scaleNormalized (coefficientCutoffLaw_isotropic M m)
      (cutoffNormalizationDepth d m)
  adjoint_invariant :=
    Ch04.RestrictionAdjointInvariantLaw.scaleNormalized
      (coefficientCutoffLaw_adjoint_invariant M m)
      (cutoffNormalizationDepth d m)

end

end Algsuperdiff.Section3.Cutoff
