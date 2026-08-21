import Algsuperdiff.Section3.Cutoff.CoefficientFamily
import Algsuperdiff.Section3.Observable.HomogenizationError

/-!
# Literal cutoff homogenization-error observable

This file records the *raw*, pointwise manuscript expression
`\mathcal E_{s,\infty,2}(\square_m; a_L, \sigma \operatorname{Id})` on the
canonical cutoff-sample carrier.  The coefficient scale `L` and the observed
cube scale `m` are deliberately separate arguments.

It is deliberately not itself the measurable representative.  The companion
module `CutoffHomogenizationErrorRepresentative` constructs the genuine
nonnegative measurable representative and proves its explicit almost-everywhere
identity with this literal expression.  Keeping the raw expression separate
prevents a measurable modification from being mistaken for the manuscript
observable.

## References

* ABK26, definition `d.mathcal.E`, (2.28).
* ABK26, definition `d.mathcalS.def`, Section 3.1.
-/

namespace Algsuperdiff.Section3.Observable

open Homogenization Homogenization.Book.Ch02

noncomputable section

/-- The literal cutoff expression
`\mathcal E_{s,\infty,2}(\square_m; a_L, \sigma \operatorname{Id})`.

`coefficientScale` specifies the actual lower-infinite cutoff coefficient
`a_L`, while `domainScale` specifies the cube `\square_m`; neither scale is
silently substituted for the other. -/
noncomputable def cutoffHomogenizationErrorRaw {d : ℕ} [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) : ℝ :=
  homogenizationErrorAtScale domainScale s
    (Cutoff.coefficientCutoffCoeffOn M coefficientScale omega
      (originCube d domainScale))
    sigma

/-- The raw cutoff expression is exactly the manuscript's homogenization
error on the genuine compatible cutoff family. -/
theorem cutoffHomogenizationErrorRaw_characterization {d : ℕ} [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    cutoffHomogenizationErrorRaw M coefficientScale domainScale s sigma omega =
      HomogenizationErrorOnCube (originCube d domainScale) s .infinity (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
        (isotropicComparatorMatrix sigma) := by
  exact homogenizationErrorAtScale_characterization domainScale s
    (Cutoff.coefficientCutoffCoeffOn M coefficientScale omega
      (originCube d domainScale)) sigma
    (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
    (Cutoff.coefficientCutoffTriadicCoeffFamily_coeffOn_aeeq M coefficientScale omega
      (originCube d domainScale))

/-- The literal cutoff homogenization error is nonnegative. -/
theorem cutoffHomogenizationErrorRaw_nonneg {d : ℕ} [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ}
    (hs : 0 < s) (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationErrorRaw M coefficientScale domainScale s sigma omega :=
  homogenizationErrorAtScale_nonneg domainScale hs
    (Cutoff.coefficientCutoffCoeffOn M coefficientScale omega
      (originCube d domainScale)) sigma

end

end Algsuperdiff.Section3.Observable
