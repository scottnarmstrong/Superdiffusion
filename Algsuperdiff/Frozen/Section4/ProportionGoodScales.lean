import Algsuperdiff.Frozen.Section4.GoodEvents
import Algsuperdiff.Section4.Support.CgEllipLowerConstant
import Algsuperdiff.Section4.Provider.Proportion.ProportionFinal

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-!
# Proportion of good scales — [ABK] `p.independence.between.scales`

Along any window of consecutive triadic scales the good events occur at
almost every scale: the probability that the empirical proportion of good
scales in a window of length `Mw + 1` drops below `1 - theta` decays
exponentially in `Mw`, at a rate proportional to
`cstar^2 s^7 epsilon^2 theta / gamma`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.proportion_of_good_scales
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s ep theta : ℝ),
        s ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        ep ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        theta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        M.gamma ≤
          C⁻¹ * min (Disorder.cstar M ^ (10 : ℕ))
            (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ)) →
        8 * M.gamma ≤ s →
        C * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (6 : ℕ) * ep⁻¹ ^ (2 : ℕ) *
            M.gamma ≤ theta →
        ∀ (m0 : ℤ) (Mw : ℕ) (hs : 0 < s),
          (Cutoff.cutoffSampleLaw M).toMeasure
              {omega |
                (1 / ((Mw : ℝ) + 1)) *
                    ∑ k ∈ Finset.range (Mw + 1),
                      (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d)
                            (m0 + (k : ℤ)) 0 ⟨s, hs⟩ ep).indicator
                        (fun _ => (1 : ℝ)) omega ≤
                  1 - theta } ≤
            ENNReal.ofReal
              (6 *
                Real.exp
                  (-(Disorder.cstar M ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) *
                        theta * ((Mw : ℝ) + 1)) /
                    (C * M.gamma)))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Proportion.exists_proportion_good_scales_provider d
