import Algsuperdiff.Frozen.Section4.GoodEvents
import Algsuperdiff.Section4.Support.CgEllipLowerConstant
import Algsuperdiff.Section4.Support.FluxCorrectedRepresentative
import Algsuperdiff.Section4.Provider.MinimalScale.MinimalScaleFinal

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-!
# Minimal scale separation — [ABK] `p.minimal.scale.separation.sec4`

There is an almost surely finite random minimal scale `Z`, with an exponential
tail in the number of scales, above which the scale averages of two quantities
are simultaneously at most `delta`, uniformly over the triadic lattice points
of the ambient cube: the flux-corrected error observable restricted to the
good event, and the indicator of the complement of that good event.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.minimal_scale_separation
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s delta : ℝ),
        s ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
        M.gamma ≤
          (C⁻¹) ^ (10 : ℕ) *
            min (Disorder.cstar M ^ (10 : ℕ))
              (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) →
        8 * M.gamma ≤ s →
        ∀ m : ℤ, ∀ hs : 0 < s,
          ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable Z ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ Z omega} ≤
                  ENNReal.ofReal
                    (C *
                      Real.exp
                        (-(((N : ℝ) - 1) * s ^ (9 : ℕ) *
                              Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
                          (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                (⨆ z : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d (n - 1) m),
                    ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
                      ∑ k ∈ Finset.Icc n m,
                        Set.indicator
                          (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) k
                            (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                            ⟨s, hs⟩ (s * Real.sqrt delta))
                          (fun omega' =>
                            Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSup M k
                              ⟨s, hs⟩
                              (Cutoff.translateCutoffSample
                                (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                                omega'))
                          omega)) ≤
                  ENNReal.ofReal delta ∧
                (⨆ z : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d (n - 1) m),
                    ((((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
                      ∑ k ∈ Finset.Icc n m,
                        Set.indicator
                          ((Algsuperdiff.Frozen.Section4.goodEventAt M
                              (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) k
                              (Algsuperdiff.Section4.Support.triadicLatticePoint (n - 1) z)
                              ⟨s, hs⟩ (s * Real.sqrt delta))ᶜ)
                          (fun _ => (1 : ℝ≥0∞)) omega)) ≤
                  ENNReal.ofReal delta
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.MinimalScale.minimal_scale_separation_provider d
