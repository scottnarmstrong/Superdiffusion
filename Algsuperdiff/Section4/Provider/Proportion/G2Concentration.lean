/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.G2RowConversion
import Algsuperdiff.Section4.Provider.Proportion.G2Locality

/-!
# The `𝒢₂` lane: `r`-dependence of the atoms `X_j` and the proportion tail

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E`: the Appendix-D independence
hypothesis and the application of `p.concentration.for.scales` at the lane rate
`s' = ¼s`.

## `r`-dependence

`columnsIndep_Xcal` is the `𝒢₂` twin of `Concentration.columnsIndep_Ycal`, and
it runs on **exactly** the same geometry: the atom `X_j` reads only truncation
levels `≤ j − 2` and only on `annulusRegion d j`
(`G2Locality.measurable_Xcal_annulusRegion_local`, a statement with **no**
hypotheses), so the varying-level producer
`Probability.iIndepFun_of_local_cutoffSample` applies at the separation
supplied by `Probability.separatedBy_annulusRegion_of_gap` at the truncation
offset `c = 2`.

## The lane tail

`ratioTail_Xcal` assembles the Appendix-D unit moments
(`G2Moments.lintegral_rpow_le_one_Xcal`), the independence above, the proved
`ScalesConcentration.p_concentration_for_scales_Cstar` and the proved
`IndicatorDensityTails.ratioTail_of_concentration` — which also closes the
short-window gap with no extra hypothesis — into the tail

```
ℙ[ θ < (proportion of scales k ≤ n at which Ev k fails) ] ≤ exp(−c₁ n) / Q .
```

The event family `Ev` and its reduction `hreduce` are the caller's;
`G2RowConversion.hreduce_eventG2` supplies them for the frozen `𝒢₂` event
enlarged by the null set of `goodRowSetG2`.

## Scope

Provider material: proved local helpers.  `hcube` and `hnorm` are conditional A
obligations, discharged at the caller.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory ProbabilityTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `r`-dependence of the `𝒢₂` atoms -/

/-- **The Appendix-D independence hypothesis `e.independent.columns.twosided` for
the `𝒢₂` lane.**

The atoms `X_j` are `r`-dependent for every `r ≥ 1` with
`3 + 2·3^{1−2}√d ≤ 3^r`, i.e. `3 + (2/3)√d ≤ 3^r`.  The statement is at the
**general `r`**, so no dimension restriction enters this file.

Unlike the `𝒢₀` lane, the locality input needs no premise at all: the `𝒢₂`
locality endpoint `measurable_Xcal_annulusRegion_local` is unconditional. -/
theorem columnsIndep_Xcal (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ)) :
    ColumnsIndep (Cutoff.cutoffSampleLaw M).toMeasure (xcalArray M s D) r := by
  refine columnsIndep_colArray _ r fun b => ?_
  refine iIndepFun_of_local_cutoffSample M (fun j : ℤ => j * (r : ℤ) + b - 2)
    (U := fun j : ℤ => annulusRegion d (j * (r : ℤ) + b))
    (fun j => measurableSet_annulusRegion d _) ?_ ?_
  · intro j j' hjj'
    have hgap : (r : ℤ) ≤ |j * (r : ℤ) + b - (j' * (r : ℤ) + b)| := by
      have hrw : j * (r : ℤ) + b - (j' * (r : ℤ) + b) = (j - j') * (r : ℤ) := by ring
      rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (r : ℤ))]
      exact le_mul_of_one_le_left (by positivity)
        (Int.one_le_abs (sub_ne_zero_of_ne hjj'))
    exact separatedBy_annulusRegion_of_gap (c := 2) (r := r) hr1 hr hgap
  · intro j
    exact (measurable_Xcal_annulusRegion_local M s (j * (r : ℤ) + b)).const_mul D⁻¹

/-! ## 2. The `𝒢₂` proportion tail, at the lemma level -/

/-- **The `𝒢₂`-lane proportion tail, in the consumer's shape.**

For every window `{0,…,n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach (closed by the proved
`ratioTail_of_concentration` with no extra hypothesis) —

```
ℙ[ θ < (proportion of scales k ≤ n at which Ev k fails) ] ≤ exp(−c₁ n) / Q .
```

The lane rate is Appendix D's `s' = ¼s`, matching the weight `3^{−¼s(m−j)}` of
the manuscript's row.  `hcube` is the per-cube two-term display and `hnorm` is
the manuscript's constant-selection sentence `e.K.and.p.choices`; both are
discharged at the caller. -/
theorem ratioTail_Xcal (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ)
    {A1 A2 p theta c1 Q : ℝ} {r : ℕ} (Ev : ℤ → Set (Cutoff.CutoffSample d))
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hD : 0 < D) (hp : 1 ≤ p)
    (hs1 : (s : ℝ) ≤ 1) (hsp : 1 ≤ (s : ℝ) / 4 * p)
    (hr1 : 1 ≤ r) (hQ : 1 ≤ Q) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hrate : Real.log (Q * (r : ℝ)) + c1 * (r : ℝ)
      ≤ (s : ℝ) / 4 * p * theta / (16 * (r : ℝ)))
    (hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2)
    (hnorm : gammaMomentConst 1 * p * xcalScaleOne d (s : ℝ) A1 +
      gammaMomentConst (1 / 4) * p ^ (4 : ℝ) * xcalScaleQuarter d (s : ℝ) A2 ≤ D)
    (hrgap : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    (hreduce : ∀ m : ℤ, 0 ≤ m → ∀ omega ∈ (Ev m)ᶜ,
      9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) <
        Yk (xcalArray M s D) ((s : ℝ) / 4) m omega)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  classical
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs40 : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have hs41 : (s : ℝ) / 4 ≤ 1 := by linarith only [hs1, hs0]
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  have hmomL := lintegral_rpow_le_one_Xcal M s hA1 hA2 hp hD hcube hnorm
  have hindep := columnsIndep_Xcal M s D hr1 hrgap
  have hconc : ∀ Mwin : ℕ, (r : ℤ) ≤ (Mwin : ℤ) →
      (Cutoff.cutoffSampleLaw M).toMeasure
          (concEvent (xcalArray M s D) p ((s : ℝ) / 4) theta Cstar Mwin)
        ≤ ENNReal.ofReal
            (Real.exp (-((s : ℝ) / 4 * p * theta) / (16 * (r : ℝ)) * ((Mwin : ℝ) + 1))) := by
    intro Mwin hMwin
    exact p_concentration_for_scales_Cstar (Cutoff.cutoffSampleLaw M).toMeasure
      (xcalArray M s D) hp hs40 hs41 hsp hr1
      (fun k j => measurable_xcalArray M s D k j)
      (fun k j omega => xcalArray_nonneg M s hD k j omega)
      hmomL hindep Mwin theta hMwin htheta0 htheta1
  exact ratioTail_of_concentration (Cutoff.cutoffSampleLaw M).toMeasure
    (xcalArray M s D) Ev hr1 hQ htheta0 hthetar hc1 hrate hconc hreduce n

end

end Algsuperdiff.Section4.Provider.Proportion
