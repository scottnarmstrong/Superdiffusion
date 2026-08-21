/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.Ycal
import Algsuperdiff.Section4.Probability.IndicatorArray
import Algsuperdiff.Section4.Probability.IndicatorDensityTails
import Algsuperdiff.Section4.Probability.AnnulusSeparation

/-!
# The `𝒢₀` lane: unit moments, `r`-dependence, and the proportion tail

ABK26, §4.1, `l.good.scales.ratio.lambda`, the moment and `p` choice,
the two-dependence step and the display `e.no.bad.scales.applied.for.lambdas`.

Accordingly the endpoint delivered here is the un-weakened concentration output
in the proved `ratioTail_of_concentration` shape.

## What is assembled

1. **`lintegral_rpow_le_one_Ycal`** — the Appendix-D moment hypothesis
   `E[(D^{-1}𝒴_n)^p] ≤ 1` from the `𝒴`-tail, via the proved `IndicatorArray`
   discharger.  This is's "by taking `p := exp(K^{-1}c⋆²γ^{-1})` with `K(d)`
   large enough, we obtain `E[𝒴_n^p] ≤ 1`"; the numerical step of that sentence
   is the hypothesis `hnorm` (`gammaMomentConst σ · p^{1/σ} · K ≤ D`), which is
   exactly the manuscript's own "for `K(d)` large enough".

2. **`columnsIndep_Ycal`** — the `2`-dependence assertion, at the honest
   `r(d)`.  The theorem below is stated at the **general `r`**, so no dimension
   restriction enters this file; `d ≤ 81` gives `r = 2`
   (`separatedBy_annulusRegion_two`), and larger `d` is covered by
   `separatedBy_annulusRegion_of_gap` at the larger `r(d)`.  The cost of `r >
   2` is absorbed in the rate.

3. **`ratioTail_Ycal`** — the per-lane proportion tail in the consumer's shape,
   assembled from 1, 2, the proved `p_concentration_for_scales_Cstar` and the
   proved `ratioTail_of_concentration` (which also closes the short-window gap
   with no extra hypothesis).

## The two frontier slots

* `hloc` — the locality of `𝒴_n` for `cutoffSampleLocalSigma M (n−2) (annulus
  n)`.  `measurable_Ycal_local` reduces it to the per-cube statement, which in
  turn needs an in-repo lemma that does not exist: the local-sigma
  measurability of the `λ_{γ,2}^{-1}` literal read at a T cube.  What is proved
  is
  `Provider.BadEvents.measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal`
  at a general `TriadicCube`, and
  `Cutoff.coefficientCutoff_translateCutoffSample`; the missing bridge is the
  identification of the translated-sample read with the translated-cube read.
  Reported as a frontier, not smuggled.
* `hreduce` — the deterministic reduction of the bad event `(Ev m)ᶜ` into the
  Appendix-D threshold event.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
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

/-- **The Appendix-D array of the `𝒢₀` lane**, `X_{k,n} = D^{-1}𝒴_n`.  The
normalizer `D` carries the manuscript's `γ^{-4}`. -/
def ycalArray (M : ABKModel d) (Ccg sprime D : ℝ) :
    ℤ → ℤ → Cutoff.CutoffSample d → ℝ :=
  colArray fun n omega => D⁻¹ * Ycal M Ccg sprime n omega

@[simp] theorem ycalArray_apply (M : ABKModel d) (Ccg sprime D : ℝ) (k j : ℤ)
    (omega : Cutoff.CutoffSample d) :
    ycalArray M Ccg sprime D k j omega = D⁻¹ * Ycal M Ccg sprime j omega := rfl

/-! ## 1. The Appendix-D unit moments -/

/-- **`E[(D^{-1}𝒴_n)^p] ≤ 1`.**  The Appendix-D moment hypothesis
`e.Xk.p.moment.twosided`, in its honest `∫⁻` reading, for the column array of
the `𝒴`-atoms.

`hnorm` is the manuscript's own numerical step: at `σ = 1/3` the moment growth
is `gammaMomentConst σ · p³ · K` makes it `≤ 1` "by taking `p:=
exp(K^{-1}c⋆²γ^{-1})` with `K(d)` large enough" — i.e. by the smallness of the
tail scale `K` against `p³`. -/
theorem lintegral_rpow_le_one_Ycal (M : ABKModel d) (Ccg : ℝ) {sigma sprime p D K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) (hp : 1 ≤ p) (hD : 0 < D)
    (htail : ∀ n : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n) K)
    (hnorm : gammaMomentConst sigma * p ^ sigma⁻¹ * K ≤ D) :
    ∀ k j : ℤ, ∫⁻ omega,
        ENNReal.ofReal ((ycalArray M Ccg sprime D k j omega) ^ p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ 1 :=
  colArray_lintegral_rpow_le_one hsigma hK hp hD
    (fun j omega => Ycal_nonneg M Ccg sprime j omega)
    (fun j => (measurable_Ycal M Ccg sprime j).aemeasurable) htail hnorm

/-! ## 2. Locality of `𝒴_n`, reduced to the per-cube statement -/

/-- **The `𝒴`-locality reduces to the per-cube locality.**  `𝒴_n` is an
`ℝ≥0∞`-series of `0`-floored maxima of the `𝒢₀` bracket over centres of the
annulus at spacings `3^{k−2}`, `k ≤ n`; each such read cube is inside
`annulusRegion d n` and each truncation level `k − 2` is at or below `n − 2`
(`AnnulusSeparation.mem_annulusRegion_of_le_triadicLatticePoint` is the
no-enlargement fact).  So the whole series stays in the single sigma-field
`cutoffSampleLocalSigma M (n−2) (annulusRegion d n)`, provided each bracket
does. -/
theorem measurable_Ycal_local (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ)
    (hatomloc : ∀ k : ℤ, k ≤ n → ∀ v : Fin d → ℤ,
      Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
        (fun omega => Localize.cgExcess M Ccg (k - 2)
          (Support.triadicLatticePoint (k - 2) v) omega)) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
      (Ycal M Ccg sprime n) := by
  refine @measurable_wsum (Cutoff.CutoffSample d)
    (Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)) _ _ ?_
  intro j
  exact @measurable_fmax (Cutoff.CutoffSample d)
    (Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)) (Fin d → ℤ) _ _
    (fun v => hatomloc (n - (j : ℤ)) (by omega) v)

/-! ## 3. `r`-dependence of the `𝒴_n` -/

/-- **The Appendix-D independence hypothesis `e.independent.columns.twosided` for
the `𝒢₀` lane.**

The atoms `𝒴_n` are `r`-dependent for every `r ≥ 1` with
`3 + 2·3^{1−2}√d ≤ 3^r`, i.e. `3 + (2/3)√d ≤ 3^r`: the annuli at index gap `≥ r`
are separated at the shared-shell threshold `√d·3^{min(n−2, n'−2)}`, which is
exactly what the varying-level producer consumes.  No dimension restriction is
imposed here — `r` is a parameter, and `d ≤ 81` gives the manuscript's `r = 2`
(`Probability.three_add_two_thirds_sqrt_le_nine`). -/
theorem columnsIndep_Ycal (M : ABKModel d) (Ccg sprime D : ℝ) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    (hloc : ∀ n : ℤ,
      Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
        (Ycal M Ccg sprime n)) :
    ColumnsIndep (Cutoff.cutoffSampleLaw M).toMeasure (ycalArray M Ccg sprime D) r := by
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
    exact (hloc (j * (r : ℤ) + b)).const_mul D⁻¹

/-! ## 4. The proportion tail (`e.no.bad.scales.applied.for.lambdas`) -/

/-- **The `𝒢₀`-lane proportion tail, in the consumer's shape.**

For every window `{0,…,n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach (closed by the proved
`ratioTail_of_concentration` with no extra hypothesis) —

```
ℙ[ θ < (proportion of scales k ≤ n at which Ev k fails) ] ≤ exp(−c₁ n) / Q .
```

This is `e.no.bad.scales.applied.for.lambdas` after the rate shaping of the
proved `IndicatorDensityTails`, and it is the un-weakened output the graph
routes the §4.1 conclusion through.

The event family `Ev` and its reduction `hreduce` into the Appendix-D threshold
event are the caller's: `hreduce` is the deterministic score-domination chain
together with the threshold identification. -/
theorem ratioTail_Ycal (M : ABKModel d) (Ccg sprime D : ℝ)
    {sigma p theta c1 Q K : ℝ} {r : ℕ} (Ev : ℤ → Set (Cutoff.CutoffSample d))
    (hsigma : 0 < sigma) (hK : 0 < K) (hD : 0 < D)
    (hp : 1 ≤ p) (hs' : 0 < sprime) (hs'1 : sprime ≤ 1) (hsp : 1 ≤ sprime * p)
    (hr1 : 1 ≤ r) (hQ : 1 ≤ Q) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hrate : Real.log (Q * (r : ℝ)) + c1 * (r : ℝ) ≤ sprime * p * theta / (16 * (r : ℝ)))
    (htail : ∀ n : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n) K)
    (hnorm : gammaMomentConst sigma * p ^ sigma⁻¹ * K ≤ D)
    (hrgap : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    (hloc : ∀ n : ℤ,
      Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
        (Ycal M Ccg sprime n))
    (hreduce : ∀ m : ℤ, 0 ≤ m → ∀ omega ∈ (Ev m)ᶜ,
      9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) <
        Yk (ycalArray M Ccg sprime D) sprime m omega)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  classical
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  have hXmeas : ∀ k j : ℤ, Measurable (ycalArray M Ccg sprime D k j) := by
    intro _k j
    exact (measurable_Ycal M Ccg sprime j).const_mul D⁻¹
  have hXnn : ∀ (k j : ℤ) (omega : Cutoff.CutoffSample d),
      0 ≤ ycalArray M Ccg sprime D k j omega := by
    intro _k j omega
    exact mul_nonneg (inv_nonneg.2 hD.le) (Ycal_nonneg M Ccg sprime j omega)
  have hmomL := lintegral_rpow_le_one_Ycal M Ccg hsigma hK hp hD htail hnorm
  have hindep := columnsIndep_Ycal M Ccg sprime D hr1 hrgap hloc
  have hconc : ∀ Mwin : ℕ, (r : ℤ) ≤ (Mwin : ℤ) →
      (Cutoff.cutoffSampleLaw M).toMeasure
          (concEvent (ycalArray M Ccg sprime D) p sprime theta Cstar Mwin)
        ≤ ENNReal.ofReal
            (Real.exp (-(sprime * p * theta) / (16 * (r : ℝ)) * ((Mwin : ℝ) + 1))) := by
    intro Mwin hMwin
    exact p_concentration_for_scales_Cstar (Cutoff.cutoffSampleLaw M).toMeasure
      (ycalArray M Ccg sprime D)
      hp hs' hs'1 hsp hr1 hXmeas hXnn hmomL hindep Mwin theta hMwin htheta0 htheta1
  exact ratioTail_of_concentration (Cutoff.cutoffSampleLaw M).toMeasure
    (ycalArray M Ccg sprime D) Ev hr1 hQ htheta0 hthetar hc1 hrate hconc hreduce n

end

end Algsuperdiff.Section4.Provider.Proportion
