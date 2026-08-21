/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.G2Concentration
import Algsuperdiff.Section4.Provider.Proportion.G2Arith
import Algsuperdiff.Section4.Provider.Proportion.G2CubeBound
import Algsuperdiff.Section4.Provider.Proportion.RatioTailArith

/-!
# The `𝒢₂` proportion tail with every parameter slot discharged

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E` composed into
`e.no.bad.scales.applied.for.lambdas` for the `𝒢₂` lane.

`G2Concentration.ratioTail_Xcal` is the lemma-level tail with four open slots.
This module closes all four:

* `hcube` — `G2CubeBound.exists_isTwoTermBigOWith_annularErrorObservable`, the
  unconditional per-cube two-term display from the Section 3 anchor;
* `hnorm` — the manuscript's constant-selection sentence `e.K.and.p.choices`,
  discharged at an **explicit** normalizer `D` built from the closed `s`-power
  evaluations of `G2Arith`;
* the rate condition — at an explicit `p`, chosen after `c₁`, so the lane carries
  **no rate ceiling** (contrast the `𝒢₀` lane's `c₁ ≤ γ^{-1}`); this is possible
  because the `𝒢₂` normalizer is paid for by the free parameter `ε` rather than
  by the model's `γ`;
* `hreduce` — `G2RowConversion.hreduce_eventG2` together with the threshold
  identification `RatioTailArith.threshold_le_inv` at the shifted normalizer `D
  s ε^{-2}` (the manuscript's `K₂ε^{−2}` lane prefactor).

## The endpoint

`exists_ratioTail_eventG2` — there are a dependence range `r(d) ≥ 1` and a
dimensional constant `C(d)` such that every model in the printed regime
`γ ≤ C^{−10}c⋆^{10}` obeys, for every `s` in the standing window `[8γ, 1]`, every
level `θ` with `θ(r+1) < 1` and every rate `c₁ ≥ 0`, at an explicit threshold
`ε₀ > 0` and every `ε ≥ ε₀`,

```
ℙ[ θ < proportion of scales k ≤ n at which 𝒢₂(k;s,ε) fails ] ≤ exp(−c₁ n)/3
```

at every window `{0,…,n}` — including the short windows `n < r`.  This is the
`𝒢₂` lane of the three-fold union bound the graph routes
`p.independence.between.scales` through.

The `ε`-threshold form is forced and is the honest one: `𝒢₂(m;s,ε)` grows with
`ε` (`Support.eventG2_subset_of_le`), so a per-lane tail can only hold from a
threshold on, and the threshold is exactly the manuscript's own
`K₂ε^{−2}`-normalization condition solved for `ε`.  It is the `𝒢₂` twin of the
`𝒢₁` lane's `T ≥ T₀`.

## Scope

Provider material: proved local helpers.  The `c⋆^{10}` regime is carried
explicitly, exactly as the anchor states it.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The two per-cube amplitudes of the anchor -/

/-- The `Γ_2`-lane per-cube amplitude produced by the Section 3 anchor through
`G2CubeBound`: `√3·(1+2d log 3)^{1/2}·C c⋆^{−1}s^{−1}√γ`. -/
def cubeAmpOne (d : ℕ) (C : ℝ) (M : ABKModel d) (s : ℝ) : ℝ :=
  Real.sqrt 3 * (annulusPenalty d 2 1 *
    (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma))

/-- The `Γ_{1/2}`-lane per-cube amplitude produced by the Section 3 anchor through
`G2CubeBound`: `√3·(1+2d log 3)²·exp(−C^{−1}c⋆³γ^{−1})`. -/
def cubeAmpTwo (d : ℕ) (C : ℝ) (M : ABKModel d) : ℝ :=
  Real.sqrt 3 * (annulusPenalty d (1 / 2) 1 *
    Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)))

private theorem cubeAmpOne_pos {C : ℝ} (hC : 0 < C) (M : ABKModel d) {s : ℝ} (hs : 0 < s) :
    0 < cubeAmpOne d C M s := by
  have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  rw [cubeAmpOne]
  exact mul_pos h3 (mul_pos hpen
    (mul_pos (mul_pos (mul_pos hC (inv_pos.2 hcs)) (inv_pos.2 hs)) hg))

private theorem cubeAmpTwo_pos (C : ℝ) (M : ABKModel d) : 0 < cubeAmpTwo d C M := by
  have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [cubeAmpTwo]
  exact mul_pos h3 (mul_pos hpen (Real.exp_pos _))

/-! ## 2. The endpoint, at a free admissible dependence range -/

/-- For every model in the manuscript's printed regime `γ ≤ C^{−10}c⋆^{10}` (the
transfer gap, carried explicitly as the anchor states it), every `s` in the
standing window `[8γ, 1]`, every level `θ` with `θ(r+1) < 1` and **every** rate
`c₁ ≥ 0`: there is an explicit threshold `ε₀ > 0` such that for every `ε ≥ ε₀`
and **every** window `{0,…,n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach  —

```
ℙ[ θ < (proportion of scales k ≤ n at which 𝒢₂(k;s,ε) fails) ] ≤ exp(−c₁ n)/3 .
```

Every remaining parameter of the manuscript's proof is discharged inside: the
per-cube two-term display (from the `p.induction.bounds` through
`G2CubeBound`), the closed `s`-power evaluations `s^{−2}` and `s^{−5}` of the
two Step-2 series, the constant-selection sentence `e.K.and.p.choices` at the
explicit `p` and normalizer `D`, the threshold identification, the
`2`-dependence geometry and the `a.s.` finiteness of the Appendix-D row.

There is **no rate ceiling**: `p` is chosen after `c₁`, and the resulting growth
of the normalizer is paid for by the free parameter `ε` rather than by the
model's `γ`.  This is the structural difference from the `𝒢₀` lane, whose atom
scale is pinned to `γ` and which therefore delivers `c₁ ≤ γ^{-1}`. -/
theorem exists_ratioTail_eventG2_of_range (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, 1 ≤ r →
        3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ) →
        ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
          ∀ s : {s : ℝ // 0 < s}, (s : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
            ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
              ∀ c1 : ℝ, 0 ≤ c1 →
                ∃ ep0 : ℝ, 0 < ep0 ∧
                  ∀ ep : ℝ, ep0 ≤ ep → ∀ n : ℕ,
                    (Cutoff.cutoffSampleLaw M).toMeasure
                        {omega | theta < scaleProp
                          (fun k => (Support.eventG2 M k s ep)ᶜ) n omega}
                      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  classical
  obtain ⟨C, hC0, hbounds⟩ := exists_isTwoTermBigOWith_annularErrorObservable d
  refine ⟨C, hC0, ?_⟩
  intro r hr1 hrgap M hreg s hswin theta htheta0 hthetar c1 hc10
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := hswin.2
  have hs40 : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  have hCs0 : (0 : ℝ) < Cstar := Cstar_pos
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  -- the per-cube display, unconditional (the `hcube` slot)
  have hA1 : 0 < cubeAmpOne d C M (s : ℝ) := cubeAmpOne_pos hC0 M hs0
  have hA2 : 0 < cubeAmpTwo d C M := cubeAmpTwo_pos C M
  have hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        (cubeAmpOne d C M (s : ℝ)) (cubeAmpTwo d C M) := by
    intro n
    exact hbounds M hreg (s : ℝ) hswin n
  -- the moment exponent `p`, chosen A the rate `c₁`
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log (3 * (r : ℝ)) + c1 * (r : ℝ) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    have hlog : (0 : ℝ) ≤ Real.log (3 * (r : ℝ)) :=
      Real.log_nonneg (by linarith only [hrR])
    have hcr : (0 : ℝ) ≤ c1 * (r : ℝ) := mul_nonneg hc10 (by linarith only [hrR])
    rw [hLdef]
    linarith only [hlog, hcr]
  obtain ⟨p, hpdef⟩ : ∃ x : ℝ, x =
      max 1 (max (4 / (s : ℝ)) (64 * (r : ℝ) * L / ((s : ℝ) * theta))) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hpdef]; exact le_max_left _ _
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hp4s : 4 / (s : ℝ) ≤ p := by
    rw [hpdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hprate : 64 * (r : ℝ) * L / ((s : ℝ) * theta) ≤ p := by
    rw [hpdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hsp : 1 ≤ (s : ℝ) / 4 * p := by
    have hstep := mul_le_mul_of_nonneg_left hp4s hs40.le
    have hone : (s : ℝ) / 4 * (4 / (s : ℝ)) = 1 := by field_simp
    rwa [hone] at hstep
  have hrate : Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)
      ≤ (s : ℝ) / 4 * p * theta / (16 * (r : ℝ)) := by
    have hst : (0 : ℝ) < (s : ℝ) * theta := mul_pos hs0 htheta0
    have hstep : 64 * (r : ℝ) * L / ((s : ℝ) * theta) * ((s : ℝ) * theta / 4)
        ≤ p * ((s : ℝ) * theta / 4) :=
      mul_le_mul_of_nonneg_right hprate (by positivity)
    have hval : 64 * (r : ℝ) * L / ((s : ℝ) * theta) * ((s : ℝ) * theta / 4)
        = 16 * (r : ℝ) * L := by
      field_simp
      ring
    rw [← hLdef, le_div_iff₀ (by linarith only [hrR] : (0 : ℝ) < 16 * (r : ℝ))]
    calc L * (16 * (r : ℝ)) = 16 * (r : ℝ) * L := by ring
      _ ≤ p * ((s : ℝ) * theta / 4) := by rw [← hval]; exact hstep
      _ = (s : ℝ) / 4 * p * theta := by ring
  -- the normalizer `D`, at the closed `s`-power evaluations (the `hnorm` slot)
  obtain ⟨D, hDdef⟩ : ∃ x : ℝ, x =
      gammaMomentConst 1 * p *
          (gammaTriangleConst (1 : ℝ) *
            (xcalNormOne d / (s : ℝ) ^ (2 : ℕ) * (2 * cubeAmpOne d C M (s : ℝ) ^ 2))) +
        gammaMomentConst (1 / 4) * p ^ (4 : ℝ) *
          (gammaTriangleConst (1 / 4 : ℝ) *
            (xcalNormQuarter d / (s : ℝ) ^ (5 : ℕ) *
              (2 * cubeAmpTwo d C M ^ 2))) := ⟨_, rfl⟩
  have hprpow : (0 : ℝ) < p ^ (4 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hD0 : 0 < D := by
    rw [hDdef]
    refine add_pos (mul_pos (mul_pos hgmc1 hp0) (mul_pos hgtc1 ?_))
      (mul_pos (mul_pos hgmc4 hprpow) (mul_pos hgtc4 ?_))
    · exact mul_pos (div_pos (xcalNormOne_pos d) (pow_pos hs0 2))
        (mul_pos two_pos (pow_pos hA1 2))
    · exact mul_pos (div_pos (xcalNormQuarter_pos d) (pow_pos hs0 5))
        (mul_pos two_pos (pow_pos hA2 2))
  have hnorm : gammaMomentConst 1 * p * xcalScaleOne d (s : ℝ) (cubeAmpOne d C M (s : ℝ)) +
      gammaMomentConst (1 / 4) * p ^ (4 : ℝ) *
        xcalScaleQuarter d (s : ℝ) (cubeAmpTwo d C M) ≤ D := by
    rw [hDdef]
    refine add_le_add
      (mul_le_mul_of_nonneg_left (xcalScaleOne_le d hs0 hs1)
        (mul_nonneg hgmc1.le hp0.le))
      (mul_le_mul_of_nonneg_left (xcalScaleQuarter_le d hs0 hs1)
        (mul_nonneg hgmc4.le hprpow.le))
  -- the null set of the enlargement
  have hnull : (Cutoff.cutoffSampleLaw M).toMeasure (goodRowSetG2 M s)ᶜ = 0 :=
    measure_compl_goodRowSetG2 M s hs1 hcube
  -- the `ε`-threshold (the threshold identification, `𝒢₂` form)
  obtain ⟨ep0, hep0def⟩ : ∃ x : ℝ, x = Real.sqrt (36 * (1 + Cstar) * D / theta) := ⟨_, rfl⟩
  have hrad0 : (0 : ℝ) < 36 * (1 + Cstar) * D / theta := by
    refine div_pos ?_ htheta0
    exact mul_pos (mul_pos (by norm_num) (by linarith only [hCs0])) hD0
  have hep00 : 0 < ep0 := by rw [hep0def]; exact Real.sqrt_pos.2 hrad0
  refine ⟨ep0, hep00, ?_⟩
  intro ep hepge n
  have hep : 0 < ep := lt_of_lt_of_le hep00 hepge
  have hep2 : (0 : ℝ) < ep ^ 2 := pow_pos hep 2
  have hep0sq : ep0 ^ 2 = 36 * (1 + Cstar) * D / theta := by
    rw [hep0def]
    exact Real.sq_sqrt hrad0.le
  have hsqle : 36 * (1 + Cstar) * D / theta ≤ ep ^ 2 := by
    rw [← hep0sq]
    exact pow_le_pow_left₀ hep00.le hepge 2
  have hbase : 36 * (1 + Cstar) * D ≤ theta * ep ^ 2 := by
    rw [div_le_iff₀ htheta0] at hsqle
    linarith only [hsqle]
  have hDp0 : (0 : ℝ) < D * (s : ℝ) / ep ^ 2 := div_pos (mul_pos hD0 hs0) hep2
  have hkeythr : 9 * (D * (s : ℝ) / ep ^ 2) * (1 + Cstar) ≤ (s : ℝ) / 4 * theta := by
    have hrw : 9 * (D * (s : ℝ) / ep ^ 2) * (1 + Cstar)
        = 9 * D * (1 + Cstar) * (s : ℝ) / ep ^ 2 := by ring
    rw [hrw, div_le_iff₀ hep2]
    calc 9 * D * (1 + Cstar) * (s : ℝ) = (s : ℝ) / 4 * (36 * (1 + Cstar) * D) := by ring
      _ ≤ (s : ℝ) / 4 * (theta * ep ^ 2) :=
          mul_le_mul_of_nonneg_left hbase (by linarith only [hs0])
      _ = (s : ℝ) / 4 * theta * ep ^ 2 := by ring
  have hthr0 := threshold_le_inv (sprime := (s : ℝ) / 4) (theta := theta) (p := p)
    hs40 htheta0 htheta1 hp1 hDp0 hkeythr
  have hinv : (D * (s : ℝ) / ep ^ 2)⁻¹ = D⁻¹ * (ep ^ 2 / (s : ℝ)) := by
    field_simp
  rw [hinv] at hthr0
  -- the assembled tail for the enlarged family
  have hmain := ratioTail_Xcal M s D
    (fun k => Support.eventG2 M k s ep ∪ (goodRowSetG2 M s)ᶜ)
    hA1 hA2 hD0 hp1 hs1 hsp hr1 (by norm_num : (1 : ℝ) ≤ 3) htheta0 hthetar hc10
    hrate hcube hnorm hrgap (hreduce_eventG2 M s hD0 hthr0)
  exact le_trans (measure_scaleProp_le_of_null_enlargement _ _ _ hnull n) (hmain n)

/-- **The `𝒢₂` lane endpoint, in the display shape of the `𝒢₀` and `𝒢₁` lanes.**

The `∃ r` form of `exists_ratioTail_eventG2_of_range`, at the dependence range
`RatioTailArith.exists_dependence_range` produces — the very same producer the
`𝒢₀` lane uses, so the two lanes run at the same `r(d)`.  (The three-fold union
bound does not in fact need the ranges to agree: the level condition
`θ(r+1) < 1` at the larger range implies it at the smaller.) -/
theorem exists_ratioTail_eventG2 (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, (s : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
          ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
            ∀ c1 : ℝ, 0 ≤ c1 →
              ∃ ep0 : ℝ, 0 < ep0 ∧
                ∀ ep : ℝ, ep0 ≤ ep → ∀ n : ℕ,
                  (Cutoff.cutoffSampleLaw M).toMeasure
                      {omega | theta < scaleProp
                        (fun k => (Support.eventG2 M k s ep)ᶜ) n omega}
                    ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  obtain ⟨r, hr1, hrgap⟩ := exists_dependence_range d
  obtain ⟨C, hC0, h⟩ := exists_ratioTail_eventG2_of_range d
  exact ⟨r, hr1, C, hC0, h r hr1 hrgap⟩

end

end Algsuperdiff.Section4.Provider.Proportion
