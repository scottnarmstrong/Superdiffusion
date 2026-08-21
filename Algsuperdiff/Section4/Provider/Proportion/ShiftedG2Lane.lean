/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.G2RatioTail
import Algsuperdiff.Section4.Provider.Proportion.ShiftedConcentration

/-!
# The `𝒢₂` proportion lane re-based at an arbitrary scale `m₀`

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E`, composed into
`e.no.bad.scales.applied.for.lambdas` and read on the window `{m₀,…,m₀+n}`
rather than on `{0,…,n}`.

The proved `𝒢₂` lane is stated at base `0`: its window is the `Finset.Icc (0:ℤ)
(n:ℤ)` inside `IndicatorDensity.scaleProp`.  The manuscript's own reduction of
the general window to that one is "translate the array", carried out once and
generically in `ShiftedConcentration`.  This module runs the `𝒢₂` lane through
that translation.

## Contents

* `ratioTail_Xcal_shift` — the `𝒢₂` lemma-level tail on `{m₀,…,m₀+n}`.  Its
  hypothesis list is the proved `G2Concentration.ratioTail_Xcal` one, with the
  base `m₀` added and the deterministic reduction asked at **every** scale `m:
  ℤ` instead of only at `m ≥ 0`.
* `hreduce_eventG2_all` — the proved `G2RowConversion.hreduce_eventG2` with its
  unused sign binder dropped, so that it can be instantiated at a negative
  scale.
* `exists_ratioTail_eventG2_of_range_shift` and `exists_ratioTail_eventG2_shift`
  — the two endpoint shapes of `G2RatioTail`, with the base `m₀` and the window
  `n` both quantified **last**, after `ε`: neither the dimensional constant `C`,
  nor the dependence range `r`, nor the threshold `ε₀` depends on the base.

## Scope

Provider material: proved local helpers.  The parameter package of the proved
endpoint is constructed inside a closed existential and is not exposed, so the
index-free parameter arithmetic of `exists_ratioTail_eventG2_of_range` is
reproduced here rather than reused.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`; `p.concentration.for.scales`.
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

/-! ## 1. The `𝒢₂` lemma-level tail on the window `{m₀,…,m₀+n}` -/

/-- **The `𝒢₂`-lane proportion tail at an arbitrary base scale `m₀`.**

For every window `{m₀,…,m₀+n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach (closed by the proved
`ratioTail_of_concentration` with no extra hypothesis) —

```
ℙ[ θ < (proportion of scales m₀+k, k ≤ n, at which Ev fails) ] ≤ exp(−c₁ n) / Q .
```

This is `G2Concentration.ratioTail_Xcal` with the base added: the same
hypothesis list, except that the deterministic reduction is asked at every scale
`m : ℤ` rather than only at `m ≥ 0`, which is what the lane in fact proves.  The
translation of the Appendix-D array is `ratioTail_of_concentration_shift`. -/
theorem ratioTail_Xcal_shift (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ)
    {A1 A2 p theta c1 Q : ℝ} {r : ℕ} (Ev : ℤ → Set (Cutoff.CutoffSample d)) (m0 : ℤ)
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
    (hreduce : ∀ m : ℤ, ∀ omega ∈ (Ev m)ᶜ,
      9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) <
        Yk (xcalArray M s D) ((s : ℝ) / 4) m omega)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev (m0 + k))ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  classical
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs40 : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have hs41 : (s : ℝ) / 4 ≤ 1 := by linarith only [hs1, hs0]
  have hmomL := lintegral_rpow_le_one_Xcal M s hA1 hA2 hp hD hcube hnorm
  have hindep := columnsIndep_Xcal M s D hr1 hrgap
  exact ratioTail_of_concentration_shift (Cutoff.cutoffSampleLaw M).toMeasure
    (xcalArray M s D) Ev m0 hp hs40 hs41 hsp hr1
    (fun k j => measurable_xcalArray M s D k j)
    (fun k j omega => xcalArray_nonneg M s hD k j omega)
    hmomL hindep hQ htheta0 hthetar hc1 hrate hreduce n

/-! ## 2. The reduction at every scale -/

/-- **The `hreduce` slot of the `𝒢₂` concentration assembly, for the enlarged
family, at every scale.**

This is the proved `G2RowConversion.hreduce_eventG2` with its **unused** sign
binder `0 ≤ m` dropped: that binder is never consumed by the proved proof, but
a caller must nonetheless supply it, so the proved form cannot be instantiated
at a negative scale.  The proof runs on the public, sign-condition-free
`G2RowConversion.lt_Yk_of_notMem_eventG2`.

`hthr` is the lane's threshold identification: the Appendix-D level
`9 s'^{-1}C_⋆^{1/p}θ^{-1/p}` at `s' = ¼s` must sit below `D^{-1}ε²s^{-1}`. -/
theorem hreduce_eventG2_all (M : ABKModel d) (s : {s : ℝ // 0 < s}) {ep p theta D : ℝ}
    (hD : 0 < D)
    (hthr : 9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      ≤ D⁻¹ * (ep ^ 2 / (s : ℝ)))
    (m : ℤ) (omega : Cutoff.CutoffSample d)
    (homega : omega ∈ (Support.eventG2 M m s ep ∪ (goodRowSetG2 M s)ᶜ)ᶜ) :
    9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      < Yk (xcalArray M s D) ((s : ℝ) / 4) m omega := by
  have h1 : omega ∉ Support.eventG2 M m s ep := fun hc => homega (Or.inl hc)
  have h2 : omega ∈ goodRowSetG2 M s := by
    by_contra hc
    exact homega (Or.inr hc)
  exact lt_of_le_of_lt hthr (lt_Yk_of_notMem_eventG2 M s hD m h2 h1)

/-! ## 3. The endpoint on `{m₀,…,m₀+n}`, at a free admissible dependence range -/

private theorem cubeAmpOne_pos' {C : ℝ} (hC : 0 < C) (M : ABKModel d) {s : ℝ} (hs : 0 < s) :
    0 < cubeAmpOne d C M s := by
  have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  rw [cubeAmpOne]
  exact mul_pos h3 (mul_pos hpen
    (mul_pos (mul_pos (mul_pos hC (inv_pos.2 hcs)) (inv_pos.2 hs)) hg))

private theorem cubeAmpTwo_pos' (C : ℝ) (M : ABKModel d) : 0 < cubeAmpTwo d C M := by
  have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [cubeAmpTwo]
  exact mul_pos h3 (mul_pos hpen (Real.exp_pos _))

/-- `r` is a free parameter here, constrained only by the honest count `3
+ (2/3)√d ≤ 3^r`.

For every model in the manuscript's printed regime `γ ≤ C^{−10}c⋆^{10}` (the
transfer gap, carried explicitly as the anchor states it), every `s` in the
standing window `[8γ, 1]`, every level `θ` with `θ(r+1) < 1` and **every** rate
`c₁ ≥ 0`: there is an explicit threshold `ε₀ > 0` such that for every `ε ≥ ε₀`,
**every** base scale `m₀ : ℤ` and **every** window `{m₀,…,m₀+n}` — including
the short windows `n < r` that `p.concentration.for.scales` does not reach  —

```
ℙ[ θ < (proportion of scales m₀+k, k ≤ n, at which 𝒢₂ fails) ] ≤ exp(−c₁ n)/3 .
```

The base `m₀` and the window `n` are quantified **last**, after `ε`: neither `C`
nor `ε₀` depends on the base, which is what a consumer running the union bound
over a moving window needs.

There is **no rate ceiling**: `p` is chosen after `c₁`, and the resulting growth
of the normalizer is paid for by the free parameter `ε` rather than by the
model's `γ`. -/
theorem exists_ratioTail_eventG2_of_range_shift (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, 1 ≤ r →
        3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ) →
        ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
          ∀ s : {s : ℝ // 0 < s}, (s : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
            ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
              ∀ c1 : ℝ, 0 ≤ c1 →
                ∃ ep0 : ℝ, 0 < ep0 ∧
                  ∀ ep : ℝ, ep0 ≤ ep → ∀ (m0 : ℤ) (n : ℕ),
                    (Cutoff.cutoffSampleLaw M).toMeasure
                        {omega | theta < scaleProp
                          (fun k => (Support.eventG2 M (m0 + k) s ep)ᶜ) n omega}
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
  have hA1 : 0 < cubeAmpOne d C M (s : ℝ) := cubeAmpOne_pos' hC0 M hs0
  have hA2 : 0 < cubeAmpTwo d C M := cubeAmpTwo_pos' C M
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
  intro ep hepge m0 n
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
  -- the assembled tail for the enlarged family, at the base `m₀`
  have hmain := ratioTail_Xcal_shift M s D
    (fun k => Support.eventG2 M k s ep ∪ (goodRowSetG2 M s)ᶜ) m0
    hA1 hA2 hD0 hp1 hs1 hsp hr1 (by norm_num : (1 : ℝ) ≤ 3) htheta0 hthetar hc10
    hrate hcube hnorm hrgap (hreduce_eventG2_all M s hD0 hthr0)
  refine le_trans (measure_scaleProp_le_of_null_enlargement
    (Cutoff.cutoffSampleLaw M).toMeasure (fun k => Support.eventG2 M (m0 + k) s ep)
    ((goodRowSetG2 M s)ᶜ) hnull n) ?_
  exact hmain n

/-- **The `𝒢₂` lane endpoint on `{m₀,…,m₀+n}`, in the display shape of the `𝒢₀`
and `𝒢₁` lanes.**

The `∃ r` form of `exists_ratioTail_eventG2_of_range_shift`, at the dependence
range `RatioTailArith.exists_dependence_range` produces — the very same producer
the base-`0` lanes use, so all the lanes run at the same `r(d)`. -/
theorem exists_ratioTail_eventG2_shift (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, (s : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
          ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
            ∀ c1 : ℝ, 0 ≤ c1 →
              ∃ ep0 : ℝ, 0 < ep0 ∧
                ∀ ep : ℝ, ep0 ≤ ep → ∀ (m0 : ℤ) (n : ℕ),
                  (Cutoff.cutoffSampleLaw M).toMeasure
                      {omega | theta < scaleProp
                        (fun k => (Support.eventG2 M (m0 + k) s ep)ᶜ) n omega}
                    ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  obtain ⟨r, hr1, hrgap⟩ := exists_dependence_range d
  obtain ⟨C, hC0, h⟩ := exists_ratioTail_eventG2_of_range_shift d
  exact ⟨r, hr1, C, hC0, h r hr1 hrgap⟩

end

end Algsuperdiff.Section4.Provider.Proportion
