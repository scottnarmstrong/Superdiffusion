/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.RowSumFinite
import Algsuperdiff.Section4.Provider.Proportion.RatioTailArith
import Algsuperdiff.Section4.Provider.Proportion.TranslatedLocality

/-!
# The `𝒢₀` proportion tail with every parameter slot discharged

ABK26, §4.1, `e.no.bad.scales.applied.for.lambdas` for the `𝒢₀` lane.

`Concentration.ratioTail_Ycal` is the lemma-level tail with five open slots.
`TranslatedLocality` closed `hloc`; `RowSumFinite` closed `hreduce` modulo the
threshold identification; `RatioTailArith` carries the abstract-real parameter
arithmetic.  This module composes them:

* `exists_cgExcess_atomTail_of_floor` — **the anchor `s`-window** (`hwin` of
  `AtomTail.exists_cgExcess_atomTail`): `exp(−(C_cg^{−1}E^{−2}γ^{−1})) ≤ γ/2` at
  the budget `E = C c⋆^{−1}`, from the printed regime `γ ≤ C^{−10}c⋆^{10}` for
  `C(d)` large; the per-atom `Γ_{1/3}` tail becomes unconditional.
* `exists_ratioTail_eventG0` — the endpoint, with **the `p`-choice** (`p:=
  exp(K(d)^{−1}c⋆²γ^{−1})` at `K(d) = 6 C_cg C²`, so that `p^{1/σ}` eats
  exactly half of the atom scale), **the `γ^{-4}` normalizer** and **the
  threshold identification** all discharged.

## The endpoint

`exists_ratioTail_eventG0` — for every dimension there is a dependence range
`r(d) ≥ 1` such that for **every** level `θ` with `θ(r+1) < 1` there is a constant
`C(d,θ)` for which every model in the printed regime `γ ≤ C^{−10}c⋆^{10}` obeys,
for every window `{0,…,n}` and every rate `c₁ ∈ [0, γ^{-1}]`,

```
ℙ[ θ < proportion of scales k ≤ n at which 𝒢₀(k) fails ] ≤ exp(−c₁ n)/3 .
```

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

/-! ## 4. The two `AtomTail` bridges -/

variable {d : ℕ}

private theorem exp_le_budget (M : ABKModel d) {C : ℝ} {E : {E : ℝ // 1 ≤ E}}
    (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hCfloor : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ C) :
    Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ (E : ℝ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hcsinv : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcs0]
    calc Disorder.cstar M ≤ 3 / 2 := hcs
      _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
  have hstep : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    GoodEvents.mul_cstarInv_le_of_budget M hEval hCfloor
  have hlow : Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ))
      ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
        (Disorder.cstar M)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hcsinv
      (by positivity :
        (0 : ℝ) ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
    calc Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ))
        = 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) * (2 / 3) := by
          ring
      _ ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
            (Disorder.cstar M)⁻¹ := h
  exact le_trans hlow hstep

private theorem atomTail_of_budget (M : ABKModel d) {C : ℝ} {E : {E : ℝ // 1 ≤ E}}
    (hC1 : 1 ≤ C) (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hEreg : M.gamma ≤ (((E : ℝ))⁻¹) ^ 10)
    (hall : ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E)
    (hexpE : Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ (E : ℝ))
    (hwin : cgTailScale M (E : ℝ) ≤ M.gamma / 2) (k : ℤ) (z : Vec d) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (fun omega =>
        Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
      (cgTailScale M (E : ℝ)) := by
  have hEwindow := GoodEvents.coarseEllipticityBudget M hEval hC1 hEreg hall hexpE (k - 2)
  refine isBigOWith_cgExcess_of_state M k z ?_ hEwindow.2.1 hEwindow.2.2 hwin
  have hidx : k - 2 - 1 = k - 3 := by ring
  rw [hidx] at hEwindow
  exact hEwindow.1

/-! ## 5b. SLOT: the anchor's `s`-window at `s = γ`, discharged -/

/-- **The `𝒢₀` atom tail, unconditionally, at any floor the caller needs.**

`AtomTail.exists_cgExcess_atomTail` delivers the per-atom `Γ_{1/3}` tail only
under the anchor's own `s`-window premise `hwin: exp(−(C_cg^{−1}E^{−2}γ^{−1}))
≤ γ/2`, which it passes through as a caller obligation.  That premise is the
manuscript's own step and it is discharged here from the printed regime `γ ≤
C^{−10}c⋆^{10}` alone:

* at the budget `E = C c⋆^{−1}` the exponent is `u = c⋆²/(C_cg C² γ)`, and the
  regime with the proved `c⋆ ≤ 3/2` gives `C⁶ ≤ 12 C_cg² γu²` (`regime_core`);
* the floor `C ≥ 6912 C_cg²` therefore gives `γu² ≥ 576`, and
  `exp(−u) ≤ 2/u² ≤ γ/2` (`exp_neg_le_two_div_sq`).

The extra floor is free for the caller (the `p`-choice needs its own). -/
theorem exists_cgExcess_atomTail_of_floor (d : ℕ) (C0 : ℝ) :
    ∃ C : ℝ, 6 ≤ C ∧ C0 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E}, (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
          cgTailScale M (E : ℝ) ≤ M.gamma / 2 ∧
            ∀ (k : ℤ) (z : Vec d),
              IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
                (fun omega =>
                  Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
                (cgTailScale M (E : ℝ)) := by
  classical
  have hCcg0 : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  obtain ⟨fl, hfldef⟩ : ∃ x : ℝ, x = max C0
      (max (3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
        (6912 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ))) := ⟨_, rfl⟩
  obtain ⟨C, hC6, hCfl, hall⟩ := GoodEvents.exists_allScalesInductionState_ge d fl
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC6]
  have hC0' : (0 : ℝ) < C := by linarith only [hC6]
  have hCpow : C ≤ C ^ (6 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (6 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hflC0 : C0 ≤ C := by
    refine le_trans ?_ hCfl
    rw [hfldef]
    exact le_max_left _ _
  have hfl1 : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ C := by
    refine le_trans ?_ hCfl
    rw [hfldef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hfl2 : 6912 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) ≤ C ^ (6 : ℕ) := by
    refine le_trans ?_ (le_trans hCfl hCpow)
    rw [hfldef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC6, hflC0, ?_⟩
  intro M hreg
  obtain ⟨E, hEval, hEreg, hstate⟩ := hall M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  obtain ⟨u, hudef⟩ : ∃ x : ℝ, x = (Support.cgEllipLowerConstant d)⁻¹ *
      (((E : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hudef]
    exact mul_pos (mul_pos (inv_pos.2 hCcg0) (pow_pos (inv_pos.2 hE0) 2)) (inv_pos.2 hg0)
  have hAu : cgTailScale M (E : ℝ) = Real.exp (-u) := by rw [hudef, cgTailScale]
  obtain ⟨hcore1, -, -⟩ :=
    regime_core (u := u) hg0 hcs0 hcs32 hCcg0 hC0' hreg (by rw [hudef, hEval])
  have hpos : (0 : ℝ) < 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) :=
    mul_pos (by norm_num) (pow_pos hCcg0 2)
  have hgu : (576 : ℝ) ≤ M.gamma * u ^ (2 : ℕ) := by
    have hchain : 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (576 : ℝ)
        ≤ 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (M.gamma * u ^ (2 : ℕ)) := by
      calc 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (576 : ℝ)
          = 6912 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) := by ring
        _ ≤ C ^ (6 : ℕ) := hfl2
        _ ≤ 12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (M.gamma * u ^ (2 : ℕ)) := hcore1
    calc (576 : ℝ)
        = (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ))⁻¹ *
            (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (576 : ℝ)) :=
          (inv_mul_cancel_left₀ (ne_of_gt hpos) _).symm
      _ ≤ (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ))⁻¹ *
            (12 * (Support.cgEllipLowerConstant d) ^ (2 : ℕ) * (M.gamma * u ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hchain (inv_nonneg.2 hpos.le)
      _ = M.gamma * u ^ (2 : ℕ) := inv_mul_cancel_left₀ (ne_of_gt hpos) _
  have hwin : cgTailScale M (E : ℝ) ≤ M.gamma / 2 := by
    rw [hAu]
    calc Real.exp (-u) ≤ 2 / u ^ (2 : ℕ) := exp_neg_le_two_div_sq hu0
      _ ≤ M.gamma / 2 := by
          rw [div_le_div_iff₀ (pow_pos hu0 2) (by norm_num : (0 : ℝ) < 2)]
          linarith only [hgu]
  exact ⟨E, hEval, hwin,
    atomTail_of_budget M hC1 hEval hEreg hstate (exp_le_budget M hEval hfl1) hwin⟩

/-! ## 7. The endpoint: the `𝒢₀` proportion tail -/

/-- For every dimension there are a constant `C(d)` and a level `θ(d) ∈ (0,1)` such
that every model in the manuscript's printed regime `γ ≤ C^{−10}c⋆^{10}` obeys,
for **every** window `{0,…,n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach  —

```
ℙ[ θ < (proportion of scales k ≤ n at which 𝒢₀(k) fails) ] ≤ exp(−c₁ n)/3
```

at **every** rate `c₁ ∈ [0, γ^{-1}]` — the un-weakened output the graph routes
the §4.1 conclusion through; the printed rate is `γ p θ/C` at `p =
exp(K(d)^{−1}c⋆²γ^{−1})`, which is superexponentially larger than `γ^{-1}`, so
the `γ^{-1}` ceiling is a deliberate, checkable weakening that still dominates
every polynomial-in-`γ^{-1}` lane rate.

The only hypotheses are the model regime and the rate range; the `s`-window of
the `p.cg.ellipticity.bounds`, the `γ^{-4}` normalizer, the `p`-choice, the
threshold identification, the locality of `𝒴` and the `a.s.` finiteness of its
row sum are all discharged inside.

The parameter chain is the manuscript's: `E = C c⋆^{−1}`, atom scale
`A = exp(−u)` with `u = c⋆²/(C_cg C² γ)`, `p = exp(u/6) = exp(K(d)^{−1}c⋆²γ^{−1})`
at `K(d) = 6 C_cg C²`, so that `p^{1/σ}A = exp(−u/2)`, and normalizer
`D = gammaMomentConst σ · p^{1/σ} · K` — the manuscript's "for `K(d)` large
enough" being the floor imposed on `C`. -/
theorem exists_ratioTail_eventG0 (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
        ∃ C : ℝ, 6 ≤ C ∧
          ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
            ∀ c1 : ℝ, 0 ≤ c1 → c1 * M.gamma ≤ 1 →
            ∀ n : ℕ,
              (Cutoff.cutoffSampleLaw M).toMeasure
                  {omega | theta < scaleProp
                    (fun k => (Support.eventG0 M (Support.cgEllipLowerConstant d) k)ᶜ) n omega}
                ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  classical
  have hCcg0 : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  have hCs0 : (0 : ℝ) < Cstar := Cstar_pos
  have hgmc0 : (0 : ℝ) < gammaMomentConst (1 / 3 : ℝ) := gammaMomentConst_pos (by norm_num)
  have hgtc0 : (0 : ℝ) < gammaTriangleConst (1 / 3 : ℝ) := gammaTriangleConst_pos
  have hPn0 : (0 : ℝ) < penaltyNormalizer d := penaltyNormalizer_pos d
  obtain ⟨r, hr1, hrgap⟩ := exists_dependence_range d
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  refine ⟨r, hr1, ?_⟩
  intro theta htheta0 hthetar
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (3 * (r : ℝ)) + (r : ℝ) := ⟨_, rfl⟩
  obtain ⟨Rr, hRrdef⟩ : ∃ x : ℝ, x = max 4 (64 * (r : ℝ) * L / theta) := ⟨_, rfl⟩
  have hRr4 : (4 : ℝ) ≤ Rr := by rw [hRrdef]; exact le_max_left _ _
  have hRrL : 64 * (r : ℝ) * L / theta ≤ Rr := by rw [hRrdef]; exact le_max_right _ _
  obtain ⟨G, hGdef⟩ : ∃ x : ℝ, x = 36 * (1 + Cstar) * gammaMomentConst (1 / 3 : ℝ) *
      gammaTriangleConst (1 / 3 : ℝ) * penaltyNormalizer d / theta := ⟨_, rfl⟩
  have hG0 : 0 < G := by
    rw [hGdef]
    refine div_pos ?_ htheta0
    exact mul_pos (mul_pos (mul_pos (by linarith only [hCs0]) hgmc0) hgtc0) hPn0
  obtain ⟨C, hC6, hCfl, hall⟩ := exists_cgExcess_atomTail_of_floor d
      (max (7776 * Rr * (Support.cgEllipLowerConstant d) ^ (3 : ℕ))
        (7741440 * G * (Support.cgEllipLowerConstant d) ^ (7 : ℕ)))
  refine ⟨C, hC6, ?_⟩
  intro M hreg c1 hc10 hc1g
  have hC0 : (0 : ℝ) < C := by linarith only [hC6]
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC6]
  have hCpow6 : C ≤ C ^ (6 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (6 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hCpow4 : C ≤ C ^ (4 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (4 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hfl2 : 7776 * Rr * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) ≤ C ^ (4 : ℕ) :=
    le_trans (le_trans (le_max_left _ _) hCfl) hCpow4
  have hfl3 : 7741440 * G * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) ≤ C ^ (6 : ℕ) :=
    le_trans (le_trans (le_max_right _ _) hCfl) hCpow6
  obtain ⟨E, hEval, hwin, hatom⟩ := hall M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg4 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  obtain ⟨u, hudef⟩ : ∃ x : ℝ, x = (Support.cgEllipLowerConstant d)⁻¹ *
      (((E : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hudef]
    exact mul_pos (mul_pos (inv_pos.2 hCcg0) (pow_pos (inv_pos.2 hE0) 2)) (inv_pos.2 hg0)
  have hAu : cgTailScale M (E : ℝ) = Real.exp (-u) := by rw [hudef, cgTailScale]
  obtain ⟨-, hcore2, hcore3⟩ :=
    regime_core (u := u) hg0 hcs0 hcs32 hCcg0 hC0 hreg (by rw [hudef, hEval])
  -- the two regime consequences
  have hgu3 : 1296 * Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (3 : ℕ) := by
    have hpos : (0 : ℝ) < 6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) :=
      mul_pos (by norm_num) (pow_pos hCcg0 3)
    have hchain : 6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) * (1296 * Rr)
        ≤ 6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) *
            (M.gamma ^ (2 : ℕ) * u ^ (3 : ℕ)) := by
      calc 6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) * (1296 * Rr)
          = 7776 * Rr * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) := by ring
        _ ≤ C ^ (4 : ℕ) := hfl2
        _ ≤ 6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) *
              (M.gamma ^ (2 : ℕ) * u ^ (3 : ℕ)) := hcore3
    calc 1296 * Rr
        = (6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ))⁻¹ *
            (6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) * (1296 * Rr)) :=
          (inv_mul_cancel_left₀ (ne_of_gt hpos) _).symm
      _ ≤ (6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ))⁻¹ *
            (6 * (Support.cgEllipLowerConstant d) ^ (3 : ℕ) *
              (M.gamma ^ (2 : ℕ) * u ^ (3 : ℕ))) :=
          mul_le_mul_of_nonneg_left hchain (inv_nonneg.2 hpos.le)
      _ = M.gamma ^ (2 : ℕ) * u ^ (3 : ℕ) := inv_mul_cancel_left₀ (ne_of_gt hpos) _
  have hgu7 : 645120 * G ≤ M.gamma ^ (5 : ℕ) * u ^ (7 : ℕ) := by
    have hpos : (0 : ℝ) < 12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) :=
      mul_pos (by norm_num) (pow_pos hCcg0 7)
    have hchain : 12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) * (645120 * G)
        ≤ 12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) *
            (M.gamma ^ (5 : ℕ) * u ^ (7 : ℕ)) := by
      calc 12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) * (645120 * G)
          = 7741440 * G * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) := by ring
        _ ≤ C ^ (6 : ℕ) := hfl3
        _ ≤ 12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) *
              (M.gamma ^ (5 : ℕ) * u ^ (7 : ℕ)) := hcore2
    calc 645120 * G
        = (12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ))⁻¹ *
            (12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) * (645120 * G)) :=
          (inv_mul_cancel_left₀ (ne_of_gt hpos) _).symm
      _ ≤ (12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ))⁻¹ *
            (12 * (Support.cgEllipLowerConstant d) ^ (7 : ℕ) *
              (M.gamma ^ (5 : ℕ) * u ^ (7 : ℕ))) :=
          mul_le_mul_of_nonneg_left hchain (inv_nonneg.2 hpos.le)
      _ = M.gamma ^ (5 : ℕ) * u ^ (7 : ℕ) := inv_mul_cancel_left₀ (ne_of_gt hpos) _
  have hA0 : 0 < cgTailScale M (E : ℝ) := cgTailScale_pos M (E : ℝ)
  have hsprime0 : (0 : ℝ) < M.gamma / 4 := by linarith only [hg0]
  have hsprime1 : M.gamma / 4 ≤ 1 := by linarith only [hg4]
  -- the `𝒴`-tail at the canonical scale
  have hdom : ∀ j : ℕ, annulusPenalty d (1 / 3 : ℝ) (j + 2) * cgTailScale M (E : ℝ)
      ≤ cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2) := by
    intro j
    rw [annulusPenalty_third]
    exact le_of_eq (mul_comm _ _)
  have hapos : ∀ j : ℕ, 0 < cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2) :=
    fun j => mul_pos hA0 (annulusPenaltyThird_pos d _)
  have hsum : Summable fun j : ℕ => weightThird (M.gamma / 4) j *
      (cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2)) :=
    summable_weight_mul_annulusPenaltyThird d hsprime0 hA0.le
  obtain ⟨S0, hS0def⟩ : ∃ x : ℝ, x =
      ∑' j : ℕ, weightThird (M.gamma / 4) j * annulusPenaltyThird d (j + 2) := ⟨_, rfl⟩
  obtain ⟨Ssum, hSsumdef⟩ : ∃ x : ℝ, x = ∑' j : ℕ, weightThird (M.gamma / 4) j *
      (cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2)) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, x = gammaTriangleConst (1 / 3 : ℝ) * Ssum := ⟨_, rfl⟩
  have hSsum_eq : Ssum = cgTailScale M (E : ℝ) * S0 := by
    rw [hSsumdef, hS0def, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hSsum0 : 0 < Ssum := by
    rw [hSsumdef]
    refine hsum.tsum_pos (fun j => ?_) 0 ?_
    · exact mul_nonneg (weightThird_pos j).le (hapos j).le
    · exact mul_pos (weightThird_pos 0) (hapos 0)
  have hK0 : 0 < K := by
    rw [hKdef]
    exact mul_pos hgtc0 hSsum0
  have htail : ∀ m : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 3 : ℝ))
      (Ycal M (Support.cgEllipLowerConstant d) (M.gamma / 4) m) K := by
    intro m
    rw [hKdef, hSsumdef]
    exact isBigOWith_Ycal M (Support.cgEllipLowerConstant d) (by norm_num) hA0.le
      hatom hapos hdom hsum m
  -- SLOT (b): the `p`-choice
  obtain ⟨p, hpdef⟩ : ∃ x : ℝ, x = Real.exp (u / 6) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hpdef]; exact Real.exp_pos _
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    have h := Real.add_one_le_exp (u / 6)
    linarith only [h, hu0]
  have hinv3 : ((1 / 3 : ℝ))⁻¹ = 3 := by norm_num
  have hp3 : p ^ ((1 / 3 : ℝ))⁻¹ = Real.exp (u / 2) := by
    rw [hinv3, hpdef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  obtain ⟨D, hDdef⟩ : ∃ x : ℝ, x =
      gammaMomentConst (1 / 3 : ℝ) * p ^ ((1 / 3 : ℝ))⁻¹ * K := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hDdef]
    exact mul_pos (mul_pos hgmc0 (Real.rpow_pos_of_pos hp0 _)) hK0
  have hnorm : gammaMomentConst (1 / 3 : ℝ) * p ^ ((1 / 3 : ℝ))⁻¹ * K ≤ D := le_of_eq hDdef.symm
  have hexpprod : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hDval : D = gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) * S0 *
      Real.exp (-(u / 2)) := by
    rw [hDdef, hp3, hKdef, hSsum_eq, hAu, ← hexpprod]
    ring
  -- the moment/rate side conditions
  have hgne : M.gamma ≠ 0 := ne_of_gt hg0
  have hplow : u ^ (3 : ℕ) / 1296 ≤ p := by
    have h := Real.pow_div_factorial_le_exp (x := u / 6) (by linarith only [hu0]) 3
    have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf] at h
    rw [hpdef]
    calc u ^ (3 : ℕ) / 1296 = (u / 6) ^ (3 : ℕ) / 6 := by ring
      _ ≤ Real.exp (u / 6) := h
  have hg2p : Rr ≤ M.gamma ^ (2 : ℕ) * p := by
    calc Rr = 1296 * Rr / 1296 := by ring
      _ ≤ M.gamma ^ (2 : ℕ) * u ^ (3 : ℕ) / 1296 := by
          exact div_le_div_of_nonneg_right hgu3 (by norm_num)
      _ = M.gamma ^ (2 : ℕ) * (u ^ (3 : ℕ) / 1296) := by ring
      _ ≤ M.gamma ^ (2 : ℕ) * p := mul_le_mul_of_nonneg_left hplow (by positivity)
  have hgp : (4 : ℝ) ≤ M.gamma * p := by
    have hstep : 4 * M.gamma ≤ M.gamma ^ (2 : ℕ) * p := by
      have h1 : 4 * M.gamma ≤ 4 := by linarith only [hg4]
      linarith only [h1, hRr4, hg2p]
    have hstep2 := mul_le_mul_of_nonneg_right hstep (inv_nonneg.2 hg0.le)
    calc (4 : ℝ) = 4 * M.gamma * M.gamma⁻¹ := by field_simp
      _ ≤ M.gamma ^ (2 : ℕ) * p * M.gamma⁻¹ := hstep2
      _ = M.gamma * p := by field_simp
  have hsp : 1 ≤ M.gamma / 4 * p := by linarith only [hgp]
  have hrate : Real.log ((3 : ℝ) * (r : ℝ)) + c1 * (r : ℝ)
      ≤ M.gamma / 4 * p * theta / (16 * (r : ℝ)) := by
    have hlog3r : (0 : ℝ) ≤ Real.log (3 * (r : ℝ)) :=
      Real.log_nonneg (by linarith only [hrR])
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by linarith only [hrR]
    have hstepA : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * M.gamma ≤ L := by
      rw [hLdef]
      have h1 : Real.log (3 * (r : ℝ)) * M.gamma ≤ Real.log (3 * (r : ℝ)) :=
        mul_le_of_le_one_right hlog3r (by linarith only [hg4, hg0])
      have h2 : c1 * M.gamma * (r : ℝ) ≤ 1 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right hc1g hrnn
      linarith only [h1, h2]
    have h64 : 64 * (r : ℝ) * L ≤ M.gamma ^ (2 : ℕ) * p * theta := by
      calc 64 * (r : ℝ) * L = 64 * (r : ℝ) * L / theta * theta := by field_simp
        _ ≤ Rr * theta := mul_le_mul_of_nonneg_right hRrL htheta0.le
        _ ≤ M.gamma ^ (2 : ℕ) * p * theta := mul_le_mul_of_nonneg_right hg2p htheta0.le
    have hA : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma
        ≤ M.gamma * p * theta * M.gamma := by
      calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma
          = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * M.gamma * (64 * (r : ℝ)) := by ring
        _ ≤ L * (64 * (r : ℝ)) :=
            mul_le_mul_of_nonneg_right hstepA (by linarith only [hrnn])
        _ = 64 * (r : ℝ) * L := by ring
        _ ≤ M.gamma ^ (2 : ℕ) * p * theta := h64
        _ = M.gamma * p * theta * M.gamma := by ring
    have hB : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ))
        ≤ M.gamma * p * theta := by
      calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ))
          = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma * M.gamma⁻¹ := by
            field_simp
        _ ≤ M.gamma * p * theta * M.gamma * M.gamma⁻¹ :=
            mul_le_mul_of_nonneg_right hA (inv_nonneg.2 hg0.le)
        _ = M.gamma * p * theta := by field_simp
    rw [le_div_iff₀ (by linarith only [hrR] : (0 : ℝ) < 16 * (r : ℝ)),
      show M.gamma / 4 * p * theta = M.gamma * p * theta / 4 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (16 * (r : ℝ)) * 4
        = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) := by ring
      _ ≤ M.gamma * p * theta := hB
  -- SLOT (b'): the threshold identification
  have hS0le : S0 ≤ penaltyNormalizer d / M.gamma ^ (4 : ℕ) := by
    rw [hS0def]
    exact tsum_weightThird_mul_annulusPenaltyThird_le d hg0 hg4
  have hu20 : (0 : ℝ) < u / 2 := by linarith only [hu0]
  have hE7 : Real.exp (-(u / 2)) ≤ M.gamma ^ (5 : ℕ) / G := by
    refine le_trans (exp_neg_le_seven hu20) ?_
    rw [div_le_div_iff₀ (pow_pos hu20 7) hG0,
      show M.gamma ^ (5 : ℕ) * (u / 2) ^ (7 : ℕ) = M.gamma ^ (5 : ℕ) * u ^ (7 : ℕ) / 128 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    linarith only [hgu7]
  have hkey : 9 * D * (1 + Cstar) ≤ M.gamma / 4 * theta := by
    have hprod : S0 * Real.exp (-(u / 2))
        ≤ penaltyNormalizer d / M.gamma ^ (4 : ℕ) * (M.gamma ^ (5 : ℕ) / G) :=
      mul_le_mul hS0le hE7 (Real.exp_pos _).le (div_pos hPn0 (pow_pos hg0 4)).le
    have hc1 : (0 : ℝ) ≤ gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) :=
      (mul_pos hgmc0 hgtc0).le
    have hc2 : (0 : ℝ) ≤ 1 + Cstar := by linarith only [hCs0]
    have hstep3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hc1)
        (by norm_num : (0 : ℝ) ≤ 9)) hc2
    have hne1 : (1 + Cstar) ≠ 0 := by
      have : (0 : ℝ) < 1 + Cstar := by linarith only [hCs0]
      exact ne_of_gt this
    have hne2 : gammaMomentConst (1 / 3 : ℝ) ≠ 0 := ne_of_gt hgmc0
    have hne3 : gammaTriangleConst (1 / 3 : ℝ) ≠ 0 := ne_of_gt hgtc0
    have hne4 : penaltyNormalizer d ≠ 0 := ne_of_gt hPn0
    have hne5 : M.gamma ≠ 0 := ne_of_gt hg0
    have hne6 : theta ≠ 0 := ne_of_gt htheta0
    have hRHS : 9 * (gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) *
        (penaltyNormalizer d / M.gamma ^ (4 : ℕ) * (M.gamma ^ (5 : ℕ) / G))) * (1 + Cstar)
        = M.gamma / 4 * theta := by
      rw [hGdef]
      field_simp
      ring
    have hLHS : 9 * D * (1 + Cstar) = 9 * (gammaMomentConst (1 / 3 : ℝ) *
        gammaTriangleConst (1 / 3 : ℝ) * (S0 * Real.exp (-(u / 2)))) * (1 + Cstar) := by
      rw [hDval]
      ring
    rw [hLHS, ← hRHS]
    exact hstep3
  have hthr : 9 * (M.gamma / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) ≤ D⁻¹ :=
    threshold_le_inv hsprime0 htheta0 htheta1 hp1 hD0 hkey
  -- the null set of the enlargement
  have hnull : (Cutoff.cutoffSampleLaw M).toMeasure
      (goodRowSet M (Support.cgEllipLowerConstant d) (M.gamma / 4))ᶜ = 0 :=
    measure_compl_goodRowSet M (Support.cgEllipLowerConstant d) (by norm_num) hA0.le hK0
      hsprime0 (by linarith only [hg4]) hatom hapos hdom hsum htail
  -- the assembled tail for the enlarged family
  have hmain := ratioTail_Ycal M (Support.cgEllipLowerConstant d) (M.gamma / 4) D
    (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k ∪
      (goodRowSet M (Support.cgEllipLowerConstant d) (M.gamma / 4))ᶜ)
    (by norm_num : (0 : ℝ) < 1 / 3) hK0 hD0 hp1 hsprime0 hsprime1 hsp hr1
    (by norm_num : (1 : ℝ) ≤ 3) htheta0 hthetar hc10 hrate htail hnorm
    hrgap
    (fun m => measurable_Ycal_annulusRegion_local M (Support.cgEllipLowerConstant d)
      (M.gamma / 4) m)
    (hreduce_eventG0 M (Support.cgEllipLowerConstant d) hD0 hthr)
  exact fun n => le_trans (measure_scaleProp_le_of_null_enlargement _ _ _ hnull n) (hmain n)

end

end Algsuperdiff.Section4.Provider.Proportion
