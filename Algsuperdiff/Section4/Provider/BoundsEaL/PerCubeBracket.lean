/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.LambdaSlotConsumer
import Algsuperdiff.Section4.Provider.BoundsEaL.MomentHolder
import Algsuperdiff.Section4.Provider.BoundsEaL.SigmaBarLandmark

/-!
# Step 5's `(1 + ∇k · λ^{-1})` bracket, at every moment

## What this module does

Two of the three summands of `MajorantSlots.step3DisplayAt` carry the bracket

```
( 1 + 3^{2j}‖∇(k_L − k_{j−2})‖_{W̲^{1,∞}(□_j)} · λ_{2γ,2}^{-1} )^{θ} ,
```

at the two printed exponents `θ = 2s/(1−4γ)` and `θ = 4γ/(1−4γ)` (the
development's gapped-gauge reading of the printed `2s/(1−2γ)`, `2γ/(1−2γ)`;
`Step3HSlot`'s deviation, inherited).  This module supplies its `q`-th
moment, for every `q ∈ [1,∞)`, in the development normal form `∫⁻ (·)^q ≤
(ofReal R)^q`.

* **both exponents are `≤ 1`** in the anchor's own ranges (`s ≤ 1/4`,
  `γ ≤ 1/8`), so `x^θ ≤ x` for the base `x = 1 + ∇k·λ^{-1} ≥ 1`; NO Orlicz
  input and no `q`-power is spent on the exponent;

`step3Bracket_majorant_le` then evaluates the product majorant: the whole
`q`-th-moment bound is

```
1 + C(2)√(2q) · fullGradConst M · (3^{γ j} σ̄_{j−1}^{-1})
      · ( λUp·C_cg + C(1/3)(2q)³ · λUp·λMax · cgTailScale ) ,
```

and the middle factor is `O(√γ)` by bullet (B3) together with the `σ̄` index
reconciliation of `SigmaBarLandmark`, which is exactly the statement that the
bracket is `1 + O(√q √γ)` in the printed regime.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The abstract bracket moment -/

/-- **The bracket moment, over an abstract probability space.**

If two nonnegative observables satisfy the development normal form at the
doubled exponent `2q`, then for every `θ ≤ 1` the bracket `(1 + X·Y)^θ` satisfies it at
`q`, with the majorant `1 + R_X R_Y`.

The `θ ≤ 1` step is `x^θ ≤ x` for `x ≥ 1`: no moment input is spent on the
exponent.  The product step is the two-factor Hölder engine and the additive `1`
is `ℝ≥0∞` Minkowski against a constant, which a probability measure integrates
to `1`. -/
theorem lintegral_rpow_one_add_mul_le_of_moments {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {X Y : Omega → ℝ}
    {RX RY q theta : ℝ} (hq : 1 ≤ q) (hth1 : theta ≤ 1)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hXm : AEMeasurable X mu) (hYm : AEMeasurable Y mu) (hRX : 0 ≤ RX) (hRY : 0 ≤ RY)
    (hX : (∫⁻ omega, ENNReal.ofReal (X omega) ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RX ^ (2 * q))
    (hY : (∫⁻ omega, ENNReal.ofReal (Y omega) ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RY ^ (2 * q)) :
    (∫⁻ omega, ENNReal.ofReal (Real.rpow (1 + X omega * Y omega) theta) ^ q ∂mu) ≤
      ENNReal.ofReal (1 + RX * RY) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  set f : Omega → ℝ≥0∞ := fun _ => (1 : ℝ≥0∞) with hf
  set g : Omega → ℝ≥0∞ :=
    fun omega => ENNReal.ofReal (X omega) * ENNReal.ofReal (Y omega) with hg
  have hgm : AEMeasurable g mu := hXm.ennreal_ofReal.mul hYm.ennreal_ofReal
  -- the pointwise step: the exponent is spent by `x^θ ≤ x`
  have hpt : ∀ omega : Omega,
      ENNReal.ofReal (Real.rpow (1 + X omega * Y omega) theta) ≤ (f + g) omega := by
    intro omega
    have hxy : (0 : ℝ) ≤ X omega * Y omega := mul_nonneg (hX0 omega) (hY0 omega)
    have hbase : (1 : ℝ) ≤ 1 + X omega * Y omega := by linarith only [hxy]
    have hle : Real.rpow (1 + X omega * Y omega) theta ≤ 1 + X omega * Y omega := by
      have hstep := Real.rpow_le_rpow_of_exponent_le hbase hth1
      rwa [Real.rpow_one] at hstep
    refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
    rw [ENNReal.ofReal_add zero_le_one hxy, ENNReal.ofReal_one,
      ENNReal.ofReal_mul (hX0 omega)]
    rfl
  have hstep1 : (∫⁻ omega, ENNReal.ofReal (Real.rpow (1 + X omega * Y omega) theta) ^ q ∂mu) ≤
      ∫⁻ omega, (f + g) omega ^ q ∂mu :=
    lintegral_mono fun omega => ENNReal.rpow_le_rpow (hpt omega) hq0.le
  -- Minkowski against the constant
  have hmink : (∫⁻ omega, (f + g) omega ^ q ∂mu) ^ (1 / q) ≤
      (∫⁻ omega, f omega ^ q ∂mu) ^ (1 / q) + (∫⁻ omega, g omega ^ q ∂mu) ^ (1 / q) :=
    ENNReal.lintegral_Lp_add_le (μ := mu) (f := f) (g := g)
      measurable_const.aemeasurable hgm hq
  have hconst : (∫⁻ omega, f omega ^ q ∂mu) ^ (1 / q) = 1 := by
    rw [hf]
    simp only [ENNReal.one_rpow]
    rw [lintegral_const, measure_univ, mul_one, ENNReal.one_rpow]
  have hprod : (∫⁻ omega, g omega ^ q ∂mu) ≤ ENNReal.ofReal (RX * RY) ^ q :=
    lintegral_rpow_mul_le_of_moments hq0 hXm.ennreal_ofReal hYm.ennreal_ofReal hRX hX hY
  have hproot : (∫⁻ omega, g omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal (RX * RY) := by
    refine le_trans (ENNReal.rpow_le_rpow hprod (by positivity)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]
  have hsum : (∫⁻ omega, (f + g) omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal (1 + RX * RY) := by
    refine le_trans hmink ?_
    refine le_trans (add_le_add (le_of_eq hconst) hproot) (le_of_eq ?_)
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hRX hRY), ENNReal.ofReal_one]
  have hraise := ENNReal.rpow_le_rpow hsum hq0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one] at hraise
  exact le_trans hstep1 hraise

/-! ## 2. Both printed exponents are at most one -/

/-- **The gradient bracket's exponent.**  `2s/(1−4γ) ≤ 1` in the anchor's own
ranges `s ≤ 1/4`, `γ ≤ 1/8`.  This is the exact endpoint: at `s = 1/4` and
`γ = 0` the exponent IS `1`. -/
theorem step3_gradient_exponent_le_one {gam s : ℝ} (hgam : gam ≤ 1 / 8) (hs : s ≤ 1 / 4) :
    2 * s / (1 - 4 * gam) ≤ 1 := by
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgam]
  rw [div_le_one hden]
  linarith only [hs, hgam]

/-- **The `γ` bracket's exponent.**  `4γ/(1−4γ) ≤ 1` at `γ ≤ 1/8`. -/
theorem step3_gamma_exponent_le_one {gam : ℝ} (hgam : gam ≤ 1 / 8) :
    4 * gam / (1 - 4 * gam) ≤ 1 := by
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgam]
  rw [div_le_one hden]
  linarith only [hgam]

/-! ## 3. The two slots are nonnegative -/

/-- The `L`-free gradient slot is nonnegative at the canonical tail gauge. -/
theorem lFreeGradSlot_tailSeriesGauge_nonneg (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ lFreeGradSlot m (tailSeriesGauge m) R omega := by
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg ?_ ?_)
  · exact headLayerSum_nonneg m R.scale R.index omega
  · exact tsum_nonneg fun i => tailLayerTerm_nonneg m R.scale R.index omega i

/-- The `λ`-slot of Step 3's display is nonnegative. -/
theorem inv_unitCubeLambda_twoGamma_nonneg (M : ABKModel d) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ (Algsuperdiff.Frozen.Section24.unitCubeLambda (2 * M.gamma) (.finite 2)
      (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ := by
  haveI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  exact Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.unitCubeLambda_inv_nonneg
    (unitRescaledCutoffCoeff M R (R.scale - 2) omega) (by linarith only [hg0])
    Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.isAdmissible_finite_two

/-- The `λ`-slot of Step 3's display is measurable: the gapped gauge `2γ` is
positive, which is all `MajorantMeasurability`'s literal-measurability engine
needs. -/
theorem measurable_inv_unitCubeLambda_twoGamma (M : ABKModel d) (R : TriadicCube d) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      (Algsuperdiff.Frozen.Section24.unitCubeLambda (2 * M.gamma) (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ := by
  haveI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  exact measurable_unitCubeLambda_inv_unitRescaledCutoffCoeff M R (by linarith only [hg0])

/-! ## 4. The bracket at the Step-3 slots -/

/-- **Step 5's bracket, at every moment.**

For every `q ∈ [1,∞)` and every exponent `θ ≤ 1` — in particular the two
printed exponents `2s/(1−4γ)` and `4γ/(1−4γ)`, by
`step3_gradient_exponent_le_one` and `step3_gamma_exponent_le_one` — the
bracket of `MajorantSlots.step3DisplayAt` obeys the development normal form
with the majorant `1 + R_{B6a}(2q) · R_{B5}(2q)`, the product of the two proved
Step-4 majorants at the doubled exponent.

The binders are the printed regime (bullet (B5)'s own), the range `R.scale ≤ m`
of the gradient bullet, and `1 ≤ q`.  No `γ`-power and no `s`-power is moved. -/
theorem exists_lintegral_rpow_step3Bracket_le (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ (m : ℤ) (R : TriadicCube d), R.scale ≤ m → ∀ q : ℝ, 1 ≤ q →
          ∀ theta : ℝ, theta ≤ 1 →
            ∫⁻ omega : Cutoff.CutoffSample d,
                ENNReal.ofReal (Real.rpow (1 +
                    lFreeGradSlot m (tailSeriesGauge m) R omega *
                      (Algsuperdiff.Frozen.Section24.unitCubeLambda (2 * M.gamma) (.finite 2)
                        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹) theta) ^ q
                ∂(Cutoff.cutoffSampleLaw M).toMeasure
              ≤ ENNReal.ofReal (1 +
                  gammaTwoMomentBound (2 * q)
                      (fullGradConst M * Real.rpow 3 (M.gamma * (R.scale : ℝ))) *
                    (lambdaUpscaleConst d *
                        (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ *
                          Support.cgEllipLowerConstant d) +
                      gammaMomentBound (1 / 3) (2 * q)
                        (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
                          (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ *
                            Proportion.cgTailScale M (C * (Disorder.cstar M)⁻¹))))) ^ q := by
  obtain ⟨C, hC6, hall⟩ := exists_lintegral_rpow_inv_unitCubeLambda_twoGamma_le d
  refine ⟨C, hC6, ?_⟩
  intro M hreg m R hkm q hq theta hth
  obtain ⟨E, hEval, hlam⟩ := hall M hreg
  have h2q : (1 : ℝ) ≤ 2 * q := by linarith only [hq]
  have hsig0 : (0 : ℝ) < (Annealed.sigmaBar M (R.scale - 1) : ℝ) :=
    (Annealed.sigmaBar M (R.scale - 1)).2
  have hsiginv : (0 : ℝ) ≤ ((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ :=
    (inv_pos.mpr hsig0).le
  have hCcg : (0 : ℝ) ≤ Support.cgEllipLowerConstant d :=
    (Support.cgEllipLowerConstant_pos d).le
  have hlamUp : (0 : ℝ) ≤ lambdaUpscaleConst d := (lambdaUpscaleConst_pos d).le
  have hlamMax : (0 : ℝ) ≤ lambdaMaxOrliczConst d := (lambdaMaxOrliczConst_pos d).le
  have htail : (0 : ℝ) ≤ Proportion.cgTailScale M (E : ℝ) := (Proportion.cgTailScale_pos M _).le
  have hRX : (0 : ℝ) ≤ gammaTwoMomentBound (2 * q)
      (fullGradConst M * Real.rpow 3 (M.gamma * (R.scale : ℝ))) :=
    gammaTwoMomentBound_nonneg
      (mul_nonneg (fullGradConst_pos M).le (Real.rpow_nonneg (by norm_num) _))
  have hRY : (0 : ℝ) ≤ lambdaUpscaleConst d *
      (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ * Support.cgEllipLowerConstant d) +
      gammaMomentBound (1 / 3) (2 * q)
        (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
          (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ * Proportion.cgTailScale M (E : ℝ))) := by
    refine add_nonneg (mul_nonneg hlamUp (mul_nonneg hsiginv hCcg)) ?_
    refine gammaMomentBound_nonneg (by norm_num) (by linarith only [h2q]) ?_
    exact mul_nonneg (mul_nonneg hlamUp hlamMax) (mul_nonneg hsiginv htail)
  have hkey := lintegral_rpow_one_add_mul_le_of_moments (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
    (X := fun omega => lFreeGradSlot m (tailSeriesGauge m) R omega)
    (Y := fun omega => (Algsuperdiff.Frozen.Section24.unitCubeLambda (2 * M.gamma) (.finite 2)
      (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹)
    hq hth (fun omega => lFreeGradSlot_tailSeriesGauge_nonneg m R omega)
    (fun omega => inv_unitCubeLambda_twoGamma_nonneg M R omega)
    ((measurable_lFreeGradSlot m (tailSeriesGauge m)
      (fun k v => measurable_tailSeriesGauge m k v) R).aemeasurable)
    (measurable_inv_unitCubeLambda_twoGamma M R).aemeasurable hRX hRY
    (lintegral_rpow_lFreeGradSlot_le M m R hkm h2q) (hlam R (2 * q) h2q)
  rw [hEval] at hkey
  exact hkey

/-! ## 5. The bracket majorant is `1 + O(√q √γ)` -/

/-- **The bracket is `O(1)` in the printed regime.**

The product majorant of `exists_lintegral_rpow_step3Bracket_le` is bounded by

```
C(2)√(2q) · fullGradConst M · 16 c⋆^{-1/2} √γ
    · ( λUp·C_cg + C(1/3)(2q)³ · λUp·λMax · γ/2 ) ,
```

i.e. by `O(√q √γ (1 + q³γ))`.  Two proved inputs do all the work: the (B3)
gauge slot at the (B5) index (`SigmaBarLandmark`), which turns the product
`3^{γj}·σ̄_{j−1}^{-1}` of the two bullets into the `√γ` the anchor's scalar
carries, and the `s`-window `LambdaWindow.cgTailScale_le_half_gamma`, which
prices the `Γ_{1/3}` tail at `γ/2`.

Consequently the bracket contributes `1 + O(√q√γ)` to Step 5's Hölder product;
under the anchor's own `p ≤ C^{-1}γ^{-1}s` (which gives `√p√γ ≤ √(C^{-1}s)`)
this is bounded, and NO `γ`-power is consumed by the bracket. -/
theorem step3Bracket_majorant_le (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ (j : ℤ) (q : ℝ), 1 ≤ q →
          gammaTwoMomentBound (2 * q) (fullGradConst M * Real.rpow 3 (M.gamma * (j : ℝ))) *
              (lambdaUpscaleConst d * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
                  Support.cgEllipLowerConstant d) +
                gammaMomentBound (1 / 3) (2 * q)
                  (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
                    (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
                      Proportion.cgTailScale M (C * (Disorder.cstar M)⁻¹)))) ≤
            gammaMomentConst 2 * Real.sqrt (2 * q) * fullGradConst M *
              (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) *
              (lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
                gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
                  (lambdaUpscaleConst d * lambdaMaxOrliczConst d * (M.gamma / 2))) := by
  obtain ⟨C3, hC3, hgauge⟩ := exists_rpow_gamma_mul_inv_sigmaBar_sub_one_le d
  refine ⟨max (max 6 (Support.cgEllipLowerConstant d)) C3,
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro M hreg j q hq
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hC6 : (6 : ℝ) ≤ max (max 6 (Support.cgEllipLowerConstant d)) C3 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCcgle : Support.cgEllipLowerConstant d ≤
      max (max 6 (Support.cgEllipLowerConstant d)) C3 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hgauge' := hgauge M
    (gamma_regime_mono hC3 (le_max_right _ _) hcs0.le hreg) j
  have htail := cgTailScale_le_half_gamma M hC6 hCcgle hreg
  -- the abbreviations
  have hK : (0 : ℝ) ≤ gammaMomentConst 2 * Real.sqrt (2 * q) * fullGradConst M :=
    mul_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))
      (fullGradConst_pos M).le
  have hPS : (0 : ℝ) ≤ Real.rpow 3 (M.gamma * (j : ℝ)) *
      ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (inv_pos.mpr (Annealed.sigmaBar M (j - 1)).2).le
  have hA : (0 : ℝ) ≤ lambdaUpscaleConst d * Support.cgEllipLowerConstant d :=
    mul_nonneg (lambdaUpscaleConst_pos d).le (Support.cgEllipLowerConstant_pos d).le
  have hT : (0 : ℝ) ≤ gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
      (lambdaUpscaleConst d * lambdaMaxOrliczConst d) := by
    refine mul_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le ?_) ?_
    · exact Real.rpow_nonneg (by linarith only [hq]) _
    · exact mul_nonneg (lambdaUpscaleConst_pos d).le (lambdaMaxOrliczConst_pos d).le
  have htail0 : (0 : ℝ) ≤ Proportion.cgTailScale M
      (max (max 6 (Support.cgEllipLowerConstant d)) C3 * (Disorder.cstar M)⁻¹) :=
    (Proportion.cgTailScale_pos M _).le
  -- the tail is priced at γ/2
  have hbracket : lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
      gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
        (lambdaUpscaleConst d * lambdaMaxOrliczConst d) *
        Proportion.cgTailScale M
          (max (max 6 (Support.cgEllipLowerConstant d)) C3 * (Disorder.cstar M)⁻¹) ≤
      lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
        gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
          (lambdaUpscaleConst d * lambdaMaxOrliczConst d) * (M.gamma / 2) := by
    have := mul_le_mul_of_nonneg_left htail hT
    linarith only [this]
  -- the algebraic regrouping and the two monotone steps
  unfold gammaTwoMomentBound gammaMomentBound
  have hleft : gammaMomentConst 2 * Real.sqrt (2 * q) *
        (fullGradConst M * Real.rpow 3 (M.gamma * (j : ℝ))) *
        (lambdaUpscaleConst d * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
            Support.cgEllipLowerConstant d) +
          gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
            (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
              (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
                Proportion.cgTailScale M
                  (max (max 6 (Support.cgEllipLowerConstant d)) C3 *
                    (Disorder.cstar M)⁻¹)))) =
      (gammaMomentConst 2 * Real.sqrt (2 * q) * fullGradConst M) *
        ((Real.rpow 3 (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹) *
          (lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
            gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
              (lambdaUpscaleConst d * lambdaMaxOrliczConst d) *
              Proportion.cgTailScale M
                (max (max 6 (Support.cgEllipLowerConstant d)) C3 *
                  (Disorder.cstar M)⁻¹))) := by ring
  have hright : gammaMomentConst 2 * Real.sqrt (2 * q) * fullGradConst M *
        (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) *
        (lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
          gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
            (lambdaUpscaleConst d * lambdaMaxOrliczConst d * (M.gamma / 2))) =
      (gammaMomentConst 2 * Real.sqrt (2 * q) * fullGradConst M) *
        ((16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) *
          (lambdaUpscaleConst d * Support.cgEllipLowerConstant d +
            gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
              (lambdaUpscaleConst d * lambdaMaxOrliczConst d) * (M.gamma / 2))) := by ring
  rw [hleft, hright]
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hamp : (0 : ℝ) ≤ 16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  exact mul_le_mul hgauge' hbracket
    (add_nonneg hA (mul_nonneg hT htail0)) hamp

end

end Algsuperdiff.Section4.Provider.BoundsEaL
