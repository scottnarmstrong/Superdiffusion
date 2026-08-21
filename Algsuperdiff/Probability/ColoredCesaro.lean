import Algsuperdiff.Probability.CesaroWindow
import Algsuperdiff.Probability.ColoredAverage
import Algsuperdiff.Probability.RDependent

/-!
# The `r`-dependent Cesàro `Γ_σ` concentration engine

ABK26, proof of `l.minimal.scale.sep`, Step 1.  Step 1 does *not* end with
a fully independent family: it ends with

> "Since the sequence `{X_j}` is 2-dependent, we may apply Proposition
> `p.concentration` to obtain
> `(m−n)^{-1/2} ∑_{j=n}^m (X_j − E[X_j]) ≤ O_{Γ₂}(C c⋆^{-1} s^{-5/2} γ^{1/2})`."

`p.concentration` as printed is stated for **independent** sequences, so the
object Step 1 actually consumes is not a theorem of the manuscript.  This
module supplies it: the exact analogue of the independent Cesàro engine with
full independence weakened to the `r`-dependence of
`Algsuperdiff/Probability/.lean`.  The free `r` reaches the conclusion only
through the constant `rDepEngineConst r` (a `√(r+1)` colour count), so no
dimensional restriction rides on the engine.

## The route

Split the window `[n, m] ⊆ ℤ` into the `r+1` residue classes mod `r+1`. Two
distinct indices in one class differ by a nonzero multiple of `r+1`, hence are
`≥ r`-separated, hence the class is mutually independent
(`le_abs_sub_of_intCast_zmod_eq`); the `r+1` per-class sums are recombined by the
`Γ_σ` triangle inequality. Both halves are packaged in the palette-generic
`isBigO_gammaSigma_average_colored`, whose combinatorial input at this colouring
is `sum_sqrt_class_card_le` together with `card_zmod_succ`.

## Contents

1. `rDepEngineConst`, `rDepTailEngineConst`, `twoDepEngineConst` — the explicit
   constants.
2. `isBigO_cesaroAvg_of_rDependent_centered` — colouring plus concentration, for
   a centred family.
3. `cesaroAvg_isBigO_of_rDependent` — the headline engine
   (`cesaroAvg_isBigO_of_twoDependent` is its `r = 2` instance).
4. `cesaroAvg_isBigO_of_rDependent_with_tail` — the engine with an additive
   boundary term.

## References

* ABK26, Proposition `p.concentration`.
* ABK26, `l.minimal.scale.sep`, Step 1.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open Homogenization.IndependentSums
open Homogenization.Book.Ch04 (gammaSigmaIndependentSumConst)
open scoped BigOperators

noncomputable section

/-! ## Explicit constants -/

/-- The `r`-dependent Cesàro engine constant: CoarseGraining's centered
independent-sum constant for `σ = 2`, times the centering cost, inflated by the
`Γ₂` triangle constant (recombining the `r+1` colour classes) and by `√(r+1)`
(the colour count). -/
def rDepEngineConst (r : ℕ) : ℝ :=
  gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((r : ℝ) + 1) * cesaroCenterConst 2

/-- The `r`-dependent Cesàro engine constant in the presence of an additive
boundary/tail term. -/
def rDepTailEngineConst (r : ℕ) : ℝ :=
  (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * (rDepEngineConst r + 1)

/-- The `r = 2` engine constant (`√3` colour count) — the manuscript's regime. -/
def twoDepEngineConst : ℝ := rDepEngineConst 2

theorem rDepEngineConst_pos (r : ℕ) : 0 < rDepEngineConst r := by
  have h1 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : 0 < gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_pos (by norm_num)
  have h3 : 0 < Real.sqrt ((r : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < cesaroCenterConst 2 := cesaroCenterConst_pos (by norm_num)
  simp only [rDepEngineConst]
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

theorem rDepTailEngineConst_pos (r : ℕ) : 0 < rDepTailEngineConst r := by
  have h1 : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos one_add_log_two_pos _
  have h2 := rDepEngineConst_pos r
  simp only [rDepTailEngineConst]
  exact mul_pos h1 (by linarith only [h2])

theorem twoDepEngineConst_pos : 0 < twoDepEngineConst := rDepEngineConst_pos 2

/-- The `r = 2` constant in closed form: the colour count is `√3`. -/
theorem twoDepEngineConst_eq :
    twoDepEngineConst = gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
      Real.sqrt 3 * cesaroCenterConst 2 := by
  simp only [twoDepEngineConst, rDepEngineConst]
  norm_num

/-! ## The coloured concentration bound for a centred `r`-dependent family -/

section CenteredAverage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Averaged `p.concentration` for an `r`-dependent family, in `cesaroAvg` form.**
For a centred, `r`-dependent, `Γ₂`-controlled family `{Y_j}`, the Cesàro average
over `[n, m]` obeys `O_{Γ₂}( C √(r+1) · K · (m − n + 1)^{-1/2} )`. -/
theorem isBigO_cesaroAvg_of_rDependent_centered [IsProbabilityMeasure P]
    (Y : ℤ → Ω → ℝ) {Kc : ℝ} {r : ℕ} (hKc : 0 < Kc)
    (hdep : RDependent P Y r)
    (hmeas : ∀ j, Measurable (Y j))
    (hY : ∀ j, IsBigO P (gammaSigma 2) (Y j) Kc)
    (hmean : ∀ j, ∫ ω, Y j ω ∂P = 0)
    {n m : ℤ} (hnm : n ≤ m) :
    IsBigO P (gammaSigma 2) (fun ω => cesaroAvg (fun j => Y j ω) n m)
      (gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((r : ℝ) + 1) * Kc * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hcard : (((Finset.Icc n m).card : ℕ) : ℝ) = ((m - n + 1 : ℤ) : ℝ) :=
    natCast_card_Icc_int hnm
  have hcpos : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm
  -- Per-colour independence: same residue mod `r+1` ⇒ separation `≥ r`.
  have hIndepColor : ∀ b ∈ (Finset.Icc n m).image (fun j : ℤ => (j : ZMod (r + 1))),
      ProbabilityTheory.iIndepFun
        (fun (i : {i // i ∈ (Finset.Icc n m).filter
          (fun j : ℤ => (j : ZMod (r + 1)) = b)}) => Y i.1) P := by
    intro b _hb
    refine hdep _ ?_
    intro i hi j hj hij
    have hi' : ((i : ZMod (r + 1))) = b := (Finset.mem_filter.mp hi).2
    have hj' : ((j : ZMod (r + 1))) = b := (Finset.mem_filter.mp hj).2
    have hstep := le_abs_sub_of_intCast_zmod_eq (r := r) (by rw [hi', hj']) hij
    linarith only [hstep]
  -- The Cauchy--Schwarz input, with `colorCount = r+1`.
  have hSqrt :
      ∑ b ∈ (Finset.Icc n m).image (fun j : ℤ => (j : ZMod (r + 1))),
          Real.sqrt
            (((Finset.Icc n m).filter (fun j : ℤ => (j : ZMod (r + 1)) = b)).card : ℝ) ≤
        Real.sqrt ((r : ℝ) + 1) * Real.sqrt (((Finset.Icc n m).card : ℕ) : ℝ) := by
    have h := sum_sqrt_class_card_le (κ := ZMod (r + 1)) (Finset.Icc n m)
      (fun j : ℤ => (j : ZMod (r + 1)))
    rwa [card_zmod_succ r] at h
  have hcolored := isBigO_gammaSigma_average_colored
    (P := P) (s := Finset.Icc n m) (c := fun j : ℤ => (j : ZMod (r + 1))) (X := Y)
    (σ := 2) (K := Kc) (colorCount := (r : ℝ) + 1)
    (by norm_num) le_rfl hKc hIndepColor
    (fun i _ => hmeas i) (fun i _ => hY i) (fun i _ => hmean i) hSqrt
  -- Rewrite the averaging prefactor into `cesaroAvg` form.
  have hfun :
      (fun ω => ((((Finset.Icc n m).card : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.Icc n m, Y i ω)
        = fun ω => cesaroAvg (fun j => Y j ω) n m := by
    funext ω
    simp only [cesaroAvg, hcard, one_div]
  -- Rewrite the scale.
  have hscale :
      gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
          (Real.sqrt ((r : ℝ) + 1) *
            (Real.sqrt (((Finset.Icc n m).card : ℕ) : ℝ) /
              ((((Finset.Icc n m).card : ℕ) : ℝ)))) * Kc
        = gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((r : ℝ) + 1) * Kc *
            (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
    rw [hcard, sqrt_div_self_eq_rpow_neg_half hcpos]
    ring
  rw [hfun, hscale] at hcolored
  exact hcolored

end CenteredAverage

/-! ## The engine -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The `r`-dependent Cesàro concentration engine.** For an `r`-dependent family
`{X_j}` with `X_j ≤ O_{Γ₂}(K)` and `E X_j ≤ μ₀`, the Cesàro average over a window `[n, m]`
splits as `μ₀` plus a fluctuation of scale `rDepEngineConst r · K · (m − n +
1)^{-1/2}`.

This is the form Step 1 of ABK26 `l.minimal.scale.sep` needs: the same
conclusion as the fully independent engine, with independence weakened to
`r`-dependence. -/
theorem cesaroAvg_isBigO_of_rDependent [IsProbabilityMeasure P]
    (X : ℤ → Ω → ℝ) {K mu0 : ℝ} {r : ℕ} (hK : 0 < K)
    (hdep : RDependent P X r)
    (hmeas : ∀ j, Measurable (X j))
    (hX : ∀ j, IsBigO P (gammaSigma 2) (X j) K)
    (hmean : ∀ j, ∫ ω, X j ω ∂P ≤ mu0)
    (n m : ℤ) (hnm : n ≤ m) :
    ∃ Xfluc : Ω → ℝ,
      (∀ ω, cesaroAvg (fun j => X j ω) n m ≤ mu0 + Xfluc ω) ∧
      IsBigO P (gammaSigma 2) Xfluc
        (rDepEngineConst r * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hσ : (0 : ℝ) < 2 := by norm_num
  have hint : ∀ j, Integrable (X j) P := fun j =>
    integrable_of_isBigO_gammaSigma hσ hK (hmeas j).aemeasurable (hX j)
  have hKc : 0 < cesaroCenterConst 2 * K := mul_pos (cesaroCenterConst_pos hσ) hK
  have hYmeas : ∀ j, Measurable (fun ω => X j ω - ∫ ω', X j ω' ∂P) := fun j =>
    (hmeas j).sub measurable_const
  have hYdep : RDependent P (fun (j : ℤ) (ω : Ω) => X j ω - ∫ ω', X j ω' ∂P) r :=
    hdep.comp (fun (j : ℤ) (x : ℝ) => x - ∫ ω', X j ω' ∂P)
      (fun _ => measurable_id.sub measurable_const)
  have hYtail : ∀ j, IsBigO P (gammaSigma 2)
      (fun ω => X j ω - ∫ ω', X j ω' ∂P) (cesaroCenterConst 2 * K) := fun j =>
    centered_isBigO_gammaSigma_moment hσ hK (hmeas j).aemeasurable (hX j)
  have hYmean : ∀ j, ∫ ω, (X j ω - ∫ ω', X j ω' ∂P) ∂P = 0 := by
    intro j
    rw [MeasureTheory.integral_sub (hint j) (MeasureTheory.integrable_const _)]
    simp
  refine ⟨fun ω => cesaroAvg (fun j => X j ω - ∫ ω', X j ω' ∂P) n m, ?_, ?_⟩
  · intro ω
    exact cesaroAvg_le_add_cesaroAvg_sub (f := fun j => X j ω)
      (g := fun j => ∫ ω', X j ω' ∂P) hnm hmean
  · have hbig := isBigO_cesaroAvg_of_rDependent_centered (P := P)
      (Y := fun (j : ℤ) (ω : Ω) => X j ω - ∫ ω', X j ω' ∂P) hKc hYdep hYmeas hYtail
      hYmean hnm
    have hcst :
        gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((r : ℝ) + 1) * (cesaroCenterConst 2 * K) *
            (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
          = rDepEngineConst r * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
      simp only [rDepEngineConst]; ring
    rwa [hcst] at hbig

/-- **The `r = 2` engine** — the manuscript's regime, and the form Step 1 of
`l.minimal.scale.sep` consumes. -/
theorem cesaroAvg_isBigO_of_twoDependent [IsProbabilityMeasure P]
    (X : ℤ → Ω → ℝ) {K mu0 : ℝ} (hK : 0 < K)
    (hdep : TwoDependent P X)
    (hmeas : ∀ j, Measurable (X j))
    (hX : ∀ j, IsBigO P (gammaSigma 2) (X j) K)
    (hmean : ∀ j, ∫ ω, X j ω ∂P ≤ mu0)
    (n m : ℤ) (hnm : n ≤ m) :
    ∃ Xfluc : Ω → ℝ,
      (∀ ω, cesaroAvg (fun j => X j ω) n m ≤ mu0 + Xfluc ω) ∧
      IsBigO P (gammaSigma 2) Xfluc
        (twoDepEngineConst * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) :=
  cesaroAvg_isBigO_of_rDependent (r := 2) X hK hdep hmeas hX hmean n m hnm

/-- **The `r`-dependent Cesàro engine with an additive boundary/tail term.**
`D̄ ≤ a · avsum X + (m − n + 1)⁻¹ · T` with `T ≤ O_{Γ₂}(b)` gives
`D̄ ≤ a μ₀ + O_{Γ₂}( C (aK + b)(m − n + 1)^{-1/2} )`. -/
theorem cesaroAvg_isBigO_of_rDependent_with_tail [IsProbabilityMeasure P]
    (X : ℤ → Ω → ℝ) (T Dbar : Ω → ℝ) {K mu0 a b : ℝ} {r : ℕ}
    (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdep : RDependent P X r)
    (hmeas : ∀ j, Measurable (X j))
    (hX : ∀ j, IsBigO P (gammaSigma 2) (X j) K)
    (hmean : ∀ j, ∫ ω, X j ω ∂P ≤ mu0)
    (hT : IsBigO P (gammaSigma 2) T b)
    (n m : ℤ) (hnm : n ≤ m)
    (hdom : ∀ ω, Dbar ω ≤ a * cesaroAvg (fun j => X j ω) n m
                    + (1 / (((m - n + 1 : ℤ) : ℝ))) * T ω) :
    ∃ Xdet Xfluc : Ω → ℝ,
      (∀ ω, Dbar ω ≤ Xdet ω + Xfluc ω) ∧
      (∀ ω, Xdet ω ≤ a * mu0) ∧
      IsBigO P (gammaSigma 2) Xfluc
        (rDepTailEngineConst r * (a * K + b)
          * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨Xf, hXfpt, hXfbig⟩ :=
    cesaroAvg_isBigO_of_rDependent (P := P) X hK hdep hmeas hX hmean n m hnm
  have hc1 : (1 : ℝ) ≤ ((m - n + 1 : ℤ) : ℝ) := one_le_window hnm
  have hcpos : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm
  have hpow_nonneg : (0 : ℝ) ≤ (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg hcpos.le _
  refine ⟨fun _ => a * mu0,
    fun ω => a * Xf ω + (1 / (((m - n + 1 : ℤ) : ℝ))) * T ω, ?_, fun _ => le_rfl, ?_⟩
  · intro ω
    have hmul : a * cesaroAvg (fun j => X j ω) n m ≤ a * (mu0 + Xf ω) :=
      mul_le_mul_of_nonneg_left (hXfpt ω) ha
    have hexp : a * (mu0 + Xf ω) = a * mu0 + a * Xf ω := by ring
    linarith only [hdom ω, hmul, hexp.le, hexp.ge]
  · have h1 : IsBigO P (gammaSigma 2) (fun ω => a * Xf ω)
        (a * (rDepEngineConst r * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))) :=
      IsBigO.const_mul ha hXfbig
    have h2 : IsBigO P (gammaSigma 2) (fun ω => (1 / (((m - n + 1 : ℤ) : ℝ))) * T ω)
        ((1 / (((m - n + 1 : ℤ) : ℝ))) * b) :=
      IsBigO.const_mul (by positivity) hT
    have hle : (1 / (((m - n + 1 : ℤ) : ℝ))) * b
        ≤ b * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
      have hmono := inv_le_rpow_neg_half hc1
      have hstep := mul_le_mul_of_nonneg_right hmono hb
      linarith only [hstep]
    have h2' := IsBigO.mono_scale h2 hle
    have hA1 : (0 : ℝ) ≤ a * (rDepEngineConst r * K
        * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
      have hbase : (0 : ℝ) ≤ rDepEngineConst r * K :=
        mul_nonneg (rDepEngineConst_pos r).le hK.le
      exact mul_nonneg ha (mul_nonneg hbase hpow_nonneg)
    have hA2 : (0 : ℝ) ≤ b * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) :=
      mul_nonneg hb hpow_nonneg
    have h3 := isBigO_gammaSigma_add2' (μ := P) (by norm_num : (0 : ℝ) < 2) hA1 hA2 h1 h2'
    refine IsBigO.mono_scale h3 ?_
    have hL : (0 : ℝ) ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
      (Real.rpow_pos_of_pos one_add_log_two_pos _).le
    have hdiff : rDepTailEngineConst r * (a * K + b)
          * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
        - (1 + Real.log 2) ^ (2 : ℝ)⁻¹ *
            (a * (rDepEngineConst r * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))
              + b * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))
        = (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
            * (a * K + rDepEngineConst r * b) := by
      simp only [rDepTailEngineConst]; ring
    have hnn : (0 : ℝ) ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹
        * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) * (a * K + rDepEngineConst r * b) := by
      have h5 : (0 : ℝ) ≤ a * K + rDepEngineConst r * b :=
        add_nonneg (mul_nonneg ha hK.le) (mul_nonneg (rDepEngineConst_pos r).le hb)
      exact mul_nonneg (mul_nonneg hL hpow_nonneg) h5
    linarith only [hdiff, hnn]

end Engine

end

end Algsuperdiff.Probability
