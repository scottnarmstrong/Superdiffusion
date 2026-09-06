import Mathlib

/-!
# Uniqueness of the Laplace transform on bounded continuous functions

A bounded continuous function on the half line is determined by its Laplace
transform: if `g` is continuous and bounded and `∫_{(0,∞)} e^{-λ s} g s ds`
vanishes for every `λ > 0`, then `g` vanishes on `(0, ∞)`.

Mathlib carries no Laplace-transform file, so the argument is written out
here.  Substituting `σ = e^{-s}` turns the transforms at the integer shifts
`λ = n + 2` into the moments of `G σ = σ · g (-log σ)` on `[0,1]`; that
function is continuous, with `G 0 = 0` because `g` is bounded.  All moments of
`G` vanish, hence `∫ p G = 0` for every polynomial `p`; Weierstrass
approximation gives `∫ G² = 0`, and continuity upgrades that to `G = 0` on
`(0,1)`.

The module imports only Mathlib: nothing here is specific to the comparator.
-/

namespace SuperdiffusionAudit.Support.LaplaceUniqueness

open MeasureTheory Set

noncomputable section

/-! ## 1. The substitution `σ = e^{-s}` -/

/-- The negative exponential maps the open half line onto the open unit
interval. -/
theorem image_exp_neg_Ioi : (fun s : ℝ => Real.exp (-s)) '' Ioi 0 = Ioo (0 : ℝ) 1 := by
  ext sigma
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    have : -s < 0 := by simpa using hs
    simpa using Real.exp_lt_one_iff.2 this
  · rintro ⟨h0, h1⟩
    refine ⟨-Real.log sigma, ?_, ?_⟩
    · simpa using Real.log_neg h0 h1
    · show Real.exp (-(-Real.log sigma)) = sigma
      rw [neg_neg, Real.exp_log h0]

/-- **Change of variables** `σ = e^{-s}`: an integral over the open unit
interval is an integral over the half line against the exponential density. -/
theorem integral_Ioo_eq_integral_Ioi (g : ℝ → ℝ) :
    (∫ sigma in Ioo (0 : ℝ) 1, g sigma) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) * g (Real.exp (-s)) := by
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) (Ioi (0 : ℝ)) s := by
    intro s _
    simpa using ((hasDerivAt_neg s).exp).hasDerivWithinAt (s := Ioi (0 : ℝ))
  have hinj : InjOn (fun s : ℝ => Real.exp (-s)) (Ioi (0 : ℝ)) := by
    intro s _ t _ hst
    have := Real.exp_injective hst
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun s : ℝ => Real.exp (-s))
    (f' := fun s : ℝ => -Real.exp (-s)) measurableSet_Ioi hderiv hinj g
  rw [image_exp_neg_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [smul_eq_mul, abs_of_nonpos (neg_nonpos.2 (Real.exp_pos _).le), neg_neg]

/-! ## 2. The moment function -/

/-- The moment function of `g`: the substitution `σ = e^{-s}` carries `g` to
`G σ = σ · g (-log σ)`, whose value at `0` is `0`. -/
def momentFun (g : ℝ → ℝ) (sigma : ℝ) : ℝ := sigma * g (-Real.log sigma)

@[simp] theorem momentFun_zero (g : ℝ → ℝ) : momentFun g 0 = 0 := by
  simp [momentFun]

theorem norm_momentFun_le {g : ℝ → ℝ} {B : ℝ} (hb : ∀ s, |g s| ≤ B) (sigma : ℝ) :
    ‖momentFun g sigma‖ ≤ B * |sigma| := by
  rw [Real.norm_eq_abs, momentFun, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg sigma)

theorem continuous_momentFun {g : ℝ → ℝ} (hc : Continuous g) {B : ℝ}
    (hb : ∀ s, |g s| ≤ B) : Continuous (momentFun g) := by
  rw [continuous_iff_continuousAt]
  intro sigma
  rcases eq_or_ne sigma 0 with rfl | hne
  · have hlim : Filter.Tendsto (fun tau : ℝ => B * |tau|) (nhds (0 : ℝ)) (nhds 0) := by
      simpa using (continuous_const.mul continuous_abs).tendsto (0 : ℝ)
    have := squeeze_zero_norm (fun tau => norm_momentFun_le hb tau) hlim
    simpa [ContinuousAt] using this
  · exact ContinuousAt.mul continuousAt_id
      (hc.continuousAt.comp (Real.continuousAt_log hne).neg)

/-! ## 3. All moments vanish -/

variable {g : ℝ → ℝ}

/-- Every moment of the moment function is a Laplace transform of `g` at an
integer shift, hence vanishes. -/
theorem integral_pow_mul_momentFun
    (h : ∀ lam : ℝ, 0 < lam → (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * g s) = 0) (n : ℕ) :
    (∫ sigma in Ioo (0 : ℝ) 1, sigma ^ n * momentFun g sigma) = 0 := by
  rw [integral_Ioo_eq_integral_Ioi fun sigma => sigma ^ n * momentFun g sigma]
  have hpoint : ∀ s : ℝ,
      Real.exp (-s) * (Real.exp (-s) ^ n * momentFun g (Real.exp (-s))) =
        Real.exp (-((n : ℝ) + 2) * s) * g s := by
    intro s
    have hlog : -Real.log (Real.exp (-s)) = s := by
      rw [Real.log_exp, neg_neg]
    have hexp : Real.exp (-s) ^ (n + 2) = Real.exp (-((n : ℝ) + 2) * s) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc Real.exp (-s) * (Real.exp (-s) ^ n * momentFun g (Real.exp (-s)))
        = Real.exp (-s) ^ (n + 2) * g s := by rw [momentFun, hlog]; ring
      _ = Real.exp (-((n : ℝ) + 2) * s) * g s := by rw [hexp]
  simp only [hpoint]
  exact h ((n : ℝ) + 2) (by positivity)

/-- Testing the moment function against a polynomial gives zero. -/
theorem integral_polynomial_mul_momentFun (hc : Continuous g) {B : ℝ} (hb : ∀ s, |g s| ≤ B)
    (h : ∀ lam : ℝ, 0 < lam → (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * g s) = 0)
    (p : Polynomial ℝ) :
    (∫ sigma in Ioo (0 : ℝ) 1, p.eval sigma * momentFun g sigma) = 0 := by
  have hG : Continuous (momentFun g) := continuous_momentFun hc hb
  have hint : ∀ q : Polynomial ℝ,
      IntegrableOn (fun sigma => q.eval sigma * momentFun g sigma) (Ioo (0 : ℝ) 1) := by
    intro q
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.mono_set Ioo_subset_Icc_self
    exact (q.continuous_aeval.continuousOn).mul hG.continuousOn
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, add_mul]
      rw [integral_add (hint p) (hint q), hp, hq, add_zero]
  | monomial n a =>
      have : ∀ sigma : ℝ, (Polynomial.monomial n a).eval sigma * momentFun g sigma =
          a * (sigma ^ n * momentFun g sigma) := by
        intro sigma
        rw [Polynomial.eval_monomial]
        ring
      simp only [this]
      rw [integral_const_mul, integral_pow_mul_momentFun h n, mul_zero]

/-! ## 4. Weierstrass, and the conclusion -/

/-- The square integral of the moment function vanishes. -/
theorem integral_momentFun_sq (hc : Continuous g) {B : ℝ} (hb : ∀ s, |g s| ≤ B)
    (h : ∀ lam : ℝ, 0 < lam → (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * g s) = 0) :
    (∫ sigma in Ioo (0 : ℝ) 1, momentFun g sigma ^ 2) = 0 := by
  have hG : Continuous (momentFun g) := continuous_momentFun hc hb
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (g 0)) (hb 0)
  have hbound : ∀ sigma ∈ Icc (0 : ℝ) 1, |momentFun g sigma| ≤ B := by
    intro sigma hsigma
    refine le_trans (by simpa using norm_momentFun_le hb sigma) ?_
    rw [abs_of_nonneg hsigma.1]
    simpa using mul_le_mul_of_nonneg_left hsigma.2 hB0
  have hnonneg : 0 ≤ ∫ sigma in Ioo (0 : ℝ) 1, momentFun g sigma ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun sigma _ => sq_nonneg _
  refine le_antisymm ?_ hnonneg
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (momentFun g)
    hG.continuousOn (eps / (B + 1)) (by positivity)
  have hintG : IntegrableOn (fun sigma => (momentFun g sigma - p.eval sigma) * momentFun g sigma)
      (Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.mono_set Ioo_subset_Icc_self
    exact ((hG.continuousOn.sub p.continuous_aeval.continuousOn)).mul hG.continuousOn
  have hintP : IntegrableOn (fun sigma => p.eval sigma * momentFun g sigma)
      (Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.mono_set Ioo_subset_Icc_self
    exact (p.continuous_aeval.continuousOn).mul hG.continuousOn
  have hsplit : (∫ sigma in Ioo (0 : ℝ) 1, momentFun g sigma ^ 2) =
      ∫ sigma in Ioo (0 : ℝ) 1, (momentFun g sigma - p.eval sigma) * momentFun g sigma := by
    have := integral_add hintG hintP
    rw [integral_polynomial_mul_momentFun hc hb h p, add_zero] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioo fun sigma _ => ?_
    ring
  have hle : |∫ sigma in Ioo (0 : ℝ) 1,
      (momentFun g sigma - p.eval sigma) * momentFun g sigma| ≤ eps := by
    have hpoint : ∀ sigma ∈ Ioo (0 : ℝ) 1,
        ‖(momentFun g sigma - p.eval sigma) * momentFun g sigma‖ ≤ eps := by
      intro sigma hsigma
      have hmem : sigma ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hsigma
      have h1 : |momentFun g sigma - p.eval sigma| ≤ eps / (B + 1) := by
        rw [abs_sub_comm]
        exact (hp sigma hmem).le
      have h2 : |momentFun g sigma| ≤ B := hbound sigma hmem
      calc ‖(momentFun g sigma - p.eval sigma) * momentFun g sigma‖
          = |momentFun g sigma - p.eval sigma| * |momentFun g sigma| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ (eps / (B + 1)) * B :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ eps := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [heps.le, hB0]
    have hres := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      (s := Ioo (0 : ℝ) 1) (C := eps) measure_Ioo_lt_top hpoint
    simpa [Real.norm_eq_abs, measureReal_def] using hres
  calc (∫ sigma in Ioo (0 : ℝ) 1, momentFun g sigma ^ 2)
      = ∫ sigma in Ioo (0 : ℝ) 1, (momentFun g sigma - p.eval sigma) * momentFun g sigma :=
        hsplit
    _ ≤ eps := le_trans (le_abs_self _) hle
    _ ≤ 0 + eps := by rw [zero_add]

/-- **Uniqueness of the Laplace transform.**  A bounded continuous function
whose Laplace transform vanishes at every positive shift vanishes on the open
half line. -/
theorem eq_zero_of_integral_exp_neg_mul_eq_zero (hc : Continuous g) {B : ℝ}
    (hb : ∀ s, |g s| ≤ B)
    (h : ∀ lam : ℝ, 0 < lam → (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * g s) = 0)
    {s : ℝ} (hs : 0 < s) : g s = 0 := by
  have hG : Continuous (momentFun g) := continuous_momentFun hc hb
  have hzero : ∀ᵐ sigma ∂(volume.restrict (Ioo (0 : ℝ) 1)), momentFun g sigma ^ 2 = 0 := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun sigma => momentFun g sigma ^ 2 :=
      Filter.Eventually.of_forall fun sigma => sq_nonneg _
    have hint : IntegrableOn (fun sigma => momentFun g sigma ^ 2) (Ioo (0 : ℝ) 1) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.mono_set Ioo_subset_Icc_self
      exact (hG.continuousOn.pow 2)
    exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1
      (integral_momentFun_sq hc hb h)
  have hae : momentFun g =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ => (0 : ℝ) := by
    filter_upwards [hzero] with sigma hsigma
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsigma
  have heq : EqOn (momentFun g) (fun _ => (0 : ℝ)) (Ioo (0 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hG.continuousOn continuousOn_const
  have hmem : Real.exp (-s) ∈ Ioo (0 : ℝ) 1 := by
    rw [← image_exp_neg_Ioi]
    exact ⟨s, hs, rfl⟩
  have := heq hmem
  rw [momentFun, Real.log_exp, neg_neg] at this
  have hpos : Real.exp (-s) ≠ 0 := (Real.exp_pos _).ne'
  exact (mul_eq_zero.1 this).resolve_left hpos

/-- Two bounded continuous functions with the same Laplace transform agree on
the open half line. -/
theorem eq_of_integral_exp_neg_mul_eq {g1 g2 : ℝ → ℝ} (hc1 : Continuous g1)
    (hc2 : Continuous g2) {B : ℝ} (hb1 : ∀ s, |g1 s| ≤ B) (hb2 : ∀ s, |g2 s| ≤ B)
    (h : ∀ lam : ℝ, 0 < lam →
      (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * g1 s) =
        ∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * g2 s)
    {s : ℝ} (hs : 0 < s) : g1 s = g2 s := by
  have hb : ∀ t, |(g1 - g2) t| ≤ B + B := by
    intro t
    exact le_trans (abs_sub _ _) (add_le_add (hb1 t) (hb2 t))
  have hzero : ∀ lam : ℝ, 0 < lam →
      (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * (g1 - g2) t) = 0 := by
    intro lam hlam
    have hint1 : IntegrableOn (fun t => Real.exp (-lam * t) * g1 t) (Ioi (0 : ℝ)) := by
      have h1 := (exp_neg_integrableOn_Ioi (0 : ℝ) hlam).bdd_mul (f := g1) (c := B)
        hc1.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hb1 t)
      simpa [IntegrableOn, mul_comm] using h1
    have hint2 : IntegrableOn (fun t => Real.exp (-lam * t) * g2 t) (Ioi (0 : ℝ)) := by
      have h2 := (exp_neg_integrableOn_Ioi (0 : ℝ) hlam).bdd_mul (f := g2) (c := B)
        hc2.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hb2 t)
      simpa [IntegrableOn, mul_comm] using h2
    have : (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * (g1 - g2) t) =
        (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * g1 t) -
          ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * g2 t := by
      rw [← integral_sub hint1 hint2]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp [Pi.sub_apply, mul_sub]
    rw [this, h lam hlam, sub_self]
  have := eq_zero_of_integral_exp_neg_mul_eq_zero (hc1.sub hc2) hb hzero hs
  have hsub : g1 s - g2 s = 0 := by simpa [Pi.sub_apply] using this
  linarith

end

end SuperdiffusionAudit.Support.LaplaceUniqueness
