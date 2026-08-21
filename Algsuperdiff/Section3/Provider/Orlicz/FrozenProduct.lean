import Algsuperdiff.Section3.Provider.Orlicz.WeightedSubgaussian
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Frozen-scale product tails

Internal Fubini transport for the corrected shell-pair estimate. A random
Gamma-two frozen scale and a Gamma-two tail on every frozen slice combine into
a Gamma-one tail on the product law. This is provider infrastructure only.
-/

open MeasureTheory
open Homogenization Homogenization.IndependentSums

namespace Algsuperdiff.Section3.Provider.Orlicz

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {P : Measure α} {Q : Measure β}

/-- Transport a tail of `X ∘ f` to the pushed-forward law. -/
theorem isBigO_map_of_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → α} {X : α → ℝ} {A σ : ℝ}
    (hf : Measurable f) (hX : Measurable X)
    (h : IsBigO μ (gammaSigma σ) (fun ω => X (f ω)) A) :
    IsBigO (μ.map f) (gammaSigma σ) X A := by
  rw [isBigO_gammaSigma_iff] at h ⊢
  intro t ht
  have hset : MeasurableSet (absTailEvent X (A * t)) :=
    measurableSet_lt measurable_const hX.norm
  change ((μ.map f) (absTailEvent X (A * t))).toReal ≤ _
  rw [Measure.map_apply hf hset]
  exact h ht

/-- Pull a tail on a pushed-forward law back to the original variable. -/
theorem isBigO_comp_of_map {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → α} {X : α → ℝ} {A σ : ℝ}
    (hf : Measurable f) (hX : Measurable X)
    (h : IsBigO (μ.map f) (gammaSigma σ) X A) :
    IsBigO μ (gammaSigma σ) (fun ω => X (f ω)) A := by
  rw [isBigO_gammaSigma_iff] at h ⊢
  intro t ht
  have hset : MeasurableSet (absTailEvent X (A * t)) :=
    measurableSet_lt measurable_const hX.norm
  change (μ (f ⁻¹' absTailEvent X (A * t))).toReal ≤ _
  rw [← Measure.map_apply hf hset]
  exact h ht

/-- Product-Fubini multiplication for a random frozen scale.  If every frozen
slice `b ↦ F(a,b)` has a `Γ_{σ₁}` tail at scale `A a`, and `A` itself has a
`Γ_{σ₂}` tail at scale `B`, then `F` has the expected `Γ_{σ₁σ₂/(σ₁+σ₂)}` tail
on `P.prod Q`. -/
theorem isBigO_gammaSigma_frozen_product
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {F : α × β → ℝ} {A : α → ℝ} {B σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hAmeas : Measurable A) (hFmeas : Measurable F)
    (hAnn : ∀ a, 0 ≤ A a)
    (hA : IsBigO P (gammaSigma σ₂) A B)
    (hF : ∀ᵐ a ∂P, IsBigO Q (gammaSigma σ₁) (fun b => F (a, b)) (A a)) :
    IsBigO (P.prod Q) (gammaSigma ((σ₁ * σ₂ / (σ₁ + σ₂)))) F
      (Book.Ch04.gammaProductConst σ₁ σ₂ * B) := by
  classical
  rw [isBigO_gammaSigma_iff]
  intro t ht
  set σ₃ : ℝ := (σ₁ * σ₂ / (σ₁ + σ₂)) with hσ₃def
  set θ : ℝ := σ₂ / (σ₁ + σ₂) with hθdef
  set c : ℝ := Book.Ch04.gammaProductConst σ₁ σ₂ with hcdef
  set s : ℝ := c * t with hsdef
  have hσ₃ : 0 < σ₃ := by
    rw [hσ₃def]
    exact div_pos (mul_pos hσ₁ hσ₂) (add_pos hσ₁ hσ₂)
  have hθ0 : 0 ≤ θ := div_nonneg hσ₂.le (add_pos hσ₁ hσ₂).le
  have h1θ0 : 0 ≤ 1 - θ := by
    rw [hθdef]
    have hle : σ₂ ≤ σ₁ + σ₂ := by linarith
    exact sub_nonneg.mpr ((div_le_one (add_pos hσ₁ hσ₂)).mpr hle)
  have hθσ₁ : θ * σ₁ = σ₃ := by
    rw [hθdef, hσ₃def]
    ring
  have h1θσ₂ : (1 - θ) * σ₂ = σ₃ := by
    rw [hθdef, hσ₃def]
    field_simp
    ring
  have hcpos : 0 < c := by
    rw [hcdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    exact Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hσ₃.le)
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    exact one_le_mul_of_one_le_of_one_le hc1 ht
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hsθ1 : 1 ≤ s ^ θ := Real.one_le_rpow hs1 hθ0
  have hs1θ1 : 1 ≤ s ^ (1 - θ) := Real.one_le_rpow hs1 h1θ0
  let E : Set (α × β) :=
    absTailEvent F (B * s)
  let EA : Set α := absTailEvent A (B * s ^ (1 - θ))
  let EF : Set (α × β) :=
    {p | A p.1 * s ^ θ < |F p|}
  have hEmeas : MeasurableSet E :=
    measurableSet_lt measurable_const hFmeas.norm
  have hEFmeas : MeasurableSet EF := by
    exact measurableSet_lt ((hAmeas.comp measurable_fst).mul_const _) hFmeas.norm
  have hsub : E ⊆ (EA ×ˢ Set.univ) ∪ EF := by
    intro p hp
    by_cases ha : p.1 ∈ EA
    · exact Set.mem_union_left _ (Set.mk_mem_prod ha (by simp))
    · right
      rw [mem_absTailEvent, not_lt] at ha
      change B * s < |F p| at hp
      change A p.1 * s ^ θ < |F p|
      by_contra hnot
      have hnot' : |F p| ≤ A p.1 * s ^ θ := le_of_not_gt hnot
      have hprod : |F p| ≤ (B * s ^ (1 - θ)) * (s ^ θ) := by
        have hAupper : A p.1 ≤ B * s ^ (1 - θ) := by
          simpa only [EA, abs_of_nonneg (hAnn p.1)] using ha
        exact le_trans hnot' (mul_le_mul_of_nonneg_right hAupper
          (Real.rpow_nonneg hspos.le _))
      have hpow : s ^ (1 - θ) * s ^ θ = s := by
        rw [← Real.rpow_add hspos]
        rw [show 1 - θ + θ = (1 : ℝ) by ring, Real.rpow_one]
      have hlevel : (B * s ^ (1 - θ)) * s ^ θ = B * s := by
        rw [show (B * s ^ (1 - θ)) * s ^ θ = B * (s ^ (1 - θ) * s ^ θ) by ring, hpow]
      rw [hlevel] at hprod
      exact absurd hp (not_lt.mpr hprod)
  have htailA := (isBigO_gammaSigma_iff.mp hA) hs1θ1
  have hAexp : P.real EA ≤ Real.exp (-(s ^ σ₃)) := by
    change P.real (absTailEvent A (B * s ^ (1 - θ))) ≤ _
    simpa only [← Real.rpow_mul hspos.le, h1θσ₂] using htailA
  have htailF : ∀ᵐ a ∂P,
      Q.real (Prod.mk a ⁻¹' EF) ≤ Real.exp (-(s ^ σ₃)) := by
    filter_upwards [hF] with a hFa
    have hslice : Prod.mk a ⁻¹' EF =
        absTailEvent (fun b => F (a, b)) (A a * s ^ θ) := by
      ext b
      rfl
    rw [hslice]
    have ht := (isBigO_gammaSigma_iff.mp hFa) hsθ1
    rw [show (s ^ θ) ^ σ₁ = s ^ σ₃ by
      rw [← Real.rpow_mul hspos.le, hθσ₁]] at ht
    exact ht
  have hEFbound : (P.prod Q).real EF ≤ Real.exp (-(s ^ σ₃)) := by
    have hENN : P.prod Q EF ≤ ENNReal.ofReal (Real.exp (-(s ^ σ₃))) := by
      rw [MeasureTheory.Measure.prod_apply hEFmeas]
      calc
        (∫⁻ a, Q (Prod.mk a ⁻¹' EF) ∂P)
            ≤ ∫⁻ _ : α, ENNReal.ofReal (Real.exp (-(s ^ σ₃))) ∂P := by
              apply lintegral_mono_ae
              filter_upwards [htailF] with a hta
              rw [← ENNReal.ofReal_toReal (measure_ne_top Q _)]
              exact ENNReal.ofReal_le_ofReal hta
        _ = ENNReal.ofReal (Real.exp (-(s ^ σ₃))) := by simp
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    simpa only [MeasureTheory.Measure.real, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hreal
  have hEAprod : (P.prod Q).real (EA ×ˢ Set.univ) ≤ Real.exp (-(s ^ σ₃)) := by
    rw [measureReal_prod_prod]
    simp only [MeasureTheory.Measure.real, measure_univ, ENNReal.toReal_one, mul_one]
    exact hAexp
  have hUnion : (P.prod Q).real ((EA ×ˢ Set.univ) ∪ EF)
      ≤ Real.exp (-(s ^ σ₃)) + Real.exp (-(s ^ σ₃)) :=
    le_trans (measureReal_union_le _ _) (add_le_add hEAprod hEFbound)
  have hmono := measureReal_mono hsub (measure_ne_top (P.prod Q) _)
  have hcσ₃ : c ^ σ₃ = 2 := by
    rw [hcdef, Book.Ch04.gammaProductConst, ← hσ₃def,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      inv_mul_cancel₀ hσ₃.ne', Real.rpow_one]
  have hsσ₃ : s ^ σ₃ = 2 * t ^ σ₃ := by
    rw [hsdef, Real.mul_rpow hcpos.le (le_trans zero_le_one ht), hcσ₃]
  have hfold : 2 * Real.exp (-(s ^ σ₃)) ≤ Real.exp (-(t ^ σ₃)) := by
    rw [hsσ₃]
    simpa only [neg_mul] using
      IndependentSums.two_mul_exp_neg_two_mul_le_exp_neg
        (Real.one_le_rpow ht hσ₃.le)
  have hlevel : B * s = c * B * t := by rw [hsdef]; ring
  change (P.prod Q).real (absTailEvent F (c * B * t)) ≤ Real.exp (-(t ^ σ₃))
  rw [← hlevel]
  calc
    (P.prod Q).real E ≤ (P.prod Q).real ((EA ×ˢ Set.univ) ∪ EF) := hmono
    _ ≤ Real.exp (-(s ^ σ₃)) + Real.exp (-(s ^ σ₃)) := hUnion
    _ = 2 * Real.exp (-(s ^ σ₃)) := by ring
    _ ≤ Real.exp (-(t ^ σ₃)) := hfold


end Algsuperdiff.Section3.Provider.Orlicz
