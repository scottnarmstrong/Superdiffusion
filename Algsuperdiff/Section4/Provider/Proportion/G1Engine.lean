/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.RowSumFinite
import Algsuperdiff.Section4.Provider.Proportion.ShellColumnIndep

/-!
# The single-shell array engine behind both `𝒢₁` lanes

This module is the common engine: it takes such an array, together with a
uniform `Γ_σ` tail for its entries and a deterministic reduction of the lane's
bad event, and returns the lane's proportion tail in the consumer's shape.  Both
Appendix-D hypotheses are discharged inside:

* `hmomL` from the entries' `Γ_σ` tails and the normalizer (proved
  `lintegral_rpow_le_one_of_array`, stated at the two-index shape);
* `hindep` from (J1) alone (`columnsIndep_of_shellColumn`) — no separation
  geometry, no dimension restriction, and valid for every `r ≥ 1`.

What remains a caller obligation is the *deterministic* domination of the lane's
bad event by the Appendix-D row sum.  Because `ScalesConcentration.Yk` is a real
`tsum` (which reads `0` off summability), that domination is supplied here in
`ℝ≥0∞` and converted on a full-measure set, exactly as the `𝒢₀` lane does: the
two first moments are finite, so the rows are a.s. finite, and the enlargement
`Ev m ∪ N` costs nothing (`measure_scaleProp_le_of_null_enlargement`).

## References

* ABK26, `l.ratio.of.good.scales.for.k`.
* ABK26, `p.concentration.for.scales` and Appendix D.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two-sided geometric row weight -/

theorem summable_wtRow {sprime : ℝ} (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1) (m : ℤ) :
    Summable fun j : ℤ => wt sprime m j := by
  have h := summable_wt_half (s := 2 * sprime) (by linarith only [hs0]) hs2 m
  simpa only [show (2 * sprime / 2 : ℝ) = sprime from by ring] using h

theorem tsum_wtRow_le {sprime : ℝ} (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1) (m : ℤ) :
    ∑' j : ℤ, wt sprime m j ≤ 3 / sprime := by
  have h := sum_wt_half_le (s := 2 * sprime) (by linarith only [hs0]) hs2 m
  simp only [show (2 * sprime / 2 : ℝ) = sprime from by ring] at h
  refine h.trans (le_of_eq ?_)
  field_simp
  norm_num

/-! ## 2. The Appendix-D row of a two-index array, formed in `ℝ≥0∞` -/

/-- The two-sided Appendix-D row sum of a two-index array, formed in `ℝ≥0∞`
(total, no summability side condition). -/
def rowGE (G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ) (sprime : ℝ) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * G m j omega)

theorem measurable_rowGE {G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ}
    (hGm : ∀ m j, Measurable (G m j)) (sprime : ℝ) (m : ℤ) :
    Measurable (rowGE G sprime m) := by
  have hrw : rowGE G sprime m = fun omega =>
      ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * G m j omega) := rfl
  rw [hrw]
  exact Measurable.ennreal_tsum fun j => ((hGm m j).const_mul _).ennreal_ofReal

/-- **The row has a finite first moment.**  Tonelli over the `ℤ`-row against the
uniform `Γ_σ` tail of the entries and the summable geometric weights. -/
theorem lintegral_rowGE_le (M : ABKModel d)
    {G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ} {sigma sprime K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1)
    (hGnn : ∀ m j omega, 0 ≤ G m j omega) (hGm : ∀ m j, Measurable (G m j))
    (hGtail : ∀ m j, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigma) (G m j) K)
    (m : ℤ) :
    ∫⁻ omega, rowGE G sprime m omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3 / sprime * (gammaMomentConst sigma * K)) := by
  classical
  have hcst : (0 : ℝ) ≤ gammaMomentConst sigma * K :=
    mul_nonneg (gammaMomentConst_pos hsigma).le hK.le
  have hstep : ∫⁻ omega, rowGE G sprime m omega ∂(Cutoff.cutoffSampleLaw M).toMeasure
      = ∑' j : ℤ, ∫⁻ omega, ENNReal.ofReal (wt sprime m j * G m j omega)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hrw : rowGE G sprime m = fun omega =>
        ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * G m j omega) := rfl
    rw [hrw]
    exact lintegral_tsum fun j => (((hGm m j).const_mul _).ennreal_ofReal).aemeasurable
  have hterm : ∀ j : ℤ,
      ∫⁻ omega, ENNReal.ofReal (wt sprime m j * G m j omega)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (wt sprime m j * (gammaMomentConst sigma * K)) := by
    intro j
    have hw : (0 : ℝ) ≤ wt sprime m j := wt_nonneg sprime m j
    have hsplit : (fun omega => ENNReal.ofReal (wt sprime m j * G m j omega))
        = fun omega => ENNReal.ofReal (wt sprime m j) *
            ENNReal.ofReal (G m j omega) :=
      funext fun omega => ENNReal.ofReal_mul hw
    rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmom := lintegral_ofReal_le_of_isBigOWith hsigma hK
      (fun omega => hGnn m j omega) (hGm m j).aemeasurable (hGtail m j)
    calc ENNReal.ofReal (wt sprime m j) *
            ∫⁻ omega, ENNReal.ofReal (G m j omega)
              ∂(Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (wt sprime m j) *
            ENNReal.ofReal (gammaMomentConst sigma * K) := mul_le_mul_right hmom _
      _ = ENNReal.ofReal (wt sprime m j * (gammaMomentConst sigma * K)) :=
          (ENNReal.ofReal_mul hw).symm
  have hsum' : Summable fun j : ℤ => wt sprime m j * (gammaMomentConst sigma * K) :=
    (summable_wtRow hs0 hs2 m).mul_right _
  rw [hstep]
  calc ∑' j : ℤ, ∫⁻ omega, ENNReal.ofReal (wt sprime m j * G m j omega)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ∑' j : ℤ, ENNReal.ofReal (wt sprime m j * (gammaMomentConst sigma * K)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℤ, wt sprime m j * (gammaMomentConst sigma * K)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (wt_nonneg sprime m j) hcst) hsum').symm
    _ ≤ ENNReal.ofReal (3 / sprime * (gammaMomentConst sigma * K)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_right]
        exact mul_le_mul_of_nonneg_right (tsum_wtRow_le hs0 hs2 m) hcst

/-! ## 3. The null set on which the real row sum is the honest series -/

/-- The full-measure set on which every Appendix-D row of the array is finite. -/
def goodRowG (G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ) (sprime : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  {omega | ∀ m : ℤ, rowGE G sprime m omega ≠ ⊤}

theorem measurableSet_goodRowG {G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ}
    (hGm : ∀ m j, Measurable (G m j)) (sprime : ℝ) :
    MeasurableSet (goodRowG G sprime) := by
  have hrw : goodRowG G sprime = ⋂ m : ℤ, {omega | rowGE G sprime m omega ≠ ⊤} := by
    ext omega
    simp only [goodRowG, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hrw]
  refine MeasurableSet.iInter fun m => ?_
  exact (measurable_rowGE hGm sprime m (measurableSet_singleton (⊤ : ℝ≥0∞))).compl

private theorem measure_rowGE_top (M : ABKModel d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≠ ⊤) :
    (Cutoff.cutoffSampleLaw M).toMeasure {omega | f omega = ⊤} = 0 := by
  have h := ae_lt_top (μ := (Cutoff.cutoffSampleLaw M).toMeasure) hf hfin
  rw [MeasureTheory.ae_iff] at h
  refine measure_mono_null (fun omega homega => ?_) h
  rw [Set.mem_setOf_eq] at homega ⊢
  rw [homega]
  exact lt_irrefl _

/-- **The enlargement's null set is null**, by first moments alone: countably
many rows, each with a finite expectation. -/
theorem measure_compl_goodRowG (M : ABKModel d)
    {G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ} {sigma sprime K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) (hs0 : 0 < sprime) (hs2 : 2 * sprime ≤ 1)
    (hGnn : ∀ m j omega, 0 ≤ G m j omega) (hGm : ∀ m j, Measurable (G m j))
    (hGtail : ∀ m j, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigma) (G m j) K) :
    (Cutoff.cutoffSampleLaw M).toMeasure (goodRowG G sprime)ᶜ = 0 := by
  have hcompl : (goodRowG G sprime)ᶜ =
      ⋃ m : ℤ, {omega | rowGE G sprime m omega = ⊤} := by
    ext omega
    simp only [goodRowG, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion,
      not_forall, not_not]
  rw [hcompl]
  refine measure_iUnion_null fun m => ?_
  refine measure_rowGE_top M (measurable_rowGE hGm sprime m) ?_
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_rowGE_le M hsigma hK hs0 hs2 hGnn hGm hGtail m)

/-! ## 4. From the `ℝ≥0∞` row to `ScalesConcentration.Yk` -/

/-- **The `ℝ≥0∞`-to-`ℝ` conversion of the Appendix-D row.**  On the finiteness
set, a strict lower bound for the `ℝ≥0∞` row is a strict lower bound for the real
normalized row `Yk`. -/
theorem lt_Yk_of_lt_rowGE {G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ}
    {sprime D lam : ℝ} (hD : 0 < D) (hlam : 0 ≤ lam) (m : ℤ)
    {omega : Cutoff.CutoffSample d} (hnn : ∀ j : ℤ, 0 ≤ G m j omega)
    (hfin : rowGE G sprime m omega ≠ ⊤)
    (hlt : ENNReal.ofReal (D * lam) < rowGE G sprime m omega) :
    lam < Yk (fun m j omega => D⁻¹ * G m j omega) sprime m omega := by
  have htoReal : (rowGE G sprime m omega).toReal
      = ∑' j : ℤ, wt sprime m j * G m j omega := by
    rw [rowGE, ENNReal.tsum_toReal_eq (fun _j => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun j =>
      ENNReal.toReal_ofReal (mul_nonneg (wt_nonneg _ m j) (hnn j))
  have hlt' : D * lam < (rowGE G sprime m omega).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).2 hlt
    rwa [ENNReal.toReal_ofReal (mul_nonneg hD.le hlam)] at h
  have hYk : Yk (fun m j omega => D⁻¹ * G m j omega) sprime m omega
      = D⁻¹ * ∑' j : ℤ, wt sprime m j * G m j omega := by
    rw [Yk, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [hYk, ← htoReal, inv_mul_eq_div, lt_div_iff₀ hD]
  linarith only [hlt']

/-! ## 5. The lane engine -/

/-- **The proportion tail of one `𝒢₁` lane, in the consumer's shape.**

Both Appendix-D hypotheses are discharged inside: the unit moments from the
entries' `Γ_σ` tails and the normalizer, and the columns' independence from (J1)
alone, at the caller's `r ≥ 1`.  `hreduce` is the lane's deterministic reduction,
and `hnorm`, `hrate`, `hthetar` are the parameter conditions. -/
theorem ratioTail_of_shellArray (M : ABKModel d)
    (Ev : ℤ → Set (Cutoff.CutoffSample d)) (G : ℤ → ℤ → Cutoff.CutoffSample d → ℝ)
    {sigma p sprime theta c1 K D Q : ℝ} {r : ℕ}
    (hsigma : 0 < sigma) (hK : 0 < K) (hD : 0 < D)
    (hp : 1 ≤ p) (hs' : 0 < sprime) (hs'1 : sprime ≤ 1) (hsp : 1 ≤ sprime * p)
    (hr1 : 1 ≤ r) (hQ : 1 ≤ Q) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hrate : Real.log (Q * (r : ℝ)) + c1 * (r : ℝ) ≤ sprime * p * theta / (16 * (r : ℝ)))
    (hGnn : ∀ m j omega, 0 ≤ G m j omega)
    (hGloc : ∀ m j, Measurable[shellSigma d j] (G m j))
    (hGtail : ∀ m j, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma sigma) (G m j) K)
    (hnorm : gammaMomentConst sigma * p ^ sigma⁻¹ * K ≤ D)
    (hreduce : ∀ m : ℤ, 0 ≤ m → ∀ omega ∈ (Ev m)ᶜ,
      9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) <
        Yk (fun m j omega => D⁻¹ * G m j omega) sprime m omega)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  have hGm : ∀ m j : ℤ, Measurable (G m j) := fun m j =>
    (hGloc m j).mono (shellSigma_le j) le_rfl
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have htheta1 : theta ≤ 1 := by nlinarith only [hthetar, htheta0, hr1R]
  have hXmeas : ∀ k j : ℤ,
      Measurable ((fun m j omega => D⁻¹ * G m j omega) k j) :=
    fun k j => (hGm k j).const_mul _
  have hXnn : ∀ (k j : ℤ) (omega : Cutoff.CutoffSample d),
      0 ≤ (fun m j omega => D⁻¹ * G m j omega) k j omega := fun k j omega =>
    mul_nonneg (inv_nonneg.2 hD.le) (hGnn k j omega)
  have hmomL := IndicatorDensity.lintegral_rpow_le_one_of_array
    (P := (Cutoff.cutoffSampleLaw M).toMeasure) (Y := G) hsigma hK hp hD hGnn
    (fun m j => (hGm m j).aemeasurable) hGtail hnorm
  have hindep : ColumnsIndep (Cutoff.cutoffSampleLaw M).toMeasure
      (fun m j omega => D⁻¹ * G m j omega) r :=
    columnsIndep_of_shellColumn M _ hr1 fun m j => (hGloc m j).const_mul _
  have hconc : ∀ Mw : ℕ, (r : ℤ) ≤ (Mw : ℤ) →
      (Cutoff.cutoffSampleLaw M).toMeasure
          (concEvent (fun m j omega => D⁻¹ * G m j omega) p sprime theta Cstar Mw)
        ≤ ENNReal.ofReal
            (Real.exp (-(sprime * p * theta) / (16 * (r : ℝ)) * ((Mw : ℝ) + 1))) :=
    fun Mw hMw => p_concentration_for_scales_Cstar _ _ hp hs' hs'1 hsp hr1
      hXmeas hXnn hmomL hindep Mw theta hMw htheta0 htheta1
  exact ratioTail_of_concentration _ _ Ev hr1 hQ htheta0 hthetar hc1 hrate hconc
    hreduce n

end

end Algsuperdiff.Section4.Provider.Proportion
