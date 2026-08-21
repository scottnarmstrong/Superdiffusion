/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.MomentEngine
import Algsuperdiff.Section4.Provider.Proportion.AtomTail
import Algsuperdiff.Section4.Provider.Localize.GaugeAntitone
import Algsuperdiff.Section4.Provider.Localize.SensitivitySwitch

/-!
# Step 4's bullet (B5): the `λ`-slot display and its `q`-th moments

## The printed bullet

```
λ_{γ,2}^{-1}(□_j ; 𝐚_{j−2}) ≤ C σ̄_{j−1}^{-1} + 𝒪_{Γ_{1/3}}(C σ̄_{j−1}^{-1}exp(−C^{-1}γ^{-1}))
E[λ_{γ,2}^{-q}(□_j ; 𝐚_{j−2})]^{1/q} ≤ C σ̄_{j−1}^{-1}(1 + C q³ exp(−C^{-1}γ^{-1}))
```

the `q³` being `q^{1/σ}` at `σ = 1/3`.

## What is delivered, and the ONE index that does not match

The whole display is produced from the Section 3 anchor
`Frozen.Section3.coarse_ellipticity_bounds` through the proved
`Proportion.AtomTail`, whose `exists_cgExcess_atomTail` already discharges the
induction state and both `E`-window premises of `p.cg.ellipticity.bounds` (the
all-scales budget at the floor `(3/2)·exp(3C_cg)`).

**The index mismatch.**  The proposition is `sup_{L ≥ m−1}
λ_{s,q}^{-1}(□_m ; 𝐚_L) σ̄_{m−1}` (frozen at the family base `m − 1`).
Reading it at the cube `□_j` forces `m = j`, hence `σ̄_{j−1}` — which is
exactly the printed right-hand side — but also `L ≥ j − 1`, whereas the printed
left-hand side carries the field `𝐚_{j−2}`.  The two readings cannot both hold:
at `m = j − 1` the field index `j − 2` is admissible but the cube becomes
`□_{j−1}` and the gauge becomes `σ̄_{j−2}`.  The statements below are therefore
delivered at the anchor's own matched pair `(□_{k−2}, 𝐚_{k−2}, σ̄_{k−3})`, i.e. at
`k = j + 2` in the Step-4 indices: cube `□_j`, gauge `σ̄_{j−1}` — both printed
— and field `𝐚_j` in place of the printed `𝐚_{j−2}`.  The missing step is a
domain/field upscaling for `λ^{-1}`, the (B5) analogue of (B4)'s; it is not
performed here, but in `LambdaIndexUpscale.lean`.

## The gauge

The displays are at the printed gauge `γ`.  Here that direction is the useful
one: `..._twoGamma` below transports every bound proved at `γ` to the gapped
gauge at constant `1`.  The converse is NOT available and is not claimed.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (bullet (B5)); `p.cg.ellipticity.bounds`;
  `l.moments.gamma.psi`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The `σ = 1/3` moment majorant -/

/-- The `q^{1/σ}` of `l.moments.gamma.psi` at `σ = 1/3` is `q³` -- the printed
cubic factor of bullet (B5). -/
theorem gammaMomentBound_third_eq (p A : ℝ) :
    gammaMomentBound (1 / 3) p A = gammaMomentConst (1 / 3) * p ^ (3 : ℝ) * A := by
  have he : (((1 : ℝ)) / 3)⁻¹ = (3 : ℝ) := by norm_num
  rw [gammaMomentBound, he]

/-! ## 2. The deterministic rearrangement -/

/-- **The bullet's shape, pointwise.**

`λ_{γ,2}^{-1}(z+□_{k−2} ; 𝐚_{k−2}) ≤ σ̄_{k−3}^{-1}C + σ̄_{k−3}^{-1}𝒳_{k−2}(z)`,
where `𝒳` is `Localize.cgExcess`, the `𝒢₀` bracket.  This is the algebraic
content of bullet (B5): the anchor controls `σ̄_{k−3}λ^{-1}` and the bullet
divides by `σ̄_{k−3}`.  In the Step-4 indices `k = j + 2`: cube `□_j`, gauge
`σ̄_{j−1}`. -/
theorem lambdaAnnulusAtom_le_inv_sigmaBar_mul_add (M : ABKModel d) (Ccg : ℝ)
    (k : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d) :
    Support.lambdaAnnulusAtom M k z omega ≤
      ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ * Ccg +
        ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
          Localize.cgExcess M Ccg (k - 2) z omega := by
  have hS : (0 : ℝ) < (Annealed.sigmaBar M (k - 3) : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M (k - 3)
  have hkey : (Annealed.sigmaBar M (k - 3) : ℝ) *
      Support.lambdaAnnulusAtom M k z omega - Ccg ≤
      Localize.cgExcess M Ccg (k - 2) z omega := by
    rw [Localize.cgExcess_sub_two]
    exact le_max_left _ _
  have hprod : (Annealed.sigmaBar M (k - 3) : ℝ) *
      Support.lambdaAnnulusAtom M k z omega ≤
      Ccg + Localize.cgExcess M Ccg (k - 2) z omega := by
    linarith only [hkey]
  have hfirst : Support.lambdaAnnulusAtom M k z omega =
      ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
        ((Annealed.sigmaBar M (k - 3) : ℝ) *
          Support.lambdaAnnulusAtom M k z omega) := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hS), one_mul]
  calc Support.lambdaAnnulusAtom M k z omega
      = ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
          ((Annealed.sigmaBar M (k - 3) : ℝ) *
            Support.lambdaAnnulusAtom M k z omega) := hfirst
    _ ≤ ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
          (Ccg + Localize.cgExcess M Ccg (k - 2) z omega) :=
        mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hS.le)
    _ = ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ * Ccg +
          ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
            Localize.cgExcess M Ccg (k - 2) z omega := by ring

/-- The `𝒢₀` bracket is measurable in the sample (through the proved measurability
of the `λ`-literal at a translated centre). -/
theorem measurable_cgExcess (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (z : Vec d) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      Localize.cgExcess M Ccg (k - 2) z omega := by
  have hfun : (fun omega : Cutoff.CutoffSample d =>
        Localize.cgExcess M Ccg (k - 2) z omega) =
      fun omega : Cutoff.CutoffSample d =>
        max ((Annealed.sigmaBar M (k - 3) : ℝ) *
          Support.lambdaAnnulusAtom M k z omega - Ccg) 0 :=
    funext fun omega => Localize.cgExcess_sub_two M Ccg k z omega
  rw [hfun]
  exact (((Support.measurable_lambdaAnnulusAtom M k z).const_mul _).sub_const
    _).max measurable_const

/-- The Orlicz half of the bullet, with the `σ̄_{k−3}^{-1}` factor moved onto the
amplitude: `σ̄_{k−3}^{-1}𝒳 ≤ 𝒪_{Γ_{1/3}}(σ̄_{k−3}^{-1}exp(−(C_cg C²)^{-1}c⋆²γ^{-1}))`,
the printed `𝒪_{Γ_{1/3}}(Cσ̄_{j−1}^{-1}exp(−C^{-1}γ^{-1}))`. -/
theorem isBigOWith_inv_sigmaBar_mul_cgExcess (M : ABKModel d) {Ccg A : ℝ}
    (k : ℤ) (z : Vec d)
    (h : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (fun omega => Localize.cgExcess M Ccg (k - 2) z omega) A) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (fun omega => ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
        Localize.cgExcess M Ccg (k - 2) z omega)
      (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ * A) :=
  IsBigOWith.const_mul
    (inv_nonneg.mpr (Provider.Orlicz.sigmaBar_pos M (k - 3)).le) h

/-! ## 3. The moment conversion at the anchor's own premises -/

/-- **(B5) at every moment `q ∈ [1,∞)`, at the anchor's own premises.**

```
E[λ_{γ,2}^{-q}(z+□_{k−2} ; 𝐚_{k−2})]^{1/q}
  ≤ σ̄_{k−3}^{-1}C_cg + C(1/3) q³ σ̄_{k−3}^{-1}exp(−(C_cg^{-1}E^{-2}γ^{-1})) ,
```
the printed `C σ̄_{j−1}^{-1}(1 + C q³ exp(−C^{-1}γ^{-1}))` with the two
summands kept apart (the printed factorization is a constant rearrangement,
performed by the consumer).

Hypotheses: exactly the `p.cg.ellipticity.bounds` premises of
`Proportion.isBigOWith_cgExcess_of_state`, at `σ = 1/3`, `s = γ`, `q = 2`. -/
theorem lintegral_rpow_lambdaAnnulusAtom_le_of_state (M : ABKModel d)
    {E : {E : ℝ // 1 ≤ E}} (k : ℤ) (z : Vec d)
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (k - 3) E)
    (hE : max (Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
        (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEup : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hwin : Proportion.cgTailScale M (E : ℝ) ≤ M.gamma / 2)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (Support.lambdaAnnulusAtom M k z omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal
          (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ * Support.cgEllipLowerConstant d +
            gammaMomentBound (1 / 3) p
              (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
                Proportion.cgTailScale M (E : ℝ))) ^ p := by
  have hSpos : (0 : ℝ) < (Annealed.sigmaBar M (k - 3) : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M (k - 3)
  have hSinv : (0 : ℝ) < ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ := inv_pos.mpr hSpos
  have hCcg : (0 : ℝ) < Support.cgEllipLowerConstant d :=
    Support.cgEllipLowerConstant_pos d
  have htail := isBigOWith_inv_sigmaBar_mul_cgExcess M k z
    (Proportion.isBigOWith_cgExcess_of_state M k z hstate hE hEup hwin)
  refine lintegral_rpow_le_of_isBigOWith_add_const_of_ae_le (by norm_num)
    (mul_pos hSinv (Proportion.cgTailScale_pos M (E : ℝ))) hp
    (mul_nonneg hSinv.le hCcg.le)
    (fun omega => mul_nonneg hSinv.le (Localize.cgExcess_nonneg M _ _ z omega))
    (((measurable_cgExcess M (Support.cgEllipLowerConstant d) k z).const_mul
      _).aemeasurable) htail ?_ le_rfl
  refine Filter.Eventually.of_forall fun omega => ENNReal.ofReal_le_ofReal ?_
  exact lambdaAnnulusAtom_le_inv_sigmaBar_mul_add M
    (Support.cgEllipLowerConstant d) k z omega

/-- **(B5) at every moment, packaged through the all-scales budget.**

The induction state and both `E`-window premises of `p.cg.ellipticity.bounds`
are discharged (`Proportion.exists_cgExcess_atomTail`).  The `s`-window `hwin` is the
anchor's own and remains a caller obligation. -/
theorem exists_lintegral_rpow_lambdaAnnulusAtom_le (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            (Proportion.cgTailScale M (E : ℝ) ≤ M.gamma / 2 →
              ∀ (k : ℤ) (z : Vec d) (p : ℝ), 1 ≤ p →
                ∫⁻ omega : Cutoff.CutoffSample d,
                    ENNReal.ofReal (Support.lambdaAnnulusAtom M k z omega) ^ p
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure
                  ≤ ENNReal.ofReal
                      (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
                          Support.cgEllipLowerConstant d +
                        gammaMomentBound (1 / 3) p
                          (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
                            Proportion.cgTailScale M (E : ℝ))) ^ p) := by
  obtain ⟨C, hC6, hall⟩ := Proportion.exists_cgExcess_atomTail d
  refine ⟨C, hC6, fun M hreg => ?_⟩
  obtain ⟨E, hEval, htail⟩ := hall M hreg
  refine ⟨E, hEval, fun hwin k z p hp => ?_⟩
  have hSpos : (0 : ℝ) < (Annealed.sigmaBar M (k - 3) : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M (k - 3)
  have hSinv : (0 : ℝ) < ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ := inv_pos.mpr hSpos
  have hCcg : (0 : ℝ) < Support.cgEllipLowerConstant d :=
    Support.cgEllipLowerConstant_pos d
  have hbig := isBigOWith_inv_sigmaBar_mul_cgExcess M k z (htail hwin k z)
  refine lintegral_rpow_le_of_isBigOWith_add_const_of_ae_le (by norm_num)
    (mul_pos hSinv (Proportion.cgTailScale_pos M (E : ℝ))) hp
    (mul_nonneg hSinv.le hCcg.le)
    (fun omega => mul_nonneg hSinv.le (Localize.cgExcess_nonneg M _ _ z omega))
    (((measurable_cgExcess M (Support.cgEllipLowerConstant d) k z).const_mul
      _).aemeasurable) hbig ?_ le_rfl
  refine Filter.Eventually.of_forall fun omega => ENNReal.ofReal_le_ofReal ?_
  exact lambdaAnnulusAtom_le_inv_sigmaBar_mul_add M
    (Support.cgEllipLowerConstant d) k z omega

/-! ## 4. The gapped gauge `s̃ = 2γ` -/

/-- The dimension of a model is nonzero.  Local re-derivation (distinct name)
of the `private neZero_of_model` of five proved modules. -/
private theorem neZeroOfModel (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The centred `λ`-literal IS `λ_{s,q}^{-1}` of the Chapter 2 carrier on the
origin cube.  Local re-derivation (distinct name) of
`Localize.cutoffLowerEllipticityInvLiteral_eq_inv_lambdaSq`, whose module is
not in this file's import closure; the proof is the same two-step composition
of the proved `BadEvents.cubeLowerEllipticityInvLiteral_originCube` (an `rfl`)
with `Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv`. -/
private theorem literal_eq_inv_lambdaSq [NeZero d] (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (q : CoarseEllipticityExponent)
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q
        omega =
      (Ch02.lambdaSq (originCube d domainScale) s q.1
        (Cutoff.coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹ := by
  rw [← Algsuperdiff.Section3.Provider.BadEvents.cubeLowerEllipticityInvLiteral_originCube
      M domainScale cutoffScale s q,
    Algsuperdiff.Section3.Provider.Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv]

/-- **Transport to the gapped gauge, at constant `1`.**  `λ^{-1}` is antitone in
the gauge exponent, so the `γ`-gauge atom dominates the `2γ`-gauge one
pointwise.  This is A9's "the event side is free" direction; the converse does
NOT hold and is not claimed. -/
theorem lambdaAtom_twoGamma_le_lambdaAnnulusAtom (M : ABKModel d) (k : ℤ)
    (z : Vec d) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2) (2 * M.gamma)
        Support.coarseEllipticityExponentTwo
        (Cutoff.translateCutoffSample z omega) ≤
      Support.lambdaAnnulusAtom M k z omega := by
  haveI : NeZero d := neZeroOfModel M
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  rw [Support.lambdaAnnulusAtom,
    literal_eq_inv_lambdaSq M (k - 2) (k - 2) (2 * M.gamma)
      Support.coarseEllipticityExponentTwo (Cutoff.translateCutoffSample z omega),
    literal_eq_inv_lambdaSq M (k - 2) (k - 2) M.gamma
      Support.coarseEllipticityExponentTwo (Cutoff.translateCutoffSample z omega)]
  exact Localize.inv_lambdaSq_antitone_gauge (originCube d (k - 2)) _ hg
    (by linarith only [hg]) Support.coarseEllipticityExponentTwo.2

/-- **(B5) at the gapped gauge `s̃ = 2γ`.**  The same moment bound, for the
`λ`-slot the Step-3 consumer on this tree actually reads. -/
theorem exists_lintegral_rpow_lambdaAtom_twoGamma_le (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            (Proportion.cgTailScale M (E : ℝ) ≤ M.gamma / 2 →
              ∀ (k : ℤ) (z : Vec d) (p : ℝ), 1 ≤ p →
                ∫⁻ omega : Cutoff.CutoffSample d,
                    ENNReal.ofReal
                      (Observable.cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2)
                        (2 * M.gamma) Support.coarseEllipticityExponentTwo
                        (Cutoff.translateCutoffSample z omega)) ^ p
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure
                  ≤ ENNReal.ofReal
                      (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
                          Support.cgEllipLowerConstant d +
                        gammaMomentBound (1 / 3) p
                          (((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ *
                            Proportion.cgTailScale M (E : ℝ))) ^ p) := by
  obtain ⟨C, hC6, hall⟩ := Proportion.exists_cgExcess_atomTail d
  refine ⟨C, hC6, fun M hreg => ?_⟩
  obtain ⟨E, hEval, htail⟩ := hall M hreg
  refine ⟨E, hEval, fun hwin k z p hp => ?_⟩
  have hSpos : (0 : ℝ) < (Annealed.sigmaBar M (k - 3) : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M (k - 3)
  have hSinv : (0 : ℝ) < ((Annealed.sigmaBar M (k - 3) : ℝ))⁻¹ := inv_pos.mpr hSpos
  have hCcg : (0 : ℝ) < Support.cgEllipLowerConstant d :=
    Support.cgEllipLowerConstant_pos d
  have hbig := isBigOWith_inv_sigmaBar_mul_cgExcess M k z (htail hwin k z)
  refine lintegral_rpow_le_of_isBigOWith_add_const_of_ae_le (by norm_num)
    (mul_pos hSinv (Proportion.cgTailScale_pos M (E : ℝ))) hp
    (mul_nonneg hSinv.le hCcg.le)
    (fun omega => mul_nonneg hSinv.le (Localize.cgExcess_nonneg M _ _ z omega))
    (((measurable_cgExcess M (Support.cgEllipLowerConstant d) k z).const_mul
      _).aemeasurable) hbig ?_ le_rfl
  refine Filter.Eventually.of_forall fun omega => ENNReal.ofReal_le_ofReal ?_
  exact le_trans (lambdaAtom_twoGamma_le_lambdaAnnulusAtom M k z omega)
    (lambdaAnnulusAtom_le_inv_sigmaBar_mul_add M
      (Support.cgEllipLowerConstant d) k z omega)

end

end Algsuperdiff.Section4.Provider.BoundsEaL
