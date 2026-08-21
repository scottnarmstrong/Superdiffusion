/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryOuterCaccioppoli
import Algsuperdiff.Section4.Provider.ExcessDecay.ForcingCorrection

/-!
# The boundary-regime energy estimate at the frozen theorem's own window

```text
  ν ⨍_{(x+□_{k-2})∩□_m} |∇u|²
      ≤ 3^d · [ 2 · P_{s,t} · λ_t 3^{-2k} ‖u(·+c) - v‖²_{L̲²(□_k)}
                + 2 · 18^d · ( C r^{-3/2} Λ⁻ [g̃]_{B^r}
                             + C r^{-1/2} Λ⁺ ‖∇h̃‖_{B^r} )² ] .
```

Everything on the left is the anchor's; everything on the right is
CoarseGraining's, at the covering cube `□_k` in its own frame, at the
translated sample `τ_c ω`, `c = wellPlacedCentre x m k`.  The comparison
solution `v` is *produced*, not assumed: it is the Dirichlet solution on `□_k`
carrying the transported boundary datum `h(·+c)`.

## Why the localized datum is the only possible hypothesis (disclosed)

At `Q = □_m` that is the anchor's own condition, but at `Q = □_m` the
Caccioppoli core is `□_m ∩ (w+□_{m-2})` and the covering ratio to the anchor's
window `x+□_n` is `3^{(m-2-n)d}`, which destroys the estimate.  That is the
content of `BoundaryOuterCaccioppoli`; here it is discharged.

## The `ν |∇u|²` reading

The antisymmetric flux shift leaves the symmetric part of the coefficient
untouched and the cutoff coefficient's symmetric part is `ν Id`
(`AntisymmetricShiftCutoff`), so CoarseGraining's `localizedCoeffEnergyValue`
at the flux-corrected family is literally `ν` times the normalized average of
`|∇u|²`.  The covering transport is therefore an *identity* on the integrand
and an inequality only in the volume ratio.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The covering cube's own coefficient family.**  The cutoff coefficient at the
translated sample `τ_c ω`, `c = wellPlacedCentre x m k`, minus its own
antisymmetric flux increment over `□_k`. -/
def wellPlacedFluxCorrectedFamily (M : ABKModel d) (L : ℤ) (m k : ℤ) (x : Vec d)
    (omega : Cutoff.CutoffSample d) : Ch03.CoeffFamily d :=
  Support.fluxCorrectedCoeffFamily M L k (originCube d k)
    (Cutoff.translateCutoffSample (wellPlacedCentre x m k) omega)

/-! ## 1. The window centre in the covering cube's frame -/

/-- The anchor's window centre, seen from the well-placed centre, lies in `□_k` —
the hypothesis `x ∈ openCubeSet Q` of CoarseGraining's Caccioppoli theorem. -/
theorem sub_wellPlacedCentre_mem_openCubeSet {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    x - wellPlacedCentre x m k ∈ openCubeSet (originCube d k) := by
  have hmem : x ∈ truncatedWindow x m k := mem_truncatedWindow_self k hx
  have h := truncatedWindow_subset_image_add_wellPlacedCentre x hkm (le_refl k) hmem
  rwa [mem_image_add_iff] at h

/-! ## 2. The covering transport of the anchor's window energy -/

/-- **The anchor's window energy, transported onto CoarseGraining's Caccioppoli
core.**

`ν` times the normalized average of `|∇u|²` over the anchor's own window
`(x+□_{k-2}) ∩ □_m` is at most `3^d` times CoarseGraining's
`localizedCoeffEnergyValue` on the core of the covering cube, read at the
covering cube's own flux-corrected family and at the transported solution. -/
theorem nu_mul_normalizedSetAverage_truncatedWindow_le_coreEnergy (M : ABKModel d)
    (L : ℤ) (omega : Cutoff.CutoffSample d) {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m)
    (u : H1Function (openCubeSet (originCube d m))) :
    M.nu * normalizedSetAverage (truncatedWindow x m (k - 2))
        (fun y => vecNormSq (u.grad y)) ≤
      (3 : ℝ) ^ d *
        localizedCoeffEnergyValue
          (caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k))
          ((wellPlacedFluxCorrectedFamily M L m k x omega).coeffOn (originCube d k))
          (H1Function.untranslate (wellPlacedCentre x m k)
            (u.restrict (isOpen_translateSet_openCubeSet (wellPlacedCentre x m k) k)
              (translateSet_wellPlacedCentre_subset x hkm))) := by
  set c : Vec d := wellPlacedCentre x m k with hc
  set core : Set (Vec d) := caccioppoliCoreSet (originCube d k) (x - c) with hcore
  have hcore_sub : ((fun y => c + y) '' core) ⊆ openCubeSet (originCube d m) := by
    intro p hp
    rw [mem_image_add_iff] at hp
    have hp' : p - c ∈ openCubeSet (originCube d k) := hp.1
    have hmem : p ∈ translateSet c (openCubeSet (originCube d k)) :=
      (mem_translateSet_iff_sub_mem).2 hp'
    exact translateSet_wellPlacedCentre_subset x hkm hmem
  have hmono : volumeMeasureOn ((fun y => c + y) '' core) ≤
      volumeMeasureOn (openCubeSet (originCube d m)) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hcore_sub
  have hgrad : MemVectorL2 ((fun y => c + y) '' core) u.grad :=
    u.grad_memVectorL2.mono_measure hmono
  have hsq : MeasureTheory.IntegrableOn (fun y => vecNormSq (u.grad y))
      ((fun y => c + y) '' core) MeasureTheory.volume :=
    integrableOn_vecDot_of_memVectorL2 hgrad hgrad
  have hint : MeasureTheory.IntegrableOn (fun y => M.nu * vecNormSq (u.grad y))
      ((fun y => c + y) '' core) MeasureTheory.volume := hsq.const_mul M.nu
  have hf : ∀ y ∈ (fun y => c + y) '' core, 0 ≤ M.nu * vecNormSq (u.grad y) :=
    fun y _ => mul_nonneg M.nu_pos.le (vecNormSq_nonneg (u.grad y))
  have hcov :=
    normalizedSetAverage_truncatedWindow_le_three_pow_mul_untranslatedCore hx hkm hf hint
  have hlhs : normalizedSetAverage (truncatedWindow x m (k - 2))
      (fun y => M.nu * vecNormSq (u.grad y)) =
      M.nu * normalizedSetAverage (truncatedWindow x m (k - 2))
        (fun y => vecNormSq (u.grad y)) :=
    normalizedSetAverage_const_mul _ M.nu _
  have hrhs : normalizedSetAverage core (fun y => M.nu * vecNormSq (u.grad (y + c))) =
      localizedCoeffEnergyValue core
        ((wellPlacedFluxCorrectedFamily M L m k x omega).coeffOn (originCube d k))
        (H1Function.untranslate c
          (u.restrict (isOpen_translateSet_openCubeSet c k)
            (translateSet_wellPlacedCentre_subset x hkm))) := by
    rw [wellPlacedFluxCorrectedFamily,
      localizedCoeffEnergyValue_fluxCorrected_eq M L (originCube d k) (originCube d k)
        (Cutoff.translateCutoffSample c omega) core]
    rw [← normalizedSetAverage_const_mul]
    rfl
  rw [hlhs, hrhs] at hcov
  exact hcov

/-! ## 3. The composed boundary display at the anchor's window -/

/-- **The boundary-regime energy estimate at the frozen theorem's own window, with
the `∇h` legs present.**

Entered at the frozen theorem's own Dirichlet datum on `□_m` and its own window
centre `x ∈ □_m`, at any covering scale `k ≤ m`; concluded at the anchor's own
window `(x+□_{k-2}) ∩ □_m` and its own frame, with the comparison solution `v`
**produced** on the covering cube carrying the transported boundary datum.

The two legs of `dirichletEnergyWithRHSRHS` are the force leg `[g̃]_{B^r}` at
`r^{-3/2}` and the boundary leg `‖∇h̃‖_{B^r}` at `r^{-1/2}` — the two grad-`h`
sites the frozen theorem's general clause prices, at the exponents this chain
actually produces.  No `s`-power and no `γ`-power is moved anywhere. -/
theorem exists_boundaryWindowEnergy_le_dirichletDatumRHS (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (m k : ℤ)
        (x : Vec d) (s t r : ℝ)
        (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        x ∈ openCubeSet (originCube d m) → k ≤ m →
        Support.IsDirichletSolutionOn
          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m)
          u hdat g →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 → 0 < r → r < 1 →
        ForceBesovRegularity (originCube d k) r
          (fun y => -g (y + wellPlacedCentre x m k)) →
        ForceBesovRegularity (originCube d k) r
          (fun y => hdat.grad (y + wellPlacedCentre x m k)) →
          ∃ v : DirichletForcedCubeSolution (originCube d k)
              (wellPlacedFluxCorrectedFamily M L m k x omega)
              (fun y => -g (y + wellPlacedCentre x m k)),
            (∀ y, v.boundaryData.toFun y = hdat.toFun (y + wellPlacedCentre x m k)) ∧
              M.nu * normalizedSetAverage (truncatedWindow x m (k - 2))
                  (fun y => vecNormSq (u.grad y)) ≤
                (3 : ℝ) ^ d *
                  (2 * (caccioppoliWithRHSPrefactor C₁ (originCube d k)
                        (wellPlacedFluxCorrectedFamily M L m k x omega) s t *
                      (Ch02.lambdaS (originCube d k) t
                          (wellPlacedFluxCorrectedFamily M L m k x omega) *
                        Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
                        normalizedL2SqOnSet (openCubeSet (originCube d k))
                          (fun y => u.toFun (y + wellPlacedCentre x m k) -
                            v.toH1.toFun y))) +
                    2 * ((18 : ℝ) ^ d *
                      dirichletEnergyWithRHSRHS C₂ (originCube d k)
                        (wellPlacedFluxCorrectedFamily M L m k x omega) r
                        (fun y => -g (y + wellPlacedCentre x m k)) v ^ 2)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hmain⟩ :=
    exists_boundaryCaccioppoliEnergy_withLocalizedBoundaryDatum d
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M L omega m k x s t r u hdat g hx hkm hsol hs hs1 ht ht2 hst hr hr1 hgTr hhTr
  set c : Vec d := wellPlacedCentre x m k with hc
  set aFam : Ch03.CoeffFamily d := wellPlacedFluxCorrectedFamily M L m k x omega with haFam
  set hsub : translateSet c (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m) := translateSet_wellPlacedCentre_subset x hkm with hsubdef
  set utr : H1Function (openCubeSet (originCube d k)) :=
    H1Function.untranslate c (u.restrict (isOpen_translateSet_openCubeSet c k) hsub)
    with hutr
  set htr : H1Function (openCubeSet (originCube d k)) :=
    H1Function.untranslate c (hdat.restrict (isOpen_translateSet_openCubeSet c k) hsub)
    with hhtr
  -- the transported equation and the transported force
  have heq : IsForcedEquation (originCube d k) aFam utr (fun y => -g (y + c)) := by
    rw [haFam, wellPlacedFluxCorrectedFamily, hutr]
    exact isForcedEquation_wellPlacedCube_of_isDirichletSolutionOn M L x omega hkm hsol
  have hgL2 : MemVectorL2 (openCubeSet (originCube d k)) (fun y => -g (y + c)) :=
    memVectorL2_openCubeSet_of_forceBesovRegularity hgTr
  -- the comparison solution on the covering cube, carrying the transported datum
  obtain ⟨v, hvdat, sigma, hsigma⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData (originCube d k) aFam htr hgL2
  refine ⟨v, fun y => ?_, ?_⟩
  · rw [hvdat, hhtr]
    rfl
  -- the anchor's own zero-trace witness
  obtain ⟨rho, hrhoval, _hrhograd⟩ := hsol.1
  -- the localized zero trace of the difference on the covering cube
  have hUV : ∀ y, utr.toFun y - v.toH1.toFun y =
      rho.toH1Function.toFun (y + c) - sigma.toH1Function.toFun y := by
    intro y
    have hu : utr.toFun y = u.toFun (y + c) := rfl
    have hh : htr.toFun y = hdat.toFun (y + c) := rfl
    rw [hu, hrhoval (y + c), hsigma y, hh]
    ring
  have hloc := localizedZeroTraceFunctionOn_wellPlacedDifference x hkm rho sigma hUV
  have hscale : (originCube d k).scale - 1 = k - 1 := by
    rw [scale_originCube]
  have hloc' : Ch01.LocalizedZeroTraceFunctionOn
      (Ch02.cubeDomain (originCube d k) : Set (Vec d))
      (openCubeAtScale (x - c) ((originCube d k).scale - 1))
      (fun y => utr.toFun y - v.toH1.toFun y) := by
    rw [hscale]
    exact hloc
  -- the boundary datum's Besov regularity, at the produced solution
  have hhv : ForceBesovRegularity (originCube d k) r (dirichletBoundaryGradientField v) := by
    rw [dirichletBoundaryGradientField, hvdat]
    exact hhTr
  have hxk : x - c ∈ openCubeSet (originCube d k) :=
    sub_wellPlacedCentre_mem_openCubeSet hx hkm
  have hcacc := hmain (Q := originCube d k) (a := aFam) (s := s) (t := t) (r := r)
    (x := x - c) (g := fun y => -g (y + c)) utr v heq hloc' hs hs1 ht ht2 hst hr hr1
    hgTr hhv hxk
  rw [scale_originCube] at hcacc
  -- the covering transport of the anchor's window energy
  have hcov := nu_mul_normalizedSetAverage_truncatedWindow_le_coreEnergy M L omega hx hkm u
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  refine hcov.trans (mul_le_mul_of_nonneg_left ?_ h3d)
  exact hcacc

end

end Algsuperdiff.Section4.Provider.ExcessDecay
