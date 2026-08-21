/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBArith
import Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalChain
import Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons
import Algsuperdiff.Section4.Provider.Regularity.StepSevenSigmaBar

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The interior window's exact volume -/

/-- On the interior branch the top window `(z+□_{m-1}) ∩ □_m` IS the translate `z +
□_{m-1}`, so its volume is exactly `3^{d(m-1)}`. -/
theorem volume_toReal_truncatedWindow_inner (d : ℕ) {m : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) :
    (volume (truncatedWindow z m (m - 1))).toReal = ((3 : ℝ) ^ (m - 1)) ^ d := by
  rw [truncatedWindow_eq_translateSet_of_mem_inner hz (le_refl (m - 1)),
    ← image_add_eq_translateSet, volume_image_add,
    volume_toReal_openCubeSet_originCube]

/-- The volume ratio of the top interior window inside `□_m` is exactly `3^d`. -/
theorem volumeRatio_inner_eq (d : ℕ) (m : ℤ) :
    ((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ (m - 1)) ^ d = (3 : ℝ) ^ d := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [← div_pow, ← zpow_sub₀ h3, show m - (m - 1) = (1 : ℤ) by ring, zpow_one]

/-! ## 2. The window-to-cube step of `hgradE` -/

/-- **The top interior window against the full cube**, at the exact volume ratio:

```text
  ν^{1/2}‖∇u‖_{L̲²((z+□_{m-1}) ∩ □_m)}  ≤  3^{d/2} · ν^{1/2}‖∇u‖_{L̲²(□_m)} .
```

Not an estimate on `u`: the mass comparison is integral monotonicity on nested
sets ('s `stepSevenGradMass_mono`) and the ratio is the exact volume
computation of §1. -/
theorem stepSevenNuGradNorm_inner_le_cube (d : ℕ) {m : ℤ} {z : Vec d} {nu : ℝ}
    (hnu : 0 ≤ nu) (hz : z ∈ openCubeSet (originCube d (m - 1)))
    (u : H1Function (openCubeSet (originCube d m))) :
    stepSevenNuGradNorm nu (truncatedWindow z m (m - 1)) u.grad ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        stepSevenNuGradNorm nu (openCubeSet (originCube d m)) u.grad := by
  have hzm : z ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega) hz
  have hmono := stepSevenGradMass_mono hnu u (truncatedWindow_subset_domain z m (m - 1))
    (Set.Subset.refl (openCubeSet (originCube d m)))
  have hvolS : (0 : ℝ) < (volume (truncatedWindow z m (m - 1))).toReal := by
    rw [volume_toReal_truncatedWindow_inner d hz]
    exact pow_pos (zpow_pos (by norm_num) _) d
  have hvolT : (0 : ℝ) < (volume (openCubeSet (originCube d m))).toReal := by
    rw [volume_toReal_openCubeSet_originCube]
    exact pow_pos (zpow_pos (by norm_num) _) d
  have hratio : Real.sqrt ((volume (openCubeSet (originCube d m))).toReal /
      (volume (truncatedWindow z m (m - 1))).toReal) = Real.sqrt ((3 : ℝ) ^ d) := by
    rw [volume_toReal_truncatedWindow_inner d hz, volume_toReal_openCubeSet_originCube,
      volumeRatio_inner_eq d m]
  have hmain := normalizedSqrt_le_volumeRatio_mul hvolS hvolT hmono
  rw [hratio] at hmain
  rw [stepSevenNuGradNorm_eq_sqrt_div, stepSevenNuGradNorm_eq_sqrt_div]
  exact hmain

/-! ## 3.  at the full cube: the `hgradE` identity -/

/-- proved the `ν`-identification at the Caccioppoli core `□_{j-2}`
(`sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm`); the chain's `hgradE`
slot needs it at `openCubeSet □_j`, which is the same three-line identity — the
symmetric part of the flux-corrected family IS `ν I`, the frame moves by the
translation transport, and the window IS the translate on the interior branch. -/
theorem forcedSolutionEnergyNorm_fluxCorrected_eq_nuGradNorm (M : ABKModel d)
    (L mf m j : ℤ) (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
    {g : Vec d → Vec d}
    (u : ForcedCubeSolution (originCube d j)
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)) g)
    (G : Vec d → Vec d) (hg : ∀ y, u.toH1.grad y = G (y + z))
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    forcedSolutionEnergyNorm (originCube d j)
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) u =
      stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m j) G := by
  rw [forcedSolutionEnergyNorm, h1EnergyNormOnCube, stepSevenNuGradNorm]
  congr 1
  rw [localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq]
  have hfun : (fun x => vecNormSq (u.toH1.grad x)) = fun x => vecNormSq (G (x + z)) := by
    funext x
    rw [hg x]
  have h1 := normalizedSetAverage_vecNormSq_translateSet z
    (openCubeSet (originCube d j)) G
  rw [truncatedWindow_eq_translateSet_of_mem_inner hz hj, hfun]
  exact congrArg (fun t : ℝ => (M.nu : ℝ) * t) h1.symm

/-! ## 4. The five `IntegrableOn` binders -/

/-- The root's `H¹(□_m)` datum is integrable on every finite-volume subset. -/
theorem integrableOn_toFun_subset {m : ℤ} (u : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (hAtop : volume A ≠ ⊤) :
    IntegrableOn u.toFun A volume :=
  integrableOn_of_memLp_two hAtop (memLp_toFun_of_subset u hA)

/-- Its square is integrable there too. -/
theorem integrableOn_sq_toFun_subset {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (hAtop : volume A ≠ ⊤) :
    IntegrableOn (fun x => u.toFun x ^ 2) A volume := by
  have h := integrableOn_sub_const_sq hAtop (memLp_toFun_of_subset u hA) 0
  simpa only [sub_zero] using h

/-- And so is its mean-subtracted square. -/
theorem integrableOn_sub_sq_toFun_subset {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (hAtop : volume A ≠ ⊤)
    (b : ℝ) :
    IntegrableOn (fun x => (u.toFun x - b) ^ 2) A volume :=
  integrableOn_sub_const_sq hAtop (memLp_toFun_of_subset u hA) b

/-! ## 5. The Hölder datum in the translated frame -/

/-- **The Hölder bound transports to the good-scale cube.**  For `z ∈ □_{m-1}` and
`j ≤ m-1` the translate `z + □_j` sits inside `□_m`, so the root's own
`C^{0,1/2}(□_m)` bound on `𝐠` is a `C^{0,1/2}(□_j)` bound on the transported,
negated force `x ↦ -𝐠(x+z)` at the SAME constant (translation is an isometry
and negation preserves differences). -/
theorem holderSeminormBoundOn_translated_neg {m j : ℤ} {z : Vec d}
    {g : Vec d → Vec d} {K : ℝ} (hz : z ∈ openCubeSet (originCube d (m - 1)))
    (hj : j ≤ m - 1)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    Support.HolderSeminormBoundOn (openCubeSet (originCube d j)) (1 / 2) K
      (fun x => -g (x + z)) := by
  have hsub : (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m) := image_add_subset_openCubeSet_of_mem_inner hz hj
  intro x hx y hy
  have hxm : z + x ∈ openCubeSet (originCube d m) := hsub ⟨x, hx, rfl⟩
  have hym : z + y ∈ openCubeSet (originCube d m) := hsub ⟨y, hy, rfl⟩
  have hcx : x + z = z + x := by rw [add_comm]
  have hcy : y + z = z + y := by rw [add_comm]
  have hbase := hg (z + x) hxm (z + y) hym
  have hdiff : -g (x + z) - -g (y + z) = -(g (z + x) - g (z + y)) := by
    rw [hcx, hcy]
    ring
  have hshift : (z + x) - (z + y) = x - y := by ring
  rw [hdiff, norm_neg]
  rw [hshift] at hbase
  exact hbase

end

end Algsuperdiff.Section4.Provider.Regularity
