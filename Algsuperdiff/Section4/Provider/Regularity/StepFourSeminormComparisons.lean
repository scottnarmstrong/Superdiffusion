/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.HolderGagliardoRangeGuard
import Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

/-!
# `t.regularity` Step 4: the two seminorm comparisons

## The target

```text
  [g]_{H̲^{1/4}(U_j)}          ≤  C · 3^{j/4} · [g]_{W̲^{1/2,∞}(□_m)}          (A1)
  [∇h]_{W̲^{1/2,∞}(U_j)}       ≤              [∇h]_{W̲^{1/2,∞}(□_m)}          (A2)
```

on the Step-3 window family `U_j = (z + □_j) ∩ □_m`.

## What is delivered

**(A1)** `normalizedGagliardoESeminormOn_stepThreeWindow_le`, at a general index `0 < s <
1/2` with the honest closed-form constant and the honest scale weight,

```text
  [g]_{H̲^s(U_j)} ≤ K · C_{S4.4}(d,s) · 3^{j(1/2-s)} ,
  C_{S4.4}(d,s) = ( 2^d 3^{d+2s-1} / (1 - 3^{-(1-2s)}) )^{1/2}
                ≤ 2^{(d+1)/2} 3^{d/2} (1-2s)^{-1/2} ,
```

Specialized at the §4.4/§4.5 pin `s = 1/4` the exponents are the numerals `3^{j(1/2-1/4)}
= 3^{j/4}` and `(1-2s)^{-1/2} = 2^{1/2}`, giving exactly the printed `C·3^{j/4}` with `C ≤
(2^{d+2} 3^d)^{1/2}` (`normalizedGagliardoESeminormOn_stepThreeWindow_quarter_le` plus
`stepFourGagliardoConst_quarter_le`).

```text
  3^{sm} [g]_{H̲^s(□_m)} ≤ K · C_{S4.4}(d,s) · 3^{m/2}
```

(`three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`).  This is the missing line
between the Step-7d display's `3^{sm}[g]_{H̲^s(□_m)}` and `e.energy.density.estimate`'s
`3^{m/2}[g]_{W̲^{1/2,∞}(□_m)}`; note the free `s` cancels out of the scale weight, which
is why the theorem's conclusion can be `s`-free.

**(A2)** `holderSeminormBoundOn_stepThreeWindow`, at constant `1` exactly as
printed, from `U_j ⊆ □_m` alone.  The printed constant `1` is only correct if the
`p = ∞` seminorm carries no volume normalization; that is verified here from two
sides:

* the *volume-normalized* reading is also free:
  `normalizedGagliardoTopESeminormOn_mono_set` shows the `⨍∫`-normalized Gagliardo
  seminorm at `p = ∞` is monotone under window restriction at constant `1`, because an
  essential supremum does not see a positive scalar multiple of the measure.  So no
  `|U_j|/|□_m|` ratio enters (A2) in either reading — unlike the `p = 2` seminorm of (A1),
  where the ratio would enter and is instead avoided by the uniform-in-first-slot argument
  of `HolderGagliardoEmbedding`.

## The range guard

At the §4.4 pin `s = 1/4` the guard is met with room.

## References

* ABK26, `t.regularity` Step 4; Step 7d.
* ABK26, (the seminorm conventions).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory Metric
open Homogenization
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The window has `sup`-diameter at most `3^j` -/

/-- Every point of `U_j = (z + □_j) ∩ □_m` sees the whole window inside the
`sup`-ball of radius `3^j`: the window sits in a cube of side `3^j`. -/
theorem truncatedWindow_subset_ball {z : Vec d} {m j : ℤ} {x : Vec d}
    (hx : x ∈ truncatedWindow z m j) :
    truncatedWindow z m j ⊆ Metric.ball x ((3 : ℝ) ^ j) := by
  intro y hy
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hxc := mem_openCubeSet_originCube_iff.mp (sub_mem_openCubeSet_of_mem_truncatedWindow hx)
  have hyc := mem_openCubeSet_originCube_iff.mp (sub_mem_openCubeSet_of_mem_truncatedWindow hy)
  simp only [Pi.sub_apply] at hxc hyc
  rw [Metric.mem_ball, dist_pi_lt_iff h3]
  intro i
  have hxi := hxc i
  have hyi := hyc i
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith only [hxi.2, hyi.1]
  · linarith only [hxi.1, hyi.2]

/-! ## 2. The scale weight `3^{j(1/2-s)}` -/

private theorem three_zpow_pow_mul_rpow_neg_beta {j : ℤ} {s : ℝ} :
    ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ j) ^ (-holderGagliardoBeta d s) =
      (3 : ℝ) ^ ((j : ℝ) * (1 - 2 * s)) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have h1 : ((3 : ℝ) ^ j) ^ d = ((3 : ℝ) ^ j) ^ ((d : ℕ) : ℝ) := (Real.rpow_natCast _ d).symm
  have h2 : ((d : ℕ) : ℝ) + -holderGagliardoBeta d s = 1 - 2 * s := by
    rw [holderGagliardoBeta]; ring
  have h3 : ((3 : ℝ) ^ j) = (3 : ℝ) ^ ((j : ℤ) : ℝ) := (Real.rpow_intCast 3 j).symm
  rw [h1, ← Real.rpow_add hR, h2, h3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

private theorem sqrt_three_rpow (u : ℝ) : Real.sqrt ((3 : ℝ) ^ u) = (3 : ℝ) ^ (u / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-! ## 3. Atom (A1): the `g`-restriction comparison -/

/-- `[g]_{H̲^s(U_j)} ≤ K · C_{S4.4}(d,s) · 3^{j(1/2-s)}`,

where `K` is any `C^{0,1/2}(□_m)` bound for `g` — the development's carrier of
the printed `[g]_{W̲^{1/2,∞}(□_m)}` slot.  The scale weight is exactly the
window's diameter `3^j` to the power `1/2 - s`; no volume ratio appears. -/
theorem normalizedGagliardoESeminormOn_stepThreeWindow_le {z : Vec d} {m j : ℤ}
    {g : Vec d → E} {K s : ℝ} (hd : 1 ≤ d) (hz : z ∈ openCubeSet (originCube d m))
    (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    Support.normalizedGagliardoESeminormOn (stepThreeWindow z m j) s g ≤
      ENNReal.ofReal (K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((j : ℝ) * (1 / 2 - s))) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hwin : stepThreeWindow z m j = truncatedWindow z m j := rfl
  have hmeas : MeasurableSet (stepThreeWindow z m j) := measurableSet_stepThreeWindow z m j
  have hvol0 : volume (stepThreeWindow z m j) ≠ 0 := by
    rw [hwin]
    exact (volume_truncatedWindow_pos j hz).ne'
  have hvoltop : volume (stepThreeWindow z m j) ≠ ⊤ := by
    rw [hwin]
    exact (volume_truncatedWindow_lt_top z m j).ne
  have hballs : ∀ x ∈ stepThreeWindow z m j,
      stepThreeWindow z m j ⊆ Metric.ball x ((3 : ℝ) ^ j) := by
    intro x hx
    rw [hwin] at hx ⊢
    exact truncatedWindow_subset_ball hx
  have hgw : Support.HolderSeminormBoundOn (stepThreeWindow z m j) (1 / 2) K g := by
    rw [hwin]
    exact hg.mono_set (truncatedWindow_subset_domain z m j)
  have hmain := normalizedGagliardoESeminormOn_le_of_holderHalf (E := E)
    (A := stepThreeWindow z m j) (g := g) (K := K) (R := (3 : ℝ) ^ j) (s := s)
    hd hmeas hvol0 hvoltop hballs hR hs0 hs hK hgw
  refine hmain.trans (le_of_eq ?_)
  have hexp : (j : ℝ) * (1 - 2 * s) / 2 = (j : ℝ) * (1 / 2 - s) := by ring
  have hval : Real.sqrt (radialKernelConst d (holderGagliardoBeta d s) *
      (((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ j) ^ (-holderGagliardoBeta d s))) =
      stepFourGagliardoConst d s * (3 : ℝ) ^ ((j : ℝ) * (1 / 2 - s)) := by
    rw [three_zpow_pow_mul_rpow_neg_beta,
      Real.sqrt_mul (radialKernelConst_pos (holderGagliardoBeta_lt hs)).le,
      sqrt_three_rpow, hexp, stepFourGagliardoConst]
  rw [hval, ← mul_assoc]

/-- **The `s = 1/4` pin**: the printed `C·3^{j/4}`, with the constant
`C_{S4.4}(d,1/4) ≤ (2^{d+2} 3^d)^{1/2}` supplied by
`stepFourGagliardoConst_quarter_le`. -/
theorem normalizedGagliardoESeminormOn_stepThreeWindow_quarter_le {z : Vec d} {m j : ℤ}
    {g : Vec d → E} {K : ℝ} (hd : 1 ≤ d) (hz : z ∈ openCubeSet (originCube d m)) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    Support.normalizedGagliardoESeminormOn (stepThreeWindow z m j) (1 / 4) g ≤
      ENNReal.ofReal (K * stepFourGagliardoConst d (1 / 4) * (3 : ℝ) ^ ((j : ℝ) / 4)) := by
  have h := normalizedGagliardoESeminormOn_stepThreeWindow_le (z := z) (m := m) (j := j)
    (g := g) (K := K) (s := 1 / 4) hd hz (by norm_num) (by norm_num) hK hg
  refine h.trans (le_of_eq ?_)
  rw [show (j : ℝ) * (1 / 2 - 1 / 4) = (j : ℝ) / 4 by ring]

/-! ## 3b. The same atom on the full cube: the Step-7d passage -/

theorem zero_mem_openCubeSet_originCube (d : ℕ) (m : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d m) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> linarith only [h3]

theorem openCubeSet_subset_ball {m : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    openCubeSet (originCube d m) ⊆ Metric.ball x ((3 : ℝ) ^ m) := by
  intro y hy
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hxc := mem_openCubeSet_originCube_iff.mp hx
  have hyc := mem_openCubeSet_originCube_iff.mp hy
  rw [Metric.mem_ball, dist_pi_lt_iff h3]
  intro i
  have hxi := hxc i
  have hyi := hyc i
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith only [hxi.2, hyi.1]
  · linarith only [hxi.1, hyi.2]

/-- **The `g`-comparison on the full cube**: `[g]_{H̲^s(□_m)} ≤ K C(d,s)
3^{m(1/2-s)}`. -/
theorem normalizedGagliardoESeminormOn_cube_le {m : ℤ} {g : Vec d → E} {K s : ℝ}
    (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    Support.normalizedGagliardoESeminormOn (openCubeSet (originCube d m)) s g ≤
      ENNReal.ofReal (K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) * (1 / 2 - s))) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpen_openCubeSet _).measurableSet
  have hvol0 : volume (openCubeSet (originCube d m)) ≠ 0 :=
    ((isOpen_openCubeSet _).measure_pos volume ⟨0, zero_mem_openCubeSet_originCube d m⟩).ne'
  have hvoltop : volume (openCubeSet (originCube d m)) ≠ ⊤ := by
    rw [volume_openCubeSet_eq_volume_cubeSet]
    exact (volume_cubeSet_lt_top _).ne
  have hmain := normalizedGagliardoESeminormOn_le_of_holderHalf (E := E)
    (A := openCubeSet (originCube d m)) (g := g) (K := K) (R := (3 : ℝ) ^ m) (s := s)
    hd hmeas hvol0 hvoltop (fun x hx => openCubeSet_subset_ball hx) hR hs0 hs hK hg
  refine hmain.trans (le_of_eq ?_)
  have hexp : (m : ℝ) * (1 - 2 * s) / 2 = (m : ℝ) * (1 / 2 - s) := by ring
  have hval : Real.sqrt (radialKernelConst d (holderGagliardoBeta d s) *
      (((3 : ℝ) ^ m) ^ d * ((3 : ℝ) ^ m) ^ (-holderGagliardoBeta d s))) =
      stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) * (1 / 2 - s)) := by
    rw [three_zpow_pow_mul_rpow_neg_beta,
      Real.sqrt_mul (radialKernelConst_pos (holderGagliardoBeta_lt hs)).le,
      sqrt_three_rpow, hexp, stepFourGagliardoConst]
  rw [hval, ← mul_assoc]

theorem three_rpow_mul_normalizedGagliardoESeminormOn_cube_le {m : ℤ} {g : Vec d → E}
    {K s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    ENNReal.ofReal ((3 : ℝ) ^ ((m : ℝ) * s)) *
        Support.normalizedGagliardoESeminormOn (openCubeSet (originCube d m)) s g ≤
      ENNReal.ofReal (K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
  have h := normalizedGagliardoESeminormOn_cube_le hd hs0 hs hK hg
  have hcomb : (3 : ℝ) ^ ((m : ℝ) * s) * (3 : ℝ) ^ ((m : ℝ) * (1 / 2 - s)) =
      (3 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  refine (mul_le_mul' le_rfl h).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
  congr 1
  calc (3 : ℝ) ^ ((m : ℝ) * s) *
        (K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) * (1 / 2 - s)))
      = K * stepFourGagliardoConst d s *
          ((3 : ℝ) ^ ((m : ℝ) * s) * (3 : ℝ) ^ ((m : ℝ) * (1 / 2 - s))) := by ring
    _ = K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2) := by rw [hcomb]

/-! ## 4. Atom (A2): the Hölder restriction, at constant `1` -/

omit [NormedSpace ℝ E] in
theorem holderSeminormBoundOn_stepThreeWindow {z : Vec d} {m j : ℤ} {alpha K : ℝ}
    {f : Vec d → E}
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) alpha K f) :
    Support.HolderSeminormBoundOn (stepThreeWindow z m j) alpha K f :=
  hf.mono_set (truncatedWindow_subset_domain z m j)

/-! ## 5. The volume-normalized reading of (A2) is also at constant `1` -/

private theorem normGagMeasureOn_eq_smul_restrict (A : Set (Vec d)) :
    Support.normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
  rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
    Measure.prod_smul_left, Measure.prod_restrict]

/-- **`[f]_{W̲^{s,∞}(A)}`**, the manuscript's volume-normalized fractional seminorm
at `p = ∞` on an arbitrary set: the essential supremum of the difference
quotient `|f(x)-f(y)| / |x-y|^s` against the `⨍∫`-normalized product measure
(CoarseGraining's `kernelExponent` collapses to `s` at `p = ∞`). -/
def normalizedGagliardoTopESeminormOn (A : Set (Vec d)) (s : ℝ) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm (Gagliardo.gagliardoKernel s ∞ f) ∞ (Support.normalizedGagliardoMeasureOn A)

theorem normalizedGagliardoTopESeminormOn_def (A : Set (Vec d)) (s : ℝ) (f : Vec d → E) :
    normalizedGagliardoTopESeminormOn A s f =
      eLpNorm (Gagliardo.gagliardoKernel s ∞ f) ∞ (Support.normalizedGagliardoMeasureOn A) :=
  rfl

/-- **The volume normalization is inert at `p = ∞`.**

For `B ⊆ A` of positive finite volume, `[f]_{W̲^{s,∞}(B)} ≤ [f]_{W̲^{s,∞}(A)}`
with constant `1` — no `|A|/|B|` ratio.  The reason is that the restriction `B
⊆ A` costs only a positive scalar multiple of the measure, and an essential
supremum is invariant under such a multiple.  This is why the printed display
`[∇h]_{W̲^{1/2,∞}(U_j)} ≤ [∇h]_{W̲^{1/2,∞}(□_m)}` legitimately carries no
constant, whereas the `p = 2` display of atom (A1) does. -/
theorem normalizedGagliardoTopESeminormOn_mono_set {A B : Set (Vec d)} (hBA : B ⊆ A)
    (hBtop : volume B ≠ ⊤) (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ⊤) (s : ℝ)
    (f : Vec d → E) :
    normalizedGagliardoTopESeminormOn B s f ≤ normalizedGagliardoTopESeminormOn A s f := by
  have hc0 : (volume B)⁻¹ * volume A ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr hBtop) hA0
  have hcancel : (volume B)⁻¹ * volume A * (volume A)⁻¹ = (volume B)⁻¹ := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, mul_one]
  have hmeasle : Support.normalizedGagliardoMeasureOn B ≤
      ((volume B)⁻¹ * volume A) • Support.normalizedGagliardoMeasureOn A := by
    rw [normGagMeasureOn_eq_smul_restrict A, normGagMeasureOn_eq_smul_restrict B, smul_smul,
      hcancel]
    refine Measure.le_iff'.mpr fun S => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_mono (Set.prod_mono hBA hBA) le_rfl S)
  calc normalizedGagliardoTopESeminormOn B s f
      ≤ eLpNorm (Gagliardo.gagliardoKernel s ∞ f) ∞
          (((volume B)⁻¹ * volume A) • Support.normalizedGagliardoMeasureOn A) :=
        eLpNorm_mono_measure _ hmeasle
    _ = normalizedGagliardoTopESeminormOn A s f := by
        rw [normalizedGagliardoTopESeminormOn_def, eLpNorm_smul_measure_of_ne_zero hc0]
        simp

/-- **Atom (A2), volume-normalized reading, at the Step-3 windows.** -/
theorem normalizedGagliardoTopESeminormOn_stepThreeWindow_le {z : Vec d} {m j : ℤ}
    (hz : z ∈ openCubeSet (originCube d m)) (s : ℝ) (f : Vec d → E) :
    normalizedGagliardoTopESeminormOn (stepThreeWindow z m j) s f ≤
      normalizedGagliardoTopESeminormOn (openCubeSet (originCube d m)) s f := by
  have hwin : stepThreeWindow z m j = truncatedWindow z m j := rfl
  have hA0 : volume (openCubeSet (originCube d m)) ≠ 0 := by
    have hcube : (0 : ℝ≥0∞) < volume (openCubeSet (originCube d m)) :=
      (isOpen_openCubeSet _).measure_pos volume ⟨z, hz⟩
    exact hcube.ne'
  have hAtop : volume (openCubeSet (originCube d m)) ≠ ⊤ := by
    rw [volume_openCubeSet_eq_volume_cubeSet]
    exact (volume_cubeSet_lt_top _).ne
  have hBtop : volume (stepThreeWindow z m j) ≠ ⊤ := by
    rw [hwin]
    exact (volume_truncatedWindow_lt_top z m j).ne
  rw [hwin] at hBtop ⊢
  exact normalizedGagliardoTopESeminormOn_mono_set (truncatedWindow_subset_domain z m j)
    hBtop hA0 hAtop s f

end

end Algsuperdiff.Section4.Provider.Regularity
