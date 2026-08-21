/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# Theorem B, §4.5, Step 2: the data embedding `C^{0,1/2} ↪ H̲^s(□_m)`

## The target

Step 2 of Theorem B prices the Step-2 solution by its data.  The datum enters
Theorem C through the Besov leg `3^{sm} [g]_{H̲^s(□_m)}`, while the §4.5
normalization supplies only the HÖLDER bound

```
  [g]_{C^{0,1/2}(□_m)} ≤ 1        and       ‖∇h‖_{C^{0,1/2}(□_m)} ≤ 1.
```

The missing conversion — the obstruction (4) — is

```
  [g]_{C^{0,1/2}(□_m)} ≤ K   ⟹   3^{sm} [g]_{H̲^s(□_m)} ≤ C(d,s) K 3^{m/2}
```

for `0 < s < 1/2`, together with the identical statement for `∇h`.  This module
gives it.

## Most of the engine is already available

The conversion is not new analysis.  Both the Gagliardo engine and its `□_m`
instance are already in this repository:

* `Provider.Regularity.normalizedGagliardoESeminormOn_le_of_holderHalf`
  (`HolderGagliardoEmbedding.lean`) — the window-free atom
  `[g]_{H̲^s(A)} ≤ K (C_rad(d,β) · R^d · R^{-β})^{1/2}`, `β = d + 2s - 1`, for
  any window `A` of sup-diameter `≤ R`, at the very carriers this repository uses;
* `Provider.Regularity.radialKernelConst_holderGagliardoBeta_le` /
  `stepFourGagliardoConst_le` (`HolderGagliardoRangeGuard.lean`) — the constant
  `C_rad(d, d+2s-1) ≤ 2^{d+1} 3^d (1-2s)^{-1}`, i.e. the correction's
  `(1-2s)^{-1/2}`;
* `Provider.Regularity.three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`
  (`StepFourSeminormComparisons.lean`) — **the target display itself**, at the
  window `openCubeSet (originCube d m)`:
  `3^{ms}[g]_{H̲^s(□_m)} ≤ K · C_{S4.4}(d,s) · 3^{m/2}`, generic in `E`, so the
  `g` leg and the `∇h` leg are ONE declaration.

Nothing here re-derives any of that.  The honest residue, and the whole content
of this module, is:

1. `homDataConst` + `stepFourGagliardoConst_le_homDataConst` — the range
   guard pins the constant only at `s = 1/4` EXACTLY
   (`stepFourGagliardoConst_quarter_le`).  §4.5 runs at `s = |log γ|⁻¹`, which
   is `≤ 1/4` but never equal to it, so the pinned form is unusable as stated.
   The `γ`-free constant on the RANGE `0 < s ≤ 1/4` is supplied here.
2. `three_rpow_mul_normalizedGagliardo_originCube_le_pinned` — the §4.5-usable
   display: the `□_m` display at the gated constant.
3. `cubeSet_subset_ball_of_mem` and the general-cube instance
   `three_rpow_mul_normalizedGagliardo_cubeSet_le` — the instance is at the
   ORIGIN cube in its OPEN realization; Step 2b's windows are `z + □_j` for
   `z ∈ 3^j ℤ^d ∩ □_m`, i.e. arbitrary triadic cubes, and the Support layer's
   correspondence anchor `normalizedGagliardoESeminormOn_cubeSet` is stated at
   the HALF-OPEN realization.  Both changes are supplied here, and the half-open
   realization is what makes the ball radius exactly the side length `3^m` (each
   coordinate inequality is strict), with no dimensional loss.

## The constant

`stepFourGagliardoConst d s = C_rad(d, d+2s-1)^{1/2}` carries `(1-2s)^{-1/2}`
and therefore is NOT a constant as `s → 1/2`.  The §4.5 instance is protected by
's gate `s = |log γ|⁻¹ ≤ 1/4` (carried by `HomStepEnvelope`'s
`homS_le_quarter`), at which `1 - 2s ≥ 1/2` and the constant collapses to the
genuinely `γ`-free `homDataConst d = (2^{d+2} 3^d)^{1/2}`.  Both forms are
stated: the `s`-explicit one (no absorption) and the pinned `C(d)` one.
-/

open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Provider.Regularity

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The cube as a sup-ball about each of its points -/

theorem cubeScaleFactor_pos (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  rw [cubeScaleFactor]
  exact zpow_pos (by norm_num) _

/-- **A triadic cube of scale `m` sits in the open sup-ball of radius `3^m`
about any of its own points.**

The half-open realization `cubeSet` gives `|x i - y i| < 3^m` STRICTLY in every
coordinate, and the ambient metric on `Vec d = Fin d → ℝ` is the supremum
metric, so the radius is the side length itself. -/
theorem cubeSet_subset_ball_of_mem {Q : TriadicCube d} {x : Vec d}
    (hx : x ∈ cubeSet Q) : cubeSet Q ⊆ Metric.ball x (cubeScaleFactor Q) := by
  intro y hy
  have hpos : 0 < cubeScaleFactor Q := cubeScaleFactor_pos Q
  rw [Metric.mem_ball]
  refine (dist_pi_lt_iff hpos).2 fun i => ?_
  have hxi := hx i
  have hyi := hy i
  have hid : (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) -
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) = cubeScaleFactor Q := by
    ring
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith only [hxi.1, hxi.2, hyi.1, hyi.2, hid]
  · linarith only [hxi.1, hxi.2, hyi.1, hyi.2, hid]

/-! ## 2. The scale-weight computation -/

private theorem cubeScaleFactor_rpow (Q : TriadicCube d) (t : ℝ) :
    cubeScaleFactor Q ^ t = (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) * t) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [cubeScaleFactor, ← Real.rpow_intCast (3 : ℝ) Q.scale, ← Real.rpow_mul h3]

/-- `R^d · R^{-β} = R^{1-2s}` at `β = d + 2s - 1`, in the `3`-gauge: the whole
geometric content of the cube instance of the embedding atom. -/
private theorem sqrt_scaleWeight_eq {Q : TriadicCube d} {s : ℝ} (hs : s < 1 / 2) :
    Real.sqrt (radialKernelConst d (holderGagliardoBeta d s) *
        (cubeScaleFactor Q ^ d * cubeScaleFactor Q ^ (-holderGagliardoBeta d s))) =
      stepFourGagliardoConst d s * (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ)) := by
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hC : (0 : ℝ) ≤ radialKernelConst d (holderGagliardoBeta d s) :=
    (radialKernelConst_pos (holderGagliardoBeta_lt hs)).le
  have hnat : cubeScaleFactor Q ^ d = cubeScaleFactor Q ^ ((d : ℕ) : ℝ) :=
    (Real.rpow_natCast _ d).symm
  have hcomb : cubeScaleFactor Q ^ d * cubeScaleFactor Q ^ (-holderGagliardoBeta d s) =
      cubeScaleFactor Q ^ (1 - 2 * s) := by
    rw [hnat, ← Real.rpow_add hR]
    congr 1
    rw [holderGagliardoBeta]
    ring
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsplit : cubeScaleFactor Q ^ (1 - 2 * s) =
      ((3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ))) ^ (2 : ℕ) := by
    rw [cubeScaleFactor_rpow, ← Real.rpow_natCast
      ((3 : ℝ) ^ ((1 / 2 - s) * (((Q.scale : ℤ) : ℝ)))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [hcomb, hsplit, Real.sqrt_mul hC, Real.sqrt_sq hbase, stepFourGagliardoConst]

/-! ## 3. The embedding at the cube window -/

/-- **`C^{0,1/2}(□_m) ↪ H̲^s(□_m)` with the sharp scale weight.**

If `[g]_{C^{0,1/2}(□_m)} ≤ K` and `0 < s < 1/2`, then

```
  [g]_{H̲^s(□_m)} ≤ K · C_{S4.4}(d,s) · 3^{(1/2 - s) m},
```

`C_{S4.4}(d,s) = C_rad(d, d+2s-1)^{1/2}` the constant, which carries the
correction's `(1-2s)^{-1/2}`.  Generic in the target `E`, so the vector datum
`g` and the vector field `∇h` are the same instance. -/
theorem normalizedGagliardo_cubeSet_le_of_holderHalf {Q : TriadicCube d} {g : Vec d → E}
    {K s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (cubeSet Q) (1 / 2) K g) :
    Support.normalizedGagliardoESeminormOn (cubeSet Q) s g ≤
      ENNReal.ofReal (K * (stepFourGagliardoConst d s *
        (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ)))) := by
  have hR : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
  have hvol0 : volume (cubeSet Q) ≠ 0 := by
    intro h0
    have htoReal : (volume (cubeSet Q)).toReal = 0 := by rw [h0]; simp
    rw [volume_cubeSet_toReal] at htoReal
    exact (cubeVolume_pos Q).ne' htoReal
  have hvoltop : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hmain := normalizedGagliardoESeminormOn_le_of_holderHalf (A := cubeSet Q) (g := g)
    (K := K) (R := cubeScaleFactor Q) (s := s) hd (measurableSet_cubeSet Q) hvol0 hvoltop
    (fun x hx => cubeSet_subset_ball_of_mem hx) hR hs0 hs hK hg
  rwa [sqrt_scaleWeight_eq (Q := Q) hs] at hmain

/-- **The Step-2 display of the data embedding.**

`3^{sm} [g]_{H̲^s(□_m)} ≤ C_{S4.4}(d,s) K 3^{m/2}`: the Besov leg of Theorem C
priced by the §4.5 Hölder normalization, at the `3^{m/2}` scale Step 2 reads. -/
theorem three_rpow_mul_normalizedGagliardo_cubeSet_le {Q : TriadicCube d} {g : Vec d → E}
    {K s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (cubeSet Q) (1 / 2) K g) :
    ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
        Support.normalizedGagliardoESeminormOn (cubeSet Q) s g ≤
      ENNReal.ofReal (K * stepFourGagliardoConst d s *
        (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) / 2)) := by
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hC : (0 : ℝ) ≤ stepFourGagliardoConst d s := stepFourGagliardoConst_nonneg d s
  have hprod : (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
      (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ)) =
        (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
        Support.normalizedGagliardoESeminormOn (cubeSet Q) s g
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
          ENNReal.ofReal (K * (stepFourGagliardoConst d s *
            (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ)))) :=
        mul_le_mul' le_rfl (normalizedGagliardo_cubeSet_le_of_holderHalf hd hs0 hs hK hg)
    _ = ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
          (K * (stepFourGagliardoConst d s *
            (3 : ℝ) ^ ((1 / 2 - s) * ((Q.scale : ℤ) : ℝ))))) :=
        (ENNReal.ofReal_mul hw).symm
    _ = ENNReal.ofReal (K * stepFourGagliardoConst d s *
          (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) / 2)) := by
        congr 1
        rw [← hprod]
        ring

/-! ## 4. The pinned constant -/

/-- `C_data(d) = (2^{d+2} 3^d)^{1/2}`: the `γ`-free constant of the data
embedding at the §4.5 gate `s ≤ 1/4`. -/
def homDataConst (d : ℕ) : ℝ := Real.sqrt ((2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d)

theorem homDataConst_nonneg (d : ℕ) : 0 ≤ homDataConst d := Real.sqrt_nonneg _

theorem one_le_homDataConst (d : ℕ) : 1 ≤ homDataConst d := by
  rw [homDataConst, show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  refine Real.sqrt_le_sqrt ?_
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (d + 2) := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (d + 2) := le_trans zero_le_one h2
  have hprod : (1 : ℝ) * 1 ≤ (2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d :=
    mul_le_mul h2 h3 zero_le_one h4
  linarith only [hprod]

/-- **The `s`-dependence removed, under the explicit gate.**

For `0 < s ≤ 1/4` we have `1 - 2s ≥ 1/2`, so the `(1-2s)^{-1/2}` is at most
`2^{1/2}` and `C_{S4.4}(d,s) ≤ C_data(d)`.  The correction is respected: the
absorption happens ONLY under the displayed hypothesis `s ≤ 1/4`. -/
theorem stepFourGagliardoConst_le_homDataConst {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) :
    stepFourGagliardoConst d s ≤ homDataConst d := by
  have hlt : s < 1 / 2 := by linarith only [hs]
  have hgap : (1 : ℝ) / 2 ≤ 1 - 2 * s := by linarith only [hs]
  have hpos : (0 : ℝ) < 1 - 2 * s := by linarith only [hgap]
  have hnum : (0 : ℝ) < (2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hquot : (2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d / (1 - 2 * s) ≤
      (2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d := by
    rw [div_le_iff₀ hpos]
    have hexp : (2 : ℝ) ^ (d + 2) * (3 : ℝ) ^ d =
        2 * ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d) := by ring
    rw [hexp]
    have hscale : 2 * ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d) * (1 / 2) ≤
        2 * ((2 : ℝ) ^ (d + 1) * (3 : ℝ) ^ d) * (1 - 2 * s) :=
      mul_le_mul_of_nonneg_left hgap (by linarith only [hnum])
    linarith only [hscale]
  exact (stepFourGagliardoConst_le hs0 hlt).trans (Real.sqrt_le_sqrt hquot)

/-- **The pinned Step-2 display**: at `0 < s ≤ 1/4` the data embedding runs at
the `γ`-free constant `C_data(d)`. -/
theorem three_rpow_mul_normalizedGagliardo_cubeSet_le_pinned {Q : TriadicCube d}
    {g : Vec d → E} {K s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (cubeSet Q) (1 / 2) K g) :
    ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
        Support.normalizedGagliardoESeminormOn (cubeSet Q) s g ≤
      ENNReal.ofReal (K * homDataConst d * (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) / 2)) := by
  have hlt : s < 1 / 2 := by linarith only [hs]
  refine (three_rpow_mul_normalizedGagliardo_cubeSet_le hd hs0 hlt hK hg).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hscale : (0 : ℝ) ≤ (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := stepFourGagliardoConst_le_homDataConst (d := d) hs0 hs
  have hmul : K * stepFourGagliardoConst d s ≤ K * homDataConst d :=
    mul_le_mul_of_nonneg_left hstep hK
  exact mul_le_mul_of_nonneg_right hmul hscale

/-! ## 5. The §4.5 display: the `□_m` instance at the gated constant -/

/-- **The Step-2 data embedding in the form §4.5 consumes it.**

The display `three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`, at the
origin cube `□_m` in its open realization, with the `s`-dependent constant
replaced by the `γ`-free `C_data(d)` under the gate `s ≤ 1/4`:

```
  3^{ms} [g]_{H̲^s(□_m)} ≤ K · C_data(d) · 3^{m/2}.
```

Generic in `E`, hence one declaration for the datum `g` and for `∇h`.  With the
§4.5 normalization `K = 1` ('s `≤ 1` reading) this is exactly the Besov data
leg of Theorem C at the `3^{m/2}` scale. -/
theorem three_rpow_mul_normalizedGagliardo_originCube_le_pinned {m : ℤ}
    {g : Vec d → E} {K s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    ENNReal.ofReal ((3 : ℝ) ^ ((m : ℝ) * s)) *
        Support.normalizedGagliardoESeminormOn (openCubeSet (originCube d m)) s g ≤
      ENNReal.ofReal (K * homDataConst d * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
  have hlt : s < 1 / 2 := by linarith only [hs]
  refine (three_rpow_mul_normalizedGagliardoESeminormOn_cube_le hd hs0 hlt hK hg).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hscale : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hstep := stepFourGagliardoConst_le_homDataConst (d := d) hs0 hs
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hK) hscale

end

end Algsuperdiff.Section4.Provider.Homogenization
