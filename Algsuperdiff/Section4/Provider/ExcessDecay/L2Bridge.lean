/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.ForceTransport
import Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms
import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue

/-!
# The `L²` carrier bridge of the interior clause

```text
  eLpNorm (fun y => u y - (u)_W) 2 (normalizedVolumeMeasureOn W) ,
      W = ((z + □_{n+2}) ∩ □_m) ,
```

an `ℝ≥0∞` `L²` norm on the anchor's window.

* the `⨍`-square versus the normalized `L²` norm on an **open** cube —
  CoarseGraining's `normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq`,
  whose `MemLp` side condition is discharged here from the `H¹` structure
  itself (`H1Function.memL2`), not assumed;
* the real translation `z`, which moves the norm and the subtracted mean
  together (`ForceTransport.lean` for the norm, CoarseGraining's
  `volumeAverage_translateSet_eq_comp_addRight` for the mean).

Both are equalities: the bridge introduces **no constant**.

## Main results

* `memLp_two_normalizedCubeMeasure_of_h1`,
  `memLp_two_sub_volumeAverage_of_h1` — the `L²` data of an `H¹` function in the
  normalized cube measure.
* `normalizedL2SqOnSet_sub_average_eq_eLpNorm_sq` — the `⨍`-square is the square
  of the normalized `L²` norm (at the origin cube).

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the `‖u - (u)_W‖_{L̲²(W)}`
  slot).
* CoarseGraining,
  `Homogenization/Book/Ch03/Theorems/CoarseCaccioppoli/ZeroTraceValue.lean`,
  `Homogenization/Book/Ch01/Theorems/NormScaling.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `L²` data of an `H¹` function in the normalized measure -/

/-- The normalized cube measure is the volume-normalized restriction to the
**open** cube. -/
theorem normalizedCubeMeasure_eq_smul_restrict_openCubeSet (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- An `H¹` function on the open cube is `L²` for the normalized cube
measure. -/
theorem memLp_two_normalizedCubeMeasure_of_h1 (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    MemLp u.toFun 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_restrict_openCubeSet]
  exact u.memL2.smul_measure ENNReal.ofReal_ne_top

/-- Its mean-subtracted version is `L²` too (the normalized cube measure is
finite, so constants are `L²`). -/
theorem memLp_two_sub_volumeAverage_of_h1 (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    MemLp (fun y => u.toFun y - volumeAverage (openCubeSet Q) u.toFun) 2
      (normalizedCubeMeasure Q) := by
  letI : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact (memLp_two_normalizedCubeMeasure_of_h1 Q u).sub
    (memLp_const (volumeAverage (openCubeSet Q) u.toFun))

/-! ## 2. The `⨍`-square is the normalized `L²` norm squared -/

theorem normalizedL2SqOnSet_sub_average_eq_eLpNorm_sq (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u.toFun y - volumeAverage (openCubeSet Q) u.toFun) =
      ((eLpNorm (fun y => u.toFun y - volumeAverage (openCubeSet Q) u.toFun) 2
        (Support.normalizedVolumeMeasureOn (openCubeSet Q))).toReal) ^ (2 : ℕ) := by
  rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _
      (memLp_two_sub_volumeAverage_of_h1 Q u),
    normalizedVolumeMeasureOn_openCubeSet]
  rfl

/-- The same for a bare function with an explicit `L²` datum (the form in which
the composed interior estimate consumes it, after the `H¹` carrier has been
eliminated). -/
theorem normalizedL2SqOnSet_sub_average_eq_eLpNorm_sq_of_memLp (Q : TriadicCube d)
    (v : Vec d → ℝ) (hv : MemLp v 2 (normalizedCubeMeasure Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun y => v y - volumeAverage (openCubeSet Q) v) =
      ((eLpNorm (fun y => v y - volumeAverage (openCubeSet Q) v) 2
        (Support.normalizedVolumeMeasureOn (openCubeSet Q))).toReal) ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hsub : MemLp (fun y => v y - volumeAverage (openCubeSet Q) v) 2
      (normalizedCubeMeasure Q) :=
    hv.sub (memLp_const (volumeAverage (openCubeSet Q) v))
  rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hsub,
    normalizedVolumeMeasureOn_openCubeSet]
  rfl

/-! ## 3. The bridge to the anchor's window -/

/-- **The `L²` carrier bridge, in bare-function form.** -/
theorem normalizedL2SqOnSet_translate_sub_average_eq_eLpNorm_sq_image_add
    {z : Vec d} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp (fun y => f (y + z)) 2 (normalizedCubeMeasure Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun y => f (y + z) -
          volumeAverage (openCubeSet Q) (fun x => f (x + z))) =
      ((eLpNorm
          (fun y => f y - volumeAverage ((fun y' => z + y') '' openCubeSet Q) f) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y' => z + y') '' openCubeSet Q))).toReal) ^ (2 : ℕ) := by
  have havg : volumeAverage ((fun y' => z + y') '' openCubeSet Q) f =
      volumeAverage (openCubeSet Q) (fun x => f (x + z)) := by
    rw [image_add_eq_translateSet z (openCubeSet Q)]
    exact normalizedSetAverage_translateSet z (openCubeSet Q) f
  have hnorm : eLpNorm
        (fun y => f y - volumeAverage ((fun y' => z + y') '' openCubeSet Q) f) 2
        (Support.normalizedVolumeMeasureOn ((fun y' => z + y') '' openCubeSet Q)) =
      eLpNorm
        (fun y => f (y + z) - volumeAverage (openCubeSet Q) (fun x => f (x + z))) 2
        (Support.normalizedVolumeMeasureOn (openCubeSet Q)) := by
    rw [eLpNorm_normalizedVolumeMeasureOn_image_add z (openCubeSet Q)
      (by norm_num) (by norm_num), havg]
  rw [hnorm]
  exact normalizedL2SqOnSet_sub_average_eq_eLpNorm_sq_of_memLp Q _ hf

/-- **The `L²` carrier bridge.**

Let `u` be the transported solution on the origin cube, i.e. `u.toFun y = f (y
+ z)` for the anchor's own solution value `f` on `□_m`.  The norm and the
subtracted mean move together and no constant appears. -/
theorem normalizedL2SqOnSet_h1_sub_average_eq_eLpNorm_sq_image_add
    {z : Vec d} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    {f : Vec d → ℝ} (hf : ∀ y, u.toFun y = f (y + z)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u.toFun y - volumeAverage (openCubeSet Q) u.toFun) =
      ((eLpNorm
          (fun y => f y - volumeAverage ((fun y' => z + y') '' openCubeSet Q) f) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y' => z + y') '' openCubeSet Q))).toReal) ^ (2 : ℕ) := by
  have hfun : u.toFun = fun y => f (y + z) := funext hf
  have havg : volumeAverage ((fun y' => z + y') '' openCubeSet Q) f =
      volumeAverage (openCubeSet Q) u.toFun := by
    rw [image_add_eq_translateSet z (openCubeSet Q), hfun]
    exact normalizedSetAverage_translateSet z (openCubeSet Q) f
  have hnorm : eLpNorm
        (fun y => f y - volumeAverage ((fun y' => z + y') '' openCubeSet Q) f) 2
        (Support.normalizedVolumeMeasureOn ((fun y' => z + y') '' openCubeSet Q)) =
      eLpNorm (fun y => u.toFun y - volumeAverage (openCubeSet Q) u.toFun) 2
        (Support.normalizedVolumeMeasureOn (openCubeSet Q)) := by
    rw [eLpNorm_normalizedVolumeMeasureOn_image_add z (openCubeSet Q)
      (by norm_num) (by norm_num), havg, hfun]
  rw [hnorm, normalizedL2SqOnSet_sub_average_eq_eLpNorm_sq Q u]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
