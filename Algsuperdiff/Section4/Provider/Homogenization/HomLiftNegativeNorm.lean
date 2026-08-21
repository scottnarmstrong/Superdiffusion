/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomLiftScaleArith
import Homogenization.Deterministic.WeakNormInterfaces.Definitions
import Homogenization.Book.Ch03.Definitions

/-!
# Theorem B, §4.5, Step 3c: the `(∞,∞)` negative Besov carrier

## The carrier pin

The manuscript's Step-3 object is `‖∇u - ∇v‖_{Ŵ̲^{-s,∞}(□_m)}` (the weak
gradient bound; the bridge display in the paper drops the hat).  The manuscript
**never defines** this norm: The manuscript defines only the order `-1` dual
seminorms, and the only negative-order fractional object defined anywhere is
the negative Besov seminorm the negative Besov seminorm definition,

```text
  [F]_{B̲^{-s}_{p,q}(□_m)} = ( Σ_{n ≤ m} 3^{sqn} ( avsum_{z} |(F)_{z+□_n}|^p )^{q/p} )^{1/q}
```

(the printed weight `3^{sqm}` is the index typo recorded as).  Under the
Besov--Sobolev dictionary `W^{-s,p} ≃ B^{-s}_{p,p}` the Step-3 object is the
`(p,q) = (∞,∞)` member of this family: the supremum over scales of `3^{s n}`
times the **maximum** over the subcubes at scale `n` of the cube averages of
`F`.

That inner `p = ∞` — a maximum over subcubes, not an `ℓ^p` average — is
load-bearing for the author's mechanism.  A gradient concentrated on a single
subcube at depth `j` has `ℓ^2`-averaged depth quantity smaller than its maximum
by the factor `3^{-jd/2}`, so the `(2, ∞)` gauge does **not** control a
pointwise Hölder seminorm, while the `(∞,∞)` gauge does.  `CoarseGraining`'s
public `scaleNormalizedNegativeBesovVectorNorm Q s.infinity` is the `(2,∞)`
gauge (its depth quantity is `Real.sqrt (descendantsAverage …)`), so it is
*not* the Step-3 carrier; this module supplies the `(∞,∞)` gauge and proves the
comparison in the only direction that holds
(`scaleNormalizedNegativeBesovVectorNorm_infinity_le_of_bound`).

## Main definitions and results

* `negBesovInftyDepthMax` — the depth-`j` maximum `max_R ‖(F)_R‖` over the
  triadic descendants of `Q` at depth `j`, in the Euclidean vector norm `CoarseGraining`'s
  negative Besov family uses.
* `negBesovInftyDepthSeminorm` — the weighted depth quantity `3^{-sj} · max`.
* `negBesovInftyNorm` — the `(∞,∞)` gauge, `sSup` over the depths.
* `negBesovInftyDepthSeminorm_eq_scaleNormalized` — the identification of the
  weight with the manuscript's `3^{-ms} · 3^{ns}` at the source scale
  `n = Q.scale - j`.
* `negativeBesovVectorDepthSeminorm_le_negBesovInftyDepthSeminorm` — the
  `(2,·) ≤ (∞,·)` comparison, depth by depth.
* `scaleNormalizedNegativeBesovVectorNorm_infinity_le_of_bound` — an `(∞,∞)`
  bound implies `CoarseGraining`'s `(2,∞)` bound at the same constant.

## References

* ABK26, the negative Besov seminorm definition; the weak gradient bound; the bridge display.
-/

open Homogenization Homogenization.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The `(∞,∞)` gauge -/

/-- The depth-`j` **maximum** of the cube averages of `F` over the triadic
descendants of `Q`, measured in the Euclidean vector norm
`Real.sqrt ∘ vecNormSq` used by `CoarseGraining`'s negative Besov family.

This is the `p = ∞` inner index of the negative Besov seminorm definition. -/
def negBesovInftyDepthMax (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  (descendantsAtDepth Q j).sup' (descendantsAtDepth_nonempty Q j)
    fun R => Real.sqrt (vecNormSq (cubeAverageVec R F))

/-- The weighted depth-`j` quantity of the `(∞,∞)` gauge. -/
def negBesovInftyDepthSeminorm (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-s * (j : ℝ)) * negBesovInftyDepthMax Q F j

/-- **The `(∞,∞)` scale-normalized negative Besov gauge on a triadic cube** —
the `q = ∞` outer index applied to `negBesovInftyDepthSeminorm`.

The scale normalization is the manuscript's: the depth weight `3^{-sj}`
already carries the factor `3^{-s·Q.scale}` of the display's left side (see
`negBesovInftyDepthSeminorm_eq_scaleNormalized`). -/
def negBesovInftyNorm (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  sSup (Set.range fun j : ℕ => negBesovInftyDepthSeminorm Q s F j)

theorem negBesovInftyDepthMax_def (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) :
    negBesovInftyDepthMax Q F j =
      (descendantsAtDepth Q j).sup' (descendantsAtDepth_nonempty Q j)
        (fun R => Real.sqrt (vecNormSq (cubeAverageVec R F))) := rfl

theorem negBesovInftyDepthSeminorm_def (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) (j : ℕ) :
    negBesovInftyDepthSeminorm Q s F j =
      (3 : ℝ) ^ (-s * (j : ℝ)) * negBesovInftyDepthMax Q F j := rfl

theorem negBesovInftyNorm_def (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    negBesovInftyNorm Q s F =
      sSup (Set.range fun j : ℕ => negBesovInftyDepthSeminorm Q s F j) := rfl

/-! ## 2. Elementary API -/

/-- Every descendant's average is dominated by the depth maximum. -/
theorem le_negBesovInftyDepthMax {Q : TriadicCube d} {F : Vec d → Vec d} {j : ℕ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    Real.sqrt (vecNormSq (cubeAverageVec R F)) ≤ negBesovInftyDepthMax Q F j :=
  Finset.le_sup' (f := fun R => Real.sqrt (vecNormSq (cubeAverageVec R F))) hR

/-- A uniform bound on the descendants' averages bounds the depth maximum. -/
theorem negBesovInftyDepthMax_le {Q : TriadicCube d} {F : Vec d → Vec d} {j : ℕ} {c : ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec R F)) ≤ c) :
    negBesovInftyDepthMax Q F j ≤ c :=
  Finset.sup'_le (descendantsAtDepth_nonempty Q j) _ h

theorem negBesovInftyDepthMax_nonneg (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ negBesovInftyDepthMax Q F j := by
  obtain ⟨R, hR⟩ := descendantsAtDepth_nonempty Q j
  exact (Real.sqrt_nonneg _).trans (le_negBesovInftyDepthMax hR)

theorem negBesovInftyDepthSeminorm_nonneg (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) (j : ℕ) : 0 ≤ negBesovInftyDepthSeminorm Q s F j :=
  mul_nonneg (three_rpow_nonneg _) (negBesovInftyDepthMax_nonneg Q F j)

/-- **The manuscript's normalization.**  The depth weight `3^{-sj}` is exactly
`3^{-s·m} · 3^{s·n}` at the source scale `n = Q.scale - j`, i.e. the gauge is
the display's left-hand quantity `3^{-ms}‖·‖_{B̲^{-s}_{∞,∞}(□_m)}`. -/
theorem negBesovInftyDepthSeminorm_eq_scaleNormalized (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) (j : ℕ) :
    negBesovInftyDepthSeminorm Q s F j =
      (3 : ℝ) ^ (-(s * ((Q.scale : ℤ) : ℝ))) *
        ((3 : ℝ) ^ (s * (((Q.scale - (j : ℤ)) : ℤ) : ℝ)) *
          negBesovInftyDepthMax Q F j) := by
  rw [negBesovInftyDepthSeminorm_def, ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 2
  push_cast
  ring

/-! ## 3. The `(2,·) ≤ (∞,·)` comparison -/

/-- **Depth by depth, the `ℓ^2`-averaged gauge is dominated by the maximum
gauge.**  This is the direction that holds; the reverse fails by the factor
`3^{jd/2}` on a gradient concentrated in one descendant. -/
theorem negativeBesovVectorDepthSeminorm_le_negBesovInftyDepthSeminorm
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    negativeBesovVectorDepthSeminorm Q s F j ≤ negBesovInftyDepthSeminorm Q s F j := by
  have hM : 0 ≤ negBesovInftyDepthMax Q F j := negBesovInftyDepthMax_nonneg Q F j
  have hbd : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (cubeAverageVec R F) ≤ negBesovInftyDepthMax Q F j ^ (2 : ℕ) := by
    intro R hR
    have hsq : Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ (2 : ℕ)
        = vecNormSq (cubeAverageVec R F) :=
      Real.sq_sqrt (vecNormSq_nonneg _)
    calc vecNormSq (cubeAverageVec R F)
        = Real.sqrt (vecNormSq (cubeAverageVec R F)) ^ (2 : ℕ) := hsq.symm
      _ ≤ negBesovInftyDepthMax Q F j ^ (2 : ℕ) :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_negBesovInftyDepthMax hR) 2
  have havg : negativeBesovVectorDepthAverage Q F j ≤ negBesovInftyDepthMax Q F j ^ (2 : ℕ) := by
    have hmono := descendantsAverage_le_descendantsAverage Q j hbd
    rwa [descendantsAverage_const_eq Q j (negBesovInftyDepthMax Q F j ^ (2 : ℕ))] at hmono
  have hsqrt : Real.sqrt (negativeBesovVectorDepthAverage Q F j)
      ≤ negBesovInftyDepthMax Q F j := by
    have := Real.sqrt_le_sqrt havg
    rwa [Real.sqrt_sq hM] at this
  exact mul_le_mul_of_nonneg_left hsqrt (three_rpow_nonneg _)

/-- **An `(∞,∞)` bound implies `CoarseGraining`'s `(2,∞)` bound at the same constant.**

The Step-3 hypothesis is therefore strictly stronger than the `CoarseGraining`
public gauge at the `.infinity` outer index, and any downstream consumer stated
at the `CoarseGraining` gauge is served by the `(∞,∞)` carrier. -/
theorem scaleNormalizedNegativeBesovVectorNorm_infinity_le_of_bound
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ j : ℕ, negBesovInftyDepthSeminorm Q s F j ≤ A) :
    scaleNormalizedNegativeBesovVectorNorm Q s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity F ≤ A := by
  refine Real.sSup_le ?_ hA
  rintro x ⟨j, rfl⟩
  exact (negativeBesovVectorDepthSeminorm_le_negBesovInftyDepthSeminorm Q s F j).trans (hbd j)

/-- The gauge is bounded by any uniform bound on its depth quantities. -/
theorem negBesovInftyNorm_le (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) {A : ℝ}
    (hA : 0 ≤ A) (hbd : ∀ j : ℕ, negBesovInftyDepthSeminorm Q s F j ≤ A) :
    negBesovInftyNorm Q s F ≤ A := by
  refine Real.sSup_le ?_ hA
  rintro x ⟨j, rfl⟩
  exact hbd j

end

end Algsuperdiff.Section4.Provider.Homogenization
