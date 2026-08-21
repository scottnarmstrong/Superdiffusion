/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFiveBudgetSums
import Algsuperdiff.Section4.Provider.Regularity.StepFiveShomComparison
import Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# `t.regularity` Step 5: the concrete `δ_j` family

## The target

ABK26 `t.regularity` Step 5, — the `δ_j` slot of the iteration lemma at the
Step-5 instantiation:

```text
  δ_j := C 3^{j/2} σ̄_j^{-1} [g]_{W̲^{1/2,∞}(□_m)}
         + C ( 3^{j/2} [∇h]_{W̲^{1/2,∞}(□_m)}
               + ε_j ‖∇h‖_{L^∞(□_m)} ) 1_{z ∉ □_{m-1}} .
```

## The `ℝ≥0∞ → ℝ` layer, and where `toReal`'s convention is load-bearing

`[·]_{W̲^{1/2,∞}(□_m)}` is `normalizedGagliardoTopESeminormOn` — an `ℝ≥0∞`-valued
essential supremum — while `l.iteration.lemma` demands `δ: ℤ → ℝ`.  The junk
value `(⊤).toReal = 0` is therefore in play, and its status is settled here
once and for all:

* **Guarded (inert) in everything this tree proves.**  Every inequality of this
  module and of `StepFiveDeltaSum` carries the SAME `toReal` atoms on both
  sides — the family is bounded above by an expression built from its own
  seminorm values.  A `⊤` seminorm makes both sides `0`; no statement becomes
  false, and no statement becomes vacuous.
* That corner is closed here, not waved at:
  `stepFiveHalfSeminorm_le_of_holderSeminormBound` and
  `stepFiveLinftyNorm_le_of_bound` show both objects are finite — indeed
  bounded by the very real scalars the root anchor types them with.

```lean
  Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g
  Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad
  ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf
```

The two bridge theorems below take exactly those three hypotheses and return
`stepFiveHalfSeminorm m g ≤ Kg`, `stepFiveHalfSeminorm m h.grad ≤ Kh`, and
`stepFiveLinftyNorm m h.grad ≤ KhInf`.  So the finiteness the `toReal` layer
needs is data the roots already carry; nothing new is assumed.

## Readings of the printed list

* **D3 (the `ε` inside `δ_j`).**  The manuscript's Step-5 list sets `ε_j:= C
  ε_j(z)` and then writes `δ_j`'s boundary leg as `C (… + ε_j ‖∇h‖_{L^∞}) 1`,
  i.e. `C² ε_j(z) ‖∇h‖_{L^∞} 1`.  The proved tree pins the iteration lemma's
  `ε` slot at the `ε_j(z)` (`e.sum.eps.j.bound` is proved at `C = 1`), so
  the family below reads `C ε_j(z) ‖∇h‖_{L^∞} 1`.  The two differ by one factor
  of the generic `C = C(d,c⋆)`.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal
open scoped Classical

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The three cube-level data of `δ_j`, as reals -/

/-- **`[f]_{W̲^{1/2,∞}(□_m)}` as a real number**: the `toReal` layer over the
`ℝ≥0∞`-valued carrier `normalizedGagliardoTopESeminormOn`. -/
def stepFiveHalfSeminorm (m : ℤ) (f : Vec d → E) : ℝ :=
  (normalizedGagliardoTopESeminormOn (openCubeSet (originCube d m)) (1 / 2) f).toReal

theorem stepFiveHalfSeminorm_nonneg (m : ℤ) (f : Vec d → E) :
    0 ≤ stepFiveHalfSeminorm m f :=
  ENNReal.toReal_nonneg

/-- **`‖f‖_{L^∞(□_m)}` as a real number**: the `toReal` layer over the essential
supremum of `f` against the volume restricted to the cube. -/
def stepFiveLinftyNorm (m : ℤ) (f : Vec d → E) : ℝ :=
  (eLpNorm f ∞ (volume.restrict (openCubeSet (originCube d m)))).toReal

omit [NormedSpace ℝ E] in
theorem stepFiveLinftyNorm_nonneg (m : ℤ) (f : Vec d → E) :
    0 ≤ stepFiveLinftyNorm m f :=
  ENNReal.toReal_nonneg

/-- **`1_{z ∉ □_{m-1}}`**, the boundary indicator of `δ_j`'s second leg. -/
def stepFiveBoundaryIndicator (z : Vec d) (m : ℤ) : ℝ :=
  if z ∈ openCubeSet (originCube d (m - 1)) then 0 else 1

theorem stepFiveBoundaryIndicator_nonneg (z : Vec d) (m : ℤ) :
    0 ≤ stepFiveBoundaryIndicator z m := by
  rw [stepFiveBoundaryIndicator]
  split
  · norm_num
  · norm_num

/-! ## 2. The finiteness bridges: the roots' own `h`-legs -/

/-- The Gagliardo difference quotient of a `C^{0,s}(A)` field is bounded by the
Hölder constant at every pair of points of `A`.  The degenerate pair `x = y` is
where the kernel's `dist^{-s}` would blow up; there the numerator vanishes
first, so the quotient is `0`. -/
theorem norm_gagliardoKernel_top_le_of_holderSeminormBound {A : Set (Vec d)} {s K : ℝ}
    (hK : 0 ≤ K) {f : Vec d → E} (hf : Support.HolderSeminormBoundOn A s K f)
    {w : Vec d × Vec d} (hw : w ∈ A ×ˢ A) :
    ‖Gagliardo.gagliardoKernel s ∞ f w‖ ≤ K := by
  obtain ⟨hw1, hw2⟩ := hw
  rw [Gagliardo.gagliardoKernel_apply, Gagliardo.kernelExponent_top]
  by_cases hxy : w.1 = w.2
  · have h0 : f w.1 - f w.2 = 0 := by rw [hxy, sub_self]
    rw [h0, smul_zero, norm_zero]
    exact hK
  · have hdpos : 0 < dist w.1 w.2 := dist_pos.mpr hxy
    have hdn : ‖w.1 - w.2‖ = dist w.1 w.2 := (dist_eq_norm _ _).symm
    have hb : ‖f w.1 - f w.2‖ ≤ K * dist w.1 w.2 ^ s := by
      have h := hf w.1 hw1 w.2 hw2
      rwa [hdn] at h
    have hpow : dist w.1 w.2 ^ (-s) * dist w.1 w.2 ^ s = 1 := by
      rw [← Real.rpow_add hdpos, neg_add_cancel, Real.rpow_zero]
    have hnn : (0 : ℝ) ≤ dist w.1 w.2 ^ (-s) := Real.rpow_nonneg hdpos.le _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc dist w.1 w.2 ^ (-s) * ‖f w.1 - f w.2‖
        ≤ dist w.1 w.2 ^ (-s) * (K * dist w.1 w.2 ^ s) :=
          mul_le_mul_of_nonneg_left hb hnn
      _ = K * (dist w.1 w.2 ^ (-s) * dist w.1 w.2 ^ s) := by ring
      _ = K := by rw [hpow, mul_one]

/-- **The `W̲^{s,∞}` finiteness bridge**: a `C^{0,s}(A)` bound caps the
volume-normalized `p = ∞` Gagliardo seminorm at the SAME constant. -/
theorem normalizedGagliardoTopESeminormOn_le_of_holderSeminormBound {A : Set (Vec d)}
    (hA : MeasurableSet A) {s K : ℝ} (hK : 0 ≤ K) {f : Vec d → E}
    (hf : Support.HolderSeminormBoundOn A s K f) :
    normalizedGagliardoTopESeminormOn A s f ≤ ENNReal.ofReal K := by
  have hmeas : Support.normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
    rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
      Measure.prod_smul_left, Measure.prod_restrict]
  rw [normalizedGagliardoTopESeminormOn_def, eLpNorm_exponent_top, hmeas]
  refine eLpNormEssSup_le_of_ae_bound ?_
  refine Measure.ae_smul_measure ?_ _
  refine ae_restrict_of_forall_mem (hA.prod hA) ?_
  intro w hw
  exact norm_gagliardoKernel_top_le_of_holderSeminormBound hK hf hw

/-- The `toReal` form of the bridge, at the cube and the index `1/2`: the root's
`Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1/2) K f` leg —
its `Kg` and `Kh` slots verbatim — caps `stepFiveHalfSeminorm`. -/
theorem stepFiveHalfSeminorm_le_of_holderSeminormBound {m : ℤ} {K : ℝ} (hK : 0 ≤ K)
    {f : Vec d → E}
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    stepFiveHalfSeminorm m f ≤ K :=
  ENNReal.toReal_le_of_le_ofReal hK
    (normalizedGagliardoTopESeminormOn_le_of_holderSeminormBound
      (isOpen_openCubeSet _).measurableSet hK hf)

/-- The seminorm is under the root's leg — the statement that makes the `toReal`
layer honest. -/
theorem normalizedGagliardoTopESeminormOn_ne_top_of_holderSeminormBound {m : ℤ} {K : ℝ}
    (hK : 0 ≤ K) {f : Vec d → E}
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    normalizedGagliardoTopESeminormOn (openCubeSet (originCube d m)) (1 / 2) f ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (normalizedGagliardoTopESeminormOn_le_of_holderSeminormBound
      (isOpen_openCubeSet _).measurableSet hK hf)

omit [NormedSpace ℝ E] in
/-- **The `L^∞` finiteness bridge**: the root's pointwise leg `∀ x ∈ □_m, ‖h.grad
x‖ ≤ KhInf` — its `KhInf` slot verbatim — caps `stepFiveLinftyNorm`. -/
theorem stepFiveLinftyNorm_le_of_bound {m : ℤ} {K : ℝ} (hK : 0 ≤ K) {f : Vec d → E}
    (hf : ∀ x ∈ openCubeSet (originCube d m), ‖f x‖ ≤ K) :
    stepFiveLinftyNorm m f ≤ K := by
  refine ENNReal.toReal_le_of_le_ofReal hK ?_
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound
    (ae_restrict_of_forall_mem (isOpen_openCubeSet _).measurableSet hf)

/-! ## 3. The two geometric ratios -/

def stepFiveRatioG (M : ABKModel d) : ℝ := (3 : ℝ) ^ (-(1 / 2 - M.gamma))

/-- `r₂ := 3^{-1/2}`, the geometric ratio of `δ_j`'s `∇h`-leg. -/
def stepFiveRatioH : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))

theorem stepFiveRatioG_pos (M : ABKModel d) : 0 < stepFiveRatioG M :=
  three_rpow_neg_half_add_gamma_pos M.gamma

theorem stepFiveRatioG_lt_one {M : ABKModel d} (hgamma : M.gamma < 1 / 2) :
    stepFiveRatioG M < 1 :=
  three_rpow_neg_half_add_gamma_lt_one hgamma

theorem stepFiveRatioH_pos : (0 : ℝ) < stepFiveRatioH :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem stepFiveRatioH_lt_one : stepFiveRatioH < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The exact scale identity behind the `∇h`-leg's domination: `3^{j/2} = 3^{m/2} ·
(3^{-1/2})^{m-j}`, with the `(m-j)`-power an integer power of the fixed ratio — the
shape `StepFiveGeometricTail` sums. -/
theorem three_rpow_half_eq_mul_ratioH_zpow (m j : ℤ) :
    (3 : ℝ) ^ ((j : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) * stepFiveRatioH ^ (m - j) := by
  rw [stepFiveRatioH, ← three_rpow_mul_intCast (-(1 / 2 : ℝ)) (m - j),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

/-! ## 4. The concrete `δ_j` family and its two legs -/

/-- **`δ_j`'s `g`-leg**: `C 3^{j/2} σ̄_j^{-1} [g]_{W̲^{1/2,∞}(□_m)}`. -/
def stepFiveDeltaGLeg (M : ABKModel d) (C : ℝ) (m : ℤ) (gflux : Vec d → E) (j : ℤ) : ℝ :=
  C * (3 : ℝ) ^ ((j : ℝ) / 2) * ((Annealed.sigmaBar M j : ℝ))⁻¹ * stepFiveHalfSeminorm m gflux

/-- **`δ_j`'s `∇h`-leg**: `C 3^{j/2} [∇h]_{W̲^{1/2,∞}(□_m)}` (the indicator is carried
by `δ_j` itself). -/
def stepFiveDeltaHLeg (C : ℝ) (m : ℤ) (gradh : Vec d → E) (j : ℤ) : ℝ :=
  C * ((3 : ℝ) ^ ((j : ℝ) / 2) * stepFiveHalfSeminorm m gradh)

/-- **The concrete `δ_j` family**, at the Step-5 instantiation:

```text
  δ_j(z,ω) = C 3^{j/2} σ̄_j^{-1} [g]_{W̲^{1/2,∞}(□_m)}
             + C ( 3^{j/2} [∇h]_{W̲^{1/2,∞}(□_m)}
                   + ε_j(z,ω) ‖∇h‖_{L^∞(□_m)} ) 1_{z ∉ □_{m-1}} .
```

`ε_j(z,ω)` is `stepFiveEps` (reading D3 above); both `1/2`-seminorms are
`normalizedGagliardoTopESeminormOn` through `toReal`, and `‖·‖_{L^∞}` is the
essential supremum on the cube, likewise through `toReal`. -/
def stepFiveDelta (M : ABKModel d) (C : ℝ) (m : ℤ) (z : Vec d) (gflux gradh : Vec d → E)
    (delta : ℝ) (omega : Cutoff.CutoffSample d) (j : ℤ) : ℝ :=
  C * (3 : ℝ) ^ ((j : ℝ) / 2) * ((Annealed.sigmaBar M j : ℝ))⁻¹ *
      stepFiveHalfSeminorm m gflux +
    C * ((3 : ℝ) ^ ((j : ℝ) / 2) * stepFiveHalfSeminorm m gradh +
        stepFiveEps M j z delta omega * stepFiveLinftyNorm m gradh) *
      stepFiveBoundaryIndicator z m

/-- The family in the exact three-leg shape's `sum_Icc_delta_le_of_legs` consumes,
with `Hinf := C ‖∇h‖_{L^∞(□_m)}`. -/
theorem stepFiveDelta_eq_legs (M : ABKModel d) (C : ℝ) (m : ℤ) (z : Vec d)
    (gflux gradh : Vec d → E) (delta : ℝ) (omega : Cutoff.CutoffSample d) (j : ℤ) :
    stepFiveDelta M C m z gflux gradh delta omega j =
      stepFiveDeltaGLeg M C m gflux j +
        (stepFiveDeltaHLeg C m gradh j +
            stepFiveEps M j z delta omega * (C * stepFiveLinftyNorm m gradh)) *
          stepFiveBoundaryIndicator z m := by
  rw [stepFiveDelta, stepFiveDeltaGLeg, stepFiveDeltaHLeg]
  ring

theorem stepFiveDeltaGLeg_nonneg {C : ℝ} (hC : 0 ≤ C) (M : ABKModel d) (m : ℤ)
    (gflux : Vec d → E) (j : ℤ) : 0 ≤ stepFiveDeltaGLeg M C m gflux j := by
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((j : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ ((Annealed.sigmaBar M j : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M j).2.le
  rw [stepFiveDeltaGLeg]
  exact mul_nonneg (mul_nonneg (mul_nonneg hC h1) h2) (stepFiveHalfSeminorm_nonneg m gflux)

theorem stepFiveDeltaHLeg_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℤ) (gradh : Vec d → E) (j : ℤ) :
    0 ≤ stepFiveDeltaHLeg C m gradh j := by
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((j : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  rw [stepFiveDeltaHLeg]
  exact mul_nonneg hC (mul_nonneg h1 (stepFiveHalfSeminorm_nonneg m gradh))

/-- `δ_j ≥ 0` — the sign hypothesis of `l.iteration.lemma`. -/
theorem stepFiveDelta_nonneg {C : ℝ} (hC : 0 ≤ C) (M : ABKModel d) (m : ℤ) (z : Vec d)
    (gflux gradh : Vec d → E) (delta : ℝ) (omega : Cutoff.CutoffSample d) (j : ℤ) :
    0 ≤ stepFiveDelta M C m z gflux gradh delta omega j := by
  rw [stepFiveDelta_eq_legs]
  have hg := stepFiveDeltaGLeg_nonneg hC M m gflux j
  have hh := stepFiveDeltaHLeg_nonneg hC m gradh j
  have he : 0 ≤ stepFiveEps M j z delta omega * (C * stepFiveLinftyNorm m gradh) :=
    mul_nonneg (stepFiveEps_nonneg M j z delta omega)
      (mul_nonneg hC (stepFiveLinftyNorm_nonneg m gradh))
  have hmul : 0 ≤ (stepFiveDeltaHLeg C m gradh j +
      stepFiveEps M j z delta omega * (C * stepFiveLinftyNorm m gradh)) *
        stepFiveBoundaryIndicator z m :=
    mul_nonneg (by linarith only [hh, he]) (stepFiveBoundaryIndicator_nonneg z m)
  linarith only [hg, hmul]

/-! ## 5. The two per-scale dominations -/

/-- **`K_g`**, the top-scale coefficient of the `g`-leg: `C · 4 · 3^{m/2} σ̄_m^{-1}
[g]_{W̲^{1/2,∞}(□_m)}`. -/
def stepFiveKg (M : ABKModel d) (C : ℝ) (m : ℤ) (gflux : Vec d → E) : ℝ :=
  C * (4 * ((3 : ℝ) ^ ((m : ℝ) / 2) * ((Annealed.sigmaBar M m : ℝ))⁻¹) *
    stepFiveHalfSeminorm m gflux)

/-- **`K_h`**, the top-scale coefficient of the `∇h`-leg: `C · 3^{m/2}
[∇h]_{W̲^{1/2,∞}(□_m)}`. -/
def stepFiveKh (C : ℝ) (m : ℤ) (gradh : Vec d → E) : ℝ :=
  C * ((3 : ℝ) ^ ((m : ℝ) / 2) * stepFiveHalfSeminorm m gradh)

theorem stepFiveKg_nonneg {C : ℝ} (hC : 0 ≤ C) (M : ABKModel d) (m : ℤ)
    (gflux : Vec d → E) : 0 ≤ stepFiveKg M C m gflux := by
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M m).2.le
  rw [stepFiveKg]
  exact mul_nonneg hC
    (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg h1 h2))
      (stepFiveHalfSeminorm_nonneg m gflux))

theorem stepFiveKh_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℤ) (gradh : Vec d → E) :
    0 ≤ stepFiveKh C m gradh := by
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  rw [stepFiveKh]
  exact mul_nonneg hC (mul_nonneg h1 (stepFiveHalfSeminorm_nonneg m gradh))

/-- ```text
  C 3^{j/2} σ̄_j^{-1} [g]  ≤  K_g · r₁^{m-j}          (j ≤ m ≤ m₀) .
``` -/
theorem stepFiveDeltaGLeg_le_zpow {M : ABKModel d} {m0 : ℤ} {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap) {C : ℝ} (hC : 0 ≤ C)
    {gflux : Vec d → E} {j m : ℤ} (hjm : j ≤ m) (hm : m ≤ m0) :
    stepFiveDeltaGLeg M C m gflux j ≤ stepFiveKg M C m gflux * stepFiveRatioG M ^ (m - j) := by
  have hcomp := three_rpow_half_mul_inv_sigmaBar_le_of_inductionState hS hjm hm
  have hfac : (0 : ℝ) ≤ C * stepFiveHalfSeminorm m gflux :=
    mul_nonneg hC (stepFiveHalfSeminorm_nonneg m gflux)
  have h := mul_le_mul_of_nonneg_left hcomp hfac
  have hL : C * stepFiveHalfSeminorm m gflux *
      ((3 : ℝ) ^ ((j : ℝ) / 2) * ((Annealed.sigmaBar M j : ℝ))⁻¹)
      = stepFiveDeltaGLeg M C m gflux j := by
    rw [stepFiveDeltaGLeg]
    ring
  have hR : C * stepFiveHalfSeminorm m gflux *
      (4 * ((3 : ℝ) ^ (-(1 / 2 - M.gamma))) ^ (m - j) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) * ((Annealed.sigmaBar M m : ℝ))⁻¹))
      = stepFiveKg M C m gflux * stepFiveRatioG M ^ (m - j) := by
    rw [stepFiveKg, stepFiveRatioG]
    ring
  rw [← hL, ← hR]
  exact h

/-- **The `∇h`-leg's per-scale domination**, the elementary identity
`3^{j/2} = 3^{m/2} (3^{-1/2})^{m-j}`:

```text
  C 3^{j/2} [∇h]  ≤  K_h · r₂^{m-j}          (every j) .
``` -/
theorem stepFiveDeltaHLeg_le_zpow (C : ℝ) (m : ℤ) (gradh : Vec d → E) (j : ℤ) :
    stepFiveDeltaHLeg C m gradh j ≤ stepFiveKh C m gradh * stepFiveRatioH ^ (m - j) := by
  refine le_of_eq ?_
  rw [stepFiveDeltaHLeg, stepFiveKh, three_rpow_half_eq_mul_ratioH_zpow m j]
  ring

end

end Algsuperdiff.Section4.Provider.Regularity
