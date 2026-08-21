/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepFourIdentity
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderPoincare

/-!
# Theorem B, §4.5, Step 4: the comparator is UNIQUE (`∀ v` from `∃ v`)

## The gap this closes

`HomSpineFinalStepFour` discloses one deviation from the frozen root's shape:
the root quantifies `∀ v` over comparators solving

```text
  v ∈ H¹(□_m),   -∇·(σ̄_m ∇v) = ∇·g  in □_m,   v = h  on ∂□_m,
```

while the Schauder package PRODUCES a comparator, so the conclusion is `∃ v`.
The two differ by exactly the uniqueness of the Dirichlet comparator, and that
is proved here, unconditionally:

1. **gradient uniqueness** (`dirichletComparator_grad_ae_eq`) — both equations
   are tested against the SAME `H¹₀(□_m)` element `w = v₁ - v₂` (produced by
   `HomStepFourIdentity.exists_h10Function_grad_eq_sub` from the two zero-trace
   witnesses at the shared datum `h`); the two forcing functionals are the same
   functional of the same `g` and cancel, leaving `σ̄_m ∫_{□_m} |∇w|² = 0`.
   Since `σ̄_m > 0` and the integrand is nonnegative and integrable (the `H¹`
   membership of both gradients, `integrableOn_vecDot_of_memVectorL2`), `∇w = 0`
   a.e.
2. **function uniqueness** (`dirichletComparator_toFun_ae_eq`) — `w ∈ H¹₀(□_m)`
   with vanishing gradient, so the zero-trace Poincaré inequality at the cube's
   own scale (`Schauder.eLpNorm_le_schauderDirichletPoincare`, `Frozen`-free,
   read at the inscribing cube `0 + □_m`) forces `‖w‖_{L²(□_m)} = 0`.  The
   `L²` finiteness that the `.toReal` step needs is the `H¹` structure's own
   `memL2` field, not a new hypothesis.

**NOTE (this file's instruction to mine first).**  Both ingredients
were already in the repository and nothing analytic is added here: the testing
mechanism is `HomStepFourIdentity`'s and the Poincaré
inequality is the Schauder cone's
`eLpNorm_le_schauderDirichletPoincare`, used at `W = openCubeSet (originCube d
m)`, `c = 0`, `n = m` exactly as `CubeSchauderTopScale` uses it.  No fresh
analysis was needed and the boundary chain was not required.

## The payoff

`dirichletComparator_clauses_transfer` moves the root's two clause bodies from
the produced comparator `v'` to an ARBITRARY comparator `v`: the (C3) display
because `v =ᵐ v'`, the (C4) display because `∇v =ᵐ ∇v'` and `volumeAverage` is
an integral.  So a producer that delivers the clauses at `∃ v` delivers them at
`∀ v`, which is the root's own quantifier.
-/

open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The `H¹₀` difference, at the level of values as well as gradients -/

/-- The value of an `H¹₀` difference. -/
private theorem h10_sub_toFun {U : Set (Vec d)} (a b : H10Function U) (x : Vec d) :
    (a - b).toH1Function.toFun x = a.toH1Function.toFun x - b.toH1Function.toFun x := by
  show (a.toH1Function + ((-1 : ℝ) • b.toH1Function)).toFun x = _
  rw [H1Function.add_toFun, H1Function.smul_toFun]
  ring

/-- **The `H¹₀` difference of two solutions with the same boundary datum**, with
BOTH pointwise identities.  `HomStepFourIdentity.exists_h10Function_grad_eq_sub`
records the gradient half; the value half is what the `L²` Poincaré step
consumes. -/
theorem exists_h10Function_sub_of_hasZeroTrace {U : Set (Vec d)}
    {u v h : H1Function U} (hu : HasZeroTraceDifferenceOn U u h)
    (hv : HasZeroTraceDifferenceOn U v h) :
    ∃ w : H10Function U,
      (∀ x, w.toH1Function.toFun x = u.toFun x - v.toFun x) ∧
        ∀ x, w.toH1Function.grad x = u.grad x - v.grad x := by
  obtain ⟨wu, hwuF, hwuG⟩ := hu
  obtain ⟨wv, hwvF, hwvG⟩ := hv
  refine ⟨wu - wv, fun x => ?_, fun x => ?_⟩
  · rw [h10_sub_toFun wu wv x, hwuF x, hwvF x]
    ring
  · obtain ⟨w0, hw0⟩ :=
      exists_h10Function_grad_eq_sub (u := u) (v := v) (h := h) ⟨wu, hwuF, hwuG⟩
        ⟨wv, hwvF, hwvG⟩
    have hval : (wu - wv).toH1Function.grad x = u.grad x - v.grad x := by
      have hu' : u.grad x = h.grad x + wu.toH1Function.grad x := hwuG x
      have hv' : v.grad x = h.grad x + wv.toH1Function.grad x := hwvG x
      have hsub : (wu - wv).toH1Function.grad x =
          wu.toH1Function.grad x - wv.toH1Function.grad x := by
        show (wu.toH1Function + ((-1 : ℝ) • wv.toH1Function)).grad x = _
        rw [H1Function.add_grad, H1Function.smul_grad]
        simp only [neg_smul, one_smul]
        rw [sub_eq_add_neg]
      rw [hsub, hu', hv']
      abel
    exact hval

/-! ## 2. Gradient uniqueness -/

/-- **The comparator's gradient is unique.**

Two solutions of the SAME scalar Dirichlet problem `-∇·(σ̄∇v) = ∇·g`, `v = h`
on `∂□_m`, have a.e. equal gradients.  Both weak equations are tested against
their own difference; the forcing terms cancel and the resulting Dirichlet
energy of the difference vanishes. -/
theorem dirichletComparator_grad_ae_eq {Q : TriadicCube d} {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {v v' h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hv : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) Q v h g)
    (hv' : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) Q v' h g) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), v.grad x = v'.grad x := by
  obtain ⟨w, _, hwG⟩ := exists_h10Function_sub_of_hasZeroTrace hv.1 hv'.1
  /- the two tested equatio -/
  have h1 := hv.2 w
  have h2 := hv'.2 w
  simp only [matVecMul_smul_one, vecDot_smul_left] at h1 h2
  rw [MeasureTheory.integral_const_mul] at h1 h2
  have hne : sigmaBarM ≠ 0 := ne_of_gt hsig
  have hAB : (∫ x in openCubeSet Q, vecDot (v.grad x) (w.toH1Function.grad x) ∂volume) =
      ∫ x in openCubeSet Q, vecDot (v'.grad x) (w.toH1Function.grad x) ∂volume := by
    have := h1.trans h2.symm
    exact mul_left_cancel₀ hne this
  /- the two pairings are integrab -/
  have hIA : IntegrableOn (fun x => vecDot (v.grad x) (w.toH1Function.grad x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
      w.toH1Function.grad_memVectorL2
  have hIB : IntegrableOn (fun x => vecDot (v'.grad x) (w.toH1Function.grad x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 v'.grad_memVectorL2
      w.toH1Function.grad_memVectorL2
  /- the Dirichlet energy of the difference vanish -/
  have hzero : (∫ x in openCubeSet Q, vecNormSq (w.toH1Function.grad x) ∂volume) = 0 := by
    have hsub : (∫ x in openCubeSet Q,
        (vecDot (v.grad x) (w.toH1Function.grad x) -
          vecDot (v'.grad x) (w.toH1Function.grad x)) ∂volume) = 0 := by
      rw [MeasureTheory.integral_sub hIA hIB, hAB, sub_self]
    refine Eq.trans (MeasureTheory.integral_congr_ae ?_) hsub
    refine Filter.Eventually.of_forall fun x => ?_
    have hpt : vecDot (v.grad x) (w.toH1Function.grad x) -
        vecDot (v'.grad x) (w.toH1Function.grad x) =
        vecNormSq (w.toH1Function.grad x) := by
      rw [← vecDot_sub_left, ← hwG x]
      rfl
    exact hpt.symm
  have hInt : IntegrableOn (fun x => vecNormSq (w.toH1Function.grad x))
      (openCubeSet Q) volume := by
    have h := integrableOn_vecDot_of_memVectorL2
      (U := openCubeSet Q) w.toH1Function.grad_memVectorL2
      w.toH1Function.grad_memVectorL2
    exact h
  have hnn : (0 : Vec d → ℝ) ≤ fun x => vecNormSq (w.toH1Function.grad x) :=
    fun x => vecNormSq_nonneg _
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn hInt).mp hzero
  refine hae.mono fun x hx => ?_
  have hx0 : w.toH1Function.grad x = 0 := vecNormSq_eq_zero hx
  have := hwG x
  rw [hx0] at this
  have hfin : v.grad x - v'.grad x = 0 := this.symm
  exact sub_eq_zero.mp hfin

/-! ## 3. Function uniqueness, through the zero-trace Poincaré inequality -/

/-- **The comparator itself is unique.**

The `H¹₀` difference has vanishing gradient, so the Dirichlet Poincaré
inequality at the cube's own scale (`Schauder.eLpNorm_le_schauderDirichletPoincare`
at the inscribing cube `0 + □_m`) gives `‖v - v'‖_{L²(□_m)} = 0`.  The `L²`
finiteness needed to pass from `.toReal ≤ 0` to the vanishing of the seminorm is
the `H¹` structure's own `memL2` field. -/
theorem dirichletComparator_toFun_ae_eq [NeZero d] {m : ℤ} {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM)
    {v v' h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hv : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g)
    (hv' : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v' h g) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))), v.toFun x = v'.toFun x := by
  obtain ⟨w, hwF, hwG⟩ := exists_h10Function_sub_of_hasZeroTrace hv.1 hv'.1
  have hgrad := dirichletComparator_grad_ae_eq hsig hv hv'
  /- every coordinate of the difference's gradient vanishes a. -/
  have hcoord : ∀ i : Fin d,
      eLpNorm (fun y => w.toH1Function.grad y i) 2
        (volume.restrict (openCubeSet (originCube d m))) = 0 := by
    intro i
    have hz : (fun y => w.toH1Function.grad y i) =ᵐ[volume.restrict
        (openCubeSet (originCube d m))] fun _ => (0 : ℝ) := by
      refine hgrad.mono fun x hx => ?_
      have := hwG x
      rw [hx, sub_self] at this
      show w.toH1Function.grad x i = 0
      rw [this]
      rfl
    rw [eLpNorm_congr_ae hz]
    exact eLpNorm_zero
  /- the Poincaré inequality at the inscribing cube `0 + □_m` -/
  have hinscribe : ∀ y ∈ openCubeSet (originCube d m), ∀ j : Fin d,
      (0 : Vec d) j - (1 / 2 : ℝ) * (3 : ℝ) ^ m < y j ∧
        y j < (0 : Vec d) j + (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    intro y hy j
    have hj := mem_openCubeSet_originCube_iff.1 hy j
    exact ⟨by simpa using by linarith only [hj.1], by simpa using by linarith only [hj.2]⟩
  have hpoin := Schauder.eLpNorm_le_schauderDirichletPoincare
    (measurableSet_openCubeSet (originCube d m)) 0 m hinscribe w
  have hsum : (∑ i : Fin d,
      (eLpNorm (fun y => w.toH1Function.grad y i) 2
        (volume.restrict (openCubeSet (originCube d m)))).toReal) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcoord i]
    rfl
  rw [hsum, mul_zero] at hpoin
  /- the `L²` seminorm of the difference is finite, hence ze -/
  have hfin : eLpNorm w.toFun 2
      (volume.restrict (openCubeSet (originCube d m))) ≠ ⊤ :=
    w.toH1Function.memL2.eLpNorm_ne_top
  have htoReal : (eLpNorm w.toFun 2
      (volume.restrict (openCubeSet (originCube d m)))).toReal = 0 :=
    le_antisymm hpoin ENNReal.toReal_nonneg
  have hzero : eLpNorm w.toFun 2
      (volume.restrict (openCubeSet (originCube d m))) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with h | h
    · exact h
    · exact absurd h hfin
  have hae : w.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))] 0 :=
    (eLpNorm_eq_zero_iff w.toH1Function.memL2.aestronglyMeasurable (by norm_num)).mp hzero
  refine hae.mono fun x hx => ?_
  have hx0 : w.toH1Function.toFun x = 0 := hx
  have := hwF x
  rw [hx0] at this
  have hfin2 : v.toFun x - v'.toFun x = 0 := this.symm
  exact sub_eq_zero.mp hfin2

/-! ## 4. `∀ v` from `∃ v`: the clause transfer -/

/-- **The comparator's energy average is comparator-independent.**

`⨍_{□} σ̄|∇v|²` is the same number for every solution of the comparator
problem, because `volumeAverage` is an integral and the gradients agree a.e.
This is the (C4) half of the `∀ v`-from-`∃ v` transfer. -/
theorem dirichletComparator_energyAverage_eq {Q : TriadicCube d} {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {v v' h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hv : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) Q v h g)
    (hv' : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) Q v' h g) :
    volumeAverage (openCubeSet Q) (fun y => sigmaBarM * vecNormSq (v.grad y)) =
      volumeAverage (openCubeSet Q) (fun y => sigmaBarM * vecNormSq (v'.grad y)) := by
  have hgrad := dirichletComparator_grad_ae_eq hsig hv hv'
  rw [volumeAverage, volumeAverage]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine hgrad.mono fun x hx => ?_
  show sigmaBarM * vecNormSq (v.grad x) = sigmaBarM * vecNormSq (v'.grad x)
  rw [hx]

/-- **THE TRANSFER: the root's `∀ v` from the Schauder package's `∃ v`.**

Given the two clause bodies at the PRODUCED comparator `v'`, they hold at every
comparator `v` of the same Dirichlet problem.  (C3) transfers because `v =ᵐ v'`
and the display is an a.e. statement; (C4) transfers because `∇v =ᵐ ∇v'` and
`volumeAverage` is an integral. -/
theorem dirichletComparator_clauses_transfer [NeZero d] {m : ℤ}
    {sigmaBarM nu Bd Be : ℝ} (hsig : 0 < sigmaBarM)
    {u v v' h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hv : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g)
    (hv' : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v' h g)
    (hC3 : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v'.toFun x| ≤ Bd)
    (hC4 : |volumeAverage (openCubeSet (originCube d m))
            (fun y => nu * vecNormSq (u.grad y)) -
          volumeAverage (openCubeSet (originCube d m))
            (fun y => sigmaBarM * vecNormSq (v'.grad y))| ≤ Be) :
    (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
        Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤ Bd) ∧
      |volumeAverage (openCubeSet (originCube d m))
            (fun y => nu * vecNormSq (u.grad y)) -
          volumeAverage (openCubeSet (originCube d m))
            (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤ Be := by
  have hfun := dirichletComparator_toFun_ae_eq hsig hv hv'
  refine ⟨?_, ?_⟩
  · refine (hC3.and hfun).mono fun x hx => ?_
    rw [hx.2]
    exact hx.1
  · rw [dirichletComparator_energyAverage_eq hsig hv hv']
    exact hC4

end

end Algsuperdiff.Section4.Provider.Homogenization
