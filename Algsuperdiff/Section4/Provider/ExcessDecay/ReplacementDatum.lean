/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.ForcingCorrection
import Algsuperdiff.Section4.Provider.ExcessDecay.CoarseGrainingL2Interior

/-!
# The coarse-graining datum, populated

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {Q : TriadicCube d}

/-! ## 1. The populated datum -/

/-- **The coarse-graining comparison datum, constructed.**

`u` is the given solution of `−∇·a∇u = ∇·g`; `v` is the auxiliary
constant-coefficient solution `v_g`; the zero-trace difference is the chosen
corrector, and the identity `u − v_g = ρ_g` holds pointwise. -/
def coarseGrainingDatum (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : Ch03.IsForcedEquation Q a u g) (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.CoarseGrainingComparisonDatum Q a a0 g where
  u := u
  v := forcedReplacement a0 u hg
  uWeakSolution := hu
  vWeakSolution := isConstantCoeffForcedEquation_forcedReplacement a0 u hg
  zeroTraceDifference :=
    ⟨dirichletCorrector a0 u hg,
      Filter.Eventually.of_forall fun x => dirichletCorrector_toFun_eq_sub a0 u hg x⟩

@[simp] theorem coarseGrainingDatum_u (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hg : MemVectorL2 (openCubeSet Q) g) :
    (coarseGrainingDatum a a0 hu hg).u = u :=
  rfl

@[simp] theorem coarseGrainingDatum_v (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hg : MemVectorL2 (openCubeSet Q) g) :
    (coarseGrainingDatum a a0 hu hg).v = forcedReplacement a0 u hg :=
  rfl

/-! ## 2. The `H¹₀` test function on the half-open cube -/

/-- The chosen corrector, transported to the half-open cube: the `H¹₀` function
whose value is `u − v_g` and whose gradient is `∇u − ∇v_g`. -/
def replacementDefect (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H10Function (cubeSet Q) :=
  (dirichletCorrector a0 u hg).toCubeSet

theorem replacementDefect_grad (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementDefect a0 u hg).toH1Function.grad x =
      (coarseGrainingDatum a a0 hu hg).u.grad x -
        (coarseGrainingDatum a a0 hu hg).v.grad x := by
  rw [replacementDefect, H10Function.toCubeSet_toH1Function_grad,
    coarseGrainingDatum_u, coarseGrainingDatum_v]
  exact dirichletCorrector_grad_eq_sub a0 u hg x

theorem replacementDefect_toFun (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementDefect a0 u hg).toH1Function.toFun x =
      u.toFun x - (forcedReplacement a0 u hg).toFun x := by
  rw [replacementDefect, H10Function.toCubeSet_toH1Function_toFun]
  exact dirichletCorrector_toFun_eq_sub a0 u hg x

/-! ## 3. The coarse-graining leg at the §4.3 slot, from the equation alone -/

/-- For `0 < σ̄`, `0 < s ≤ 1`, `g ∈ L²(W) ∩ H^s(W)` and `u` solving
`−∇·a∇u = ∇·g` weakly on `W = openCubeSet Q`:

```text
  σ̄ · 3^{-scale(Q)} ‖u − v_g‖_{L̲²(Q)}
      ≤ 3 C_neg(d) C_cg(d) ·
          ( (1024/3) s^{-4} · (energy term)
          + (16384/3) s^{-6} · (forcing term) ) ,
```

with `v_g` the auxiliary solution `forcedReplacement`. -/
theorem coarseGraining_l2_slot_le_of_isForcedEquation {a : Ch03.CoeffFamily d}
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hgL2 : MemVectorL2 (openCubeSet Q) g) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hg : Ch03.ForceBesovRegularity Q s g) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
          (replacementDefect (scalarComparator hsigma0) u hgL2).toH1Function.toFun x) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
        ((1024 / 3) * (s⁻¹) ^ (4 : ℕ) *
            coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 4) u +
          (16384 / 3) * (s⁻¹) ^ (6 : ℕ) *
            coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 4) s g) :=
  coarseGraining_l2_slot_le hsigma0
    (coarseGrainingDatum a (scalarComparator hsigma0) hu hgL2)
    (replacementDefect (scalarComparator hsigma0) u hgL2)
    (replacementDefect_grad a (scalarComparator hsigma0) hu hgL2) hs hs1 hg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
