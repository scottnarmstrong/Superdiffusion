/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenWireBridge
import Algsuperdiff.Section4.Provider.Regularity.StepSevenWireEmbedding
import Algsuperdiff.Section4.Provider.Regularity.StepSevenEndAssembly

/-!
# `t.regularity` Step 7d: the narrowed chain

## What this module does

`stepSevenEnd_chain` is the entry point for Step 7d.  It takes four named
conditional inputs across its three displays: `hcg`, `hlambda`, `hembed`,
`hbridge`.  Three of them are discharged here:

* `hcg` — `StepSevenWireCgMatching.exists_stepSevenCgPoincareInput_pinned`
  (CoarseGraining's `coarsePoincareRHSTheory`, at the pin `s₀ = 1/4`);
* `hembed` — `StepSevenWireEmbedding.stepSevenEmbedding` (the Section-3
  mean-zero multiscale Poincaré, with the coordinate aggregation and the
  off-grid recovery);
* `hbridge` — `StepSevenWireBridge.stepSevenBesovBridge` (the summability
  conversion).

`exists_stepSevenEnd_chain_of_lambda` is the narrowed entry point.  Its
remaining conditional inputs are exactly

```text
  { hlambda ,  the Step-7c hgrad display (which carries hcacc / hlambda / hosc) } ,
```

plus the caller's own geometry (`hmean`, `hcomp`, the three transports and the
two `Ktr` dominations) and the printed nonnegativity/window data.  Nothing else.

## The carriers of the composition

Everything is stated at the scale normalization of the cube `Q`, which under the
translate-the-sample convention is `originCube d (m'-1)` carrying the sample
translated by `z'`:

```text
  oscLoc  = 3^{-Q.scale}‖u - (u)_Q‖_{L̲²(Q)}                     (the embedding LHS)
  besovP1 = cubeBesovNegativeVectorSeminorm Q 1 (∇u)             (B̊^{-1}_{2,1})
  besov   = scaleNormalizedNegativeBesovVectorNorm Q s₀ (.finite 2) (∇u)
  gradLoc = forcedSolutionEnergyNorm Q a u ,  dataLoc = [𝐠]_{B̲^{s₀}_{2,2}(Q)}
```

with `s₀ = stepSevenCgS = 1/4`.  Neither Besov membership is a hypothesis: the
`B^{-s₀}_{2,2}` side is CoarseGraining's proved
`forcedSolutionGradientField_negativeBesovPartialSeminormTwo_bddAbove`
(automatic for every `ForcedCubeSolution`), and the `B^{-1}_{2,1}` side is
derived from it through the conversion (`bddAbove_partialOne_of_partialTwo`).

## References

* ABK26, Step 7d; `e.energy.density.estimate`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `B^{-1}_{2,1}` side's boundedness, derived from the `B^{-s}_{2,2}` one -/

/-- The conversion propagates boundedness: the `q = 1` partial seminorms are
bounded above whenever the `q = 2` ones at index `t < 1` are. -/
theorem bddAbove_partialOne_of_partialTwo (Q : TriadicCube d) {t : ℝ} (ht1 : t < 1)
    (F : Vec d → Vec d)
    (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q t N F)) :
    BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminorm Q 1 N F) := by
  refine ⟨stepSevenBridgeConst t * cubeBesovNegativeVectorSeminormTwo Q t F, ?_⟩
  rintro x ⟨N, rfl⟩
  refine le_trans (cubeBesovNegativeVectorPartialSeminorm_le_bridgeConst_mul Q ht1 F N) ?_
  exact mul_le_mul_of_nonneg_left (le_csSup hbdd (Set.mem_range_self N))
    (stepSevenBridgeConst_nonneg t)

/-- `hbridge` with the right-hand side in CoarseGraining's `q = 2` carrier — the
object `coarsePoincareRHSTheory` produces. -/
theorem stepSevenBridge_to_scaleNormalized (Q : TriadicCube d) {t : ℝ} (ht1 : t < 1)
    (F : Vec d → Vec d)
    (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q t N F)) :
    cubeBesovNegativeVectorSeminorm Q 1 F ≤
      stepSevenBridgeConst t *
        scaleNormalizedNegativeBesovVectorNorm Q t (Ch02.MultiscaleExponent.finite 2) F := by
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
  exact stepSevenBesovBridge Q ht1 F hbdd

/-! ## 2. The embedding and the conversion, composed -/

/-- **`hembed ∘ hbridge`, both discharged.**  At the note normalization of `Q`,

```text
  3^{-Q.scale}‖u - (u)_Q‖_{L̲²(Q)}
    ≤ (d·C_osc(d)) · C(t) · 3^{-t·Q.scale}‖∇u‖_{B^{-t}_{2,2}(Q)} ,
```

for every `t < 1`, with both constants. -/
theorem stepSevenEmbedBridge [NeZero d] (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) {t : ℝ} (ht1 : t < 1)
    (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q t N u.grad)) :
    (cubeScaleFactor Q)⁻¹ * cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
      stepSevenEmbeddingConst d * stepSevenBridgeConst t *
        scaleNormalizedNegativeBesovVectorNorm Q t
          (Ch02.MultiscaleExponent.finite 2) u.grad := by
  have hembed := stepSevenEmbedding Q u (bddAbove_partialOne_of_partialTwo Q ht1 u.grad hbdd)
  have hbridge := stepSevenBridge_to_scaleNormalized Q ht1 u.grad hbdd
  have hstep := mul_le_mul_of_nonneg_left hbridge (stepSevenEmbeddingConst_nonneg d)
  have hassoc : stepSevenEmbeddingConst d *
      (stepSevenBridgeConst t *
        scaleNormalizedNegativeBesovVectorNorm Q t
          (Ch02.MultiscaleExponent.finite 2) u.grad) =
      stepSevenEmbeddingConst d * stepSevenBridgeConst t *
        scaleNormalizedNegativeBesovVectorNorm Q t
          (Ch02.MultiscaleExponent.finite 2) u.grad := by ring
  linarith only [hembed, hstep, hassoc.ge, hassoc.le]

/-! ## 3. The narrowed chain -/

/-- **Step 7d, end to end, with `hcg`, `hembed` and `hbridge` discharged.**

The remaining conditional inputs are exactly `hlambda`
(`e.lambda.stability.applied`) and the Step-7c gradient display `hgrad`
(which carries `hcacc`, `hlambda`, `hosc`); everything else below is the
caller's geometry or the printed nonnegativity data.

The conclusion is `e.energy.density.estimate` at the printed exponent
`3^{(1-α)(m-n)}` with the printed data bracket. -/
theorem exists_stepSevenEnd_chain_of_lambda (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {alpha : ℝ} {n m : ℤ} {Q : TriadicCube d} {a : CoeffFamily d}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
        {Cg Cmean Clam Kg Kd Ks Ctr shomNp shomMp shomM
          gradLoc oscTrunc gradM dataG dataM W G H : ℝ},
        0 ≤ Cg → 0 ≤ Cmean → 0 ≤ Clam → 0 ≤ Ks → 0 ≤ shomMp → 0 < shomM →
        0 ≤ oscTrunc → 0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity Q stepSevenCgS g →
        stepSevenCgLamInv Q a stepSevenCgS ≤ Clam * shomMp →
        forcedSolutionEnergyNorm Q a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo Q stepSevenCgS g ≤ Kd * dataG →
        shomMp ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        oscTrunc ≤ Cmean * ((cubeScaleFactor Q)⁻¹ *
          cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toH1.toFun x)) →
        shomNp ≤ 2 * shomM →
        gradLoc ≤ Cg * Real.sqrt shomNp *
            Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) * oscTrunc +
          Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
            (Real.sqrt shomNp * (W * (shomM⁻¹ * G + H)) + dataM) →
          gradLoc ≤
            Cg * Real.sqrt 2 *
                (Cmean * stepSevenEmbeddingConst d * stepSevenBridgeConst stepSevenCgS *
                  (C * 64 * (Real.sqrt Clam + Clam)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              Cg * Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt 2 *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCgPoincareInput_pinned d
  refine ⟨C, hCpos, ?_⟩
  intro alpha n m Q a g u Cg Cmean Clam Kg Kd Ks Ctr shomNp shomMp shomM
    gradLoc oscTrunc gradM dataG dataM W G H
    hCg hCmean hClam hKs hshomMp hshomM hoscTrunc hgradM hdataG hW hG hH
    hforce hlambda htrGrad htrData htrShom hKgb hKdb hmean hcomp hgrad
  -- the data leg's nonnegativity: a field of the printed `𝐠 ∈ H^s` binder
  have hdataNN : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q stepSevenCgS g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q stepSevenCgS g
      hforce.partialSeminorms_bddAbove
  -- the `B^{-s₀}_{2,2}` membership: proved upstream, not a hypothesis
  have hbdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q stepSevenCgS N
          (forcedSolutionGradientField u)) :=
    forcedSolutionGradientField_negativeBesovPartialSeminormTwo_bddAbove u
      stepSevenCgS_pos
  -- the coarse-graining Poincaré, `hcg` discharged
  have hcg := hC (a := a) u hforce
  have hCcg : (0 : ℝ) ≤ C * 64 := by linarith only [hCpos]
  have hshomMinv : (0 : ℝ) ≤ shomM⁻¹ := (inv_pos.mpr hshomM).le
  have hE : (0 : ℝ) ≤ forcedSolutionEnergyNorm Q a u := by
    rw [forcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have hpoincare := stepSevenCgPoincareApplied hCcg hClam hKs hshomMp hshomMinv hE hdataNN
    hgradM hdataG hcg hlambda htrGrad htrData htrShom hKgb hKdb
  -- the embedding, `hembed` discharged
  have hembed := stepSevenEmbedding Q u.toH1
    (bddAbove_partialOne_of_partialTwo Q stepSevenCgS_lt_one
      (forcedSolutionGradientField u) hbdd)
  -- the summability conversion, `hbridge` discharged
  have hbridge := stepSevenBridge_to_scaleNormalized Q stepSevenCgS_lt_one
    (forcedSolutionGradientField u) hbdd
  -- the chain
  exact stepSevenEnd_chain hCg hCmean (stepSevenEmbeddingConst_nonneg d)
    (stepSevenBridgeConst_nonneg stepSevenCgS) hshomM hoscTrunc hW hG hH hcomp hgrad
    hmean hembed hbridge hpoincare

end

end Algsuperdiff.Section4.Provider.Regularity
