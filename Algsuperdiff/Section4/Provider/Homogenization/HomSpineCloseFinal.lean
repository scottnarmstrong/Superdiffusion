/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineCloseGate
import Algsuperdiff.Frozen.Section3.InductionBounds

/-!
# Theorem B, §4.5: the spine at `{htail, hclauses}`

## What is closed here

Clause (C1) is **not** available from `Algsuperdiff.Frozen.Section3.
diffusivity_asymptotics`: that is the CONDITIONAL mid-chain statement, and it
carries binders the §4.5 root does not have (`mStar M < m₀`,
`inductionState M (m₀-1) E`, the `C_flow c⋆⁻¹ ≤ E` regime, `γ ≤ E⁻¹¹⁰`).

It comes instead from `Algsuperdiff.Frozen.Section3.induction_bounds`, which
carries the SAME `σ̄_m` closeness display as its second conjunct

```text
  |σ̄_m − √(ν² + c⋆ γ⁻¹ 3^{2γm})| ≤ C c⋆⁻² √γ |log γ| σ̄_m      (∀ m: ℤ)
```

with `mStar`, `inductionState` and the `E`-regime ALREADY RUN OUT inside its
provider (the `m₀:= max m (mStar M + 1)` landmark device), under the single
hypothesis

```text
  γ ≤ (C⁻¹)^{10} (c⋆(M))^{10},
```

which is a pure `γ`-threshold — and the §4.5 spine fixes `c⋆` BEFORE its own
`∃ γ₀`, so a `γ₀` depending on `c⋆` is exactly what the endpoint may choose.
The consumption pattern is the
`Provider/Proportion/G2CubeBound.exists_isTwoTermBigOWith_annularErrorObservable`,
which takes the anchor's other conjunct at the identical regime.

So `hC1` is DISCHARGED here, at `σ̄_m:= Annealed.sigmaBar M m` (positivity from
the `PositiveScalar` carrier) and `C_flow:= C c⋆⁻²`.  The trivial witness
`σ̄_m = √(ν² + c⋆γ⁻¹3^{2γm})` is not used and is not needed; taking the genuine
running diffusivity keeps `hclauses` and `hC1` on the SAME `σ̄_m`, which the
Step-2a producers (`HomStepTwoEnergy.exists_sqrt_nu_mul_gradL2_le`, whose
conclusion names `Annealed.sigmaBar M m` literally) require.

## The conditional set of `homogenization_spine_close`, itemized and complete

1. `htail` — the Theorem-C minimal-scale tail
   `P{X ≥ N} ≤ C e^{-(1-α)²(N-C)/(Cγ)}`, i.e. Theorem C, a declared dependency
   edge of the Step 1 (the moment bound).  Not an
   internal §4.5 obligation.
2. `hclauses` — the per-`ω` `HomSpineClauseSupplier`.  Its body is produced by
   `HomSpineCloseClause.spineClauseBody_of_coarseGraining` from ONE application
   of the transcribed printed proposition `hCG'`
   (the general coarse-graining proposition at finite `p`), the
   Schauder external, and the Step-2b/3b data feed.  `hCG'` is a DECLARED
   source hypothesis of the Step-3a node.

`hY` is gone (`HomSpineCloseGate`), `hC1` is gone (here).  Nothing else remains.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-- **THE SPINE, at `{htail, hclauses}`.**

The frozen root's conclusion body from the Theorem-C tail and the per-`ω`
clause supplier alone.  `hY` was discharged in `HomSpineCloseGate` (the
`homY_moment_bound_of_gamma_le`), and `hC1` is discharged here off the
Section-3 anchor `induction_bounds`, at the genuine running diffusivity
`Annealed.sigmaBar M m`. -/
theorem homogenization_spine_close (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar)
    {Cst Cgap Kabs : ℝ} (hCst : 1 ≤ Cst) (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
          (∀ N : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
              ENNReal.ofReal (Cst *
                Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
                  (Cst * M.gamma)))) →
          ∀ hs : 0 < homS M, ∀ m : ℤ,
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplier M Cgap
                (homMinimalScaleFactor (1 - homAlpha M) X) m hs
                ((Annealed.sigmaBar M m : ℝ)) Kabs omega) →
            ∃ sigmaBar : ℝ, 0 < sigmaBar ∧
              |sigmaBar -
                  Real.sqrt (M.nu ^ (2 : ℕ) +
                    cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
                C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar ∧
              ∃ EB : Cutoff.CutoffSample d → ℝ,
                (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
                (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
                  (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                    ENNReal.ofReal
                        (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                          Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p) ∧
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ L : ℤ, m ≤ L →
                    ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                      (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u h g →
                      IsDirichletSolutionOn
                          (fun _ => sigmaBar • (1 : Mat d)) (originCube d m) v h g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kg g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh h.grad →
                      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                      (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                        Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                          EB omega *
                            (sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                        |volumeAverage (openCubeSet (originCube d m))
                              (fun y => M.nu * vecNormSq (u.grad y)) -
                            volumeAverage (openCubeSet (originCube d m))
                              (fun y => sigmaBar * vecNormSq (v.grad y))| ≤
                          EB omega *
                            (Real.sqrt sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                Real.sqrt sigmaBar *
                                  (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                              (2 : ℕ) := by
  obtain ⟨Cib, hCib, hbounds⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  have hcinv : (0 : ℝ) ≤ cstar⁻¹ ^ (2 : ℕ) := pow_nonneg (inv_nonneg.mpr hcstar.le) 2
  have hCflow : (0 : ℝ) ≤ Cib * cstar⁻¹ ^ (2 : ℕ) := mul_nonneg hCib.le hcinv
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_endpoint_of_minimalScaleTail d cstar hcstar (Cst := Cst)
      (Cgap := Cgap) (Kabs := Kabs) (Cflow := Cib * cstar⁻¹ ^ (2 : ℕ)) hCst hCgap hKabs
      hCflow
  have hreg0 : (0 : ℝ) < (Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ) :=
    mul_pos (pow_pos (inv_pos.mpr hCib) 10) (pow_pos hcstar 10)
  refine ⟨min g0 ((Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ)), C, lt_min hg0 hreg0, hC, ?_⟩
  intro M hcs hgamma X hX htail hs m hclauses
  have hreg : M.gamma ≤ (Cib⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    rw [hcs]
    exact le_trans hgamma (min_le_right _ _)
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hC1 := (hbounds M hreg).2 m
  rw [hcs] at hC1
  exact hend M hcs (le_trans hgamma (min_le_left _ _)) X hX htail hs m
    ((Annealed.sigmaBar M m : ℝ)) hsig hC1 hclauses

end

end Algsuperdiff.Section4.Provider.Homogenization
