/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineFinalEndpoint
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineGamma0

/-!
# Theorem B, §4.5: the spine endpoint with `hY` DISCHARGED

## What is closed here

`HomSpineFinalWitness` reported a BLOCKED COMPOSITION: the `HomStepOneAnchor`
and the `HomSpineGamma0` both declared `homGamma0`/`homGamma0_pos`, so no
module could import both cones and `hY` had to stay a binder.  The pair is now
named `homGamma0Gate`/`homGamma0Gate_pos`; the composition is therefore
writable, and it is written here.

`homogenization_spine_endpoint`'s abstract `[0,∞]`-valued observable `Y` and
its exponential-moment binder `hY` are replaced by

* `X: Ω → ℕ∞`, the Theorem-C minimal scale itself, with `Measurable X`;
* `htail`, the Theorem-C tail `P{X ≥ N} ≤ C e^{-(1-α)²(N-C)/(Cγ)}`,

at `Y:= homMinimalScaleFactor (1 - homAlpha M) X = 3^{(1-α)X}` and
`C_gate:= homGateRangeConst C⋆`.  The `γ`-threshold is
`min γ₀^{end} (min (homGamma0Gate C⋆) (1/81))`: the first clause feeds the
endpoint, the second is the collapse of the three displayed gates of
`homY_moment_bound`, and the third buys `4 ≤ |log γ|`, which is the only other
hypothesis `homY_moment_bound_of_gamma_le` needs.

`hY` is GONE from the conditional set.  What is left is exactly `{hC1,
hclauses}` plus the Theorem-C tail `htail`, which is the declared dependency
Theorem C of the Step 1 (the moment bound) and not an internal obligation of
§4.5.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-- **THE SPINE ENDPOINT, with `hY` DISCHARGED.**

`homogenization_spine_endpoint` composed with the
`homY_moment_bound_of_gamma_le`: the abstract observable `Y` and its
exponential-moment hypothesis are replaced by the Theorem-C minimal scale `X`
and its tail, at `Y = 3^{(1-α)X}` and `C_gate = homGateRangeConst C⋆`.

The conditional set is `{htail, hC1, hclauses}`, and `htail` is the declared
Theorem C edge of this step, not an internal §4.5 obligation. -/
theorem homogenization_spine_endpoint_of_minimalScaleTail (d : ℕ) [NeZero d]
    (cstar : ℝ) (hcstar : 0 < cstar) {Cst Cgap Kabs Cflow : ℝ}
    (hCst : 1 ≤ Cst) (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) (hCflow : 0 ≤ Cflow) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
          (∀ N : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
              ENNReal.ofReal (Cst *
                Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
                  (Cst * M.gamma)))) →
          ∀ hs : 0 < homS M, ∀ m : ℤ, ∀ sigmaBarM : ℝ, 0 < sigmaBarM →
            |sigmaBarM -
                Real.sqrt (M.nu ^ (2 : ℕ) +
                  cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
              Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM →
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplier M Cgap
                (homMinimalScaleFactor (1 - homAlpha M) X) m hs sigmaBarM Kabs omega) →
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
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_endpoint d cstar hcstar (Cgate := homGateRangeConst Cst)
      (Cgap := Cgap) (Kabs := Kabs) (Cflow := Cflow) (homGateRangeConst_pos hCst) hCgap
      hKabs hCflow
  refine ⟨min g0 (min (homGamma0Gate Cst) (1 / 81)), C,
    lt_min hg0 (lt_min (homGamma0Gate_pos hCst) (by norm_num)), hC, ?_⟩
  intro M hcs hgamma X hX htail hs m sigmaBarM hsig hC1 hclauses
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_end : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hg_gate : M.gamma ≤ homGamma0Gate Cst :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg_81 : M.gamma ≤ 1 / 81 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_right _ _))
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  refine hend M hcs hg_end (homMinimalScaleFactor (1 - homAlpha M) X)
    (measurable_homMinimalScaleFactor _ hX) ?_ hs m sigmaBarM hsig hC1 hclauses
  intro p hp hrange
  exact homY_moment_bound_of_gamma_le M hX hCst hp hL4 hg_gate hrange htail

end

end Algsuperdiff.Section4.Provider.Homogenization
