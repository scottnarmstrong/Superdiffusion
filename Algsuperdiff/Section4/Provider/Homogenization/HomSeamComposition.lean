/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamSupClauseProvider

/-!
# The composition target: `generator_renormalization`, unconditionally

## The remaining distance, named

`GeneratorRenormalizationShape d cstar` is the frozen conclusion, named
once so that the composition can be stated without a `sorry`.  The composition
theorem

```text
  generatorRenormalizationShape_of_supClauseProducer: SupClauseProducerAt d cstar → GeneratorRenormalizationShape d cstar
```

reduces the `generator_renormalization` root, at every `d` and every `cstar > 0`,
to ONE remaining object: an a.e. producer of the sup-form multiscale clause at
some positive `γ₀`.  Nothing else is left: the `C_gap` slot is pinned to the
numeral `1`, and the factor `D3` is discharged inside
(`HomSeamBudgetArith.recut_geomFactor_le_absLog`).

## THE EXACT REMAINING APPLICATIONS

To produce `SupClauseProducerAt d cstar` one has to run, at each admissible
`M`, `m` and a.e. `ω`, and at every `L ≥ m` and every datum tuple:

1. `HomSpineSupFormClause.exists_coarseGrainingSupMultiscale_of_depthConverseOn`
   at `p = recutExponent d hd1` (`= 4d`), `hp = recutExponent_two_le`, the
   predicate `Pred s:= s = recutOrderBase M hlog`, and the dual-converse
   constant `CA` — the target interface.  Its ONE hypothesis is
   `NegativeBesovGridSmoothDualConverseAtDepth (originCube d m) s p j CA` at
   every depth `j`.
2. The constant reconciliation `Ccg ≤ recutPinnedCcgFlux d (recutExponent d hd1)`:
   the clause carrier of `RecutCoreSupplyFluxSupClause` is pinned at the lane's
   own constant, while (1) produces its own `Ccg = √d · CA · C(p,d)`.  Either
   `CoarseGrainingSupMultiscale` must be shown monotone in `Ccg`, or the pin
   must be re-cut at a model-dependent `CcgF` — see the open question below.
3. The five datum instantiations of (1): `a:= fluxCorrectedCoeffOn M L m
   (originCube d m) ω`, `sigma0:= Annealed.sigmaBar M m`, the forced-equation
   and `H¹₀`-difference legs (`HomSpineDataBridge`), `Gen:= printedLocalEnergy
   a u`, and `Fgrad`/`Fflux` at the centred difference fields.
4. The three domination legs `E1`, `E2`, `Dg` at the pinned slots
   `recutPinnedE1Flux`, `recutPinnedE2Flux`, `recutPinnedDg` (all three already
   have self-domination lemmas: `parentErrorOne_dominates_self`,
   `parentErrorTwo_dominates_self`, `overlapSeminorm_dominates_self`).

OPEN QUESTION.  Item 2 is a genuine open interface question: if `CA` is
model-dependent (`≍ |log γ|^{1-1/(4d)}`), then `Ccg` is model-dependent too, and
the lane's pinned
`recutPinnedCcgFlux` cannot receive it.  The frozen budget has room for it — the
whole `|log γ|` is spent on `GEOM` alone at present, and `GEOM ≤ 2|log γ|` is
generous — but a `CcgF: ABKModel d → ℝ` re-thread of
`RecutCoreSupplyFluxSupClause` / `RecutCoreSupplyFluxEnergySupGrad` (the only
two carriers that pin `Ccg`; everything downstream already carries it free) is
required first.  NOT attempted in this file.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The frozen conclusion, named -/

/-- **THE FROZEN `generator_renormalization` CONCLUSION.**

Byte-transcribed from the `FROZEN-STATEMENT` block of
`Algsuperdiff/Frozen/Section4/GeneratorRenormalization.lean` (which is NOT
imported), modulo this file's `open`s. -/
def GeneratorRenormalizationShape (d : ℕ) (cstar : ℝ) : Prop :=
  ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
    ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
        |sigmaBarM -
            Real.sqrt (M.nu ^ (2 : ℕ) +
              cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
          C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
        ∃ EB : Cutoff.CutoffSample d → ℝ,
          (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
          (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal
                  (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                    Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            ∀ L : ℤ, m ≤ L →
              ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u h g →
                IsDirichletSolutionOn
                    (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
                HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
                HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
                (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                    Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                      EB omega *
                        (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                  |volumeAverage (openCubeSet (originCube d m))
                        (fun y => M.nu * vecNormSq (u.grad y)) -
                      volumeAverage (openCubeSet (originCube d m))
                        (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
                    EB omega *
                      (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          Real.sqrt sigmaBarM *
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                        (2 : ℕ)

/-! ## 2. The ONE remaining input -/

/-- **THE ONE REMAINING INPUT.**  An a.e. producer of the sup-form multiscale
clause at SOME positive `γ₀`.  This is the target interface, and nothing
else stands between it and the frozen root. -/
def SupClauseProducerAt (d : ℕ) (cstar : ℝ) : Prop :=
  ∃ gamma0 : ℝ, 0 < gamma0 ∧
    ∀ (hd : 2 ≤ d) (inst : NeZero d),
      @SeamMultiscaleSupClauseSupply d inst (le_trans (by norm_num) hd) cstar gamma0

/-! ## 3. THE COMPOSITION -/

/-- **THE COMPOSITION.**  The frozen conclusion, at every dimension and
every `cstar > 0`, from the sup-form clause producer ALONE.  `C_gap` is pinned
to the numeral `1`; `C_en⁰`, `K_abs`, `C_top` and the geometric factor are
all closed terms pinned inside. -/
theorem generatorRenormalizationShape_of_supClauseProducer (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) (h : SupClauseProducerAt d cstar) :
    GeneratorRenormalizationShape d cstar := by
  obtain ⟨gamma0, hg0, hcl⟩ := h
  exact generator_renormalization_provider_final_of_supClause d cstar hcstar hg0
    one_pos hcl

/-- The same from the `ℓ^p` clause producer, through the regression
certificate `supClauseSupply_of_clauseSupply`. -/
theorem generatorRenormalizationShape_of_clauseProducer (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 : ℝ} (hg0 : 0 < gamma0)
    (hcl : ∀ (hd : 2 ≤ d) (inst : NeZero d),
      @SeamMultiscaleClauseSupply d inst (le_trans (by norm_num) hd) cstar gamma0) :
    GeneratorRenormalizationShape d cstar :=
  generatorRenormalizationShape_of_supClauseProducer d cstar hcstar
    ⟨gamma0, hg0, fun hd inst =>
      supClauseSupply_of_clauseSupply d (le_trans (by norm_num) hd) (hcl hd inst)⟩

end

end Algsuperdiff.Section4.Provider.Homogenization
