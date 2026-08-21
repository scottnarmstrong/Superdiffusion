/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineFinalWitness
import Algsuperdiff.Section4.Provider.Homogenization.HomFinitePSource
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineEndpoint
import Algsuperdiff.Section4.Provider.Homogenization.HomStepFourSchauder

/-!
# Theorem B, §4.5: THE SPINE — the frozen root's conclusion body

```text
  ∃ γ₀ C, 0 < γ₀ ∧ 0 < C ∧ ∀ M, c⋆(M) = c⋆ → γ ≤ γ₀ → ∀ m,
    ∃ σ̄_m, 0 < σ̄_m ∧ (C1) ∧
      ∃ E_B, (0 ≤ E_B) ∧ Measurable E_B ∧ (C2) ∧
        ∀ᵐ ω, ∀ L ≥ m, ∀ u v h g K_g K_h K_h^∞, (five binders) → (C3) ∧ (C4).
```

## What is DISCHARGED here, and what is supplied

* **(C1)** — the `σ̄_m` closeness display: supplied at the constant `C_flow`
  and re-based to the endpoint's own `C = C_wit + C_flow`.  This is Section 3's
  `diffusivity_asymptotics` (`Frozen/Section3/DiffusivityAsymptotics.lean`) read
  at `σ̄_m = Annealed.sigmaBar M m`; the endpoint is stated for an ARBITRARY
  `σ̄_m` satisfying it, so the Section-3 anchor plugs in unchanged, and so does
  the trivial witness `σ̄_m = √(ν² + c⋆γ⁻¹3^{2γm})` (for which the display holds
  at every `C ≥ 0`).  Nothing about `σ̄_m` is assumed beyond positivity and that
  one display.
* **(C2)** — DISCHARGED, from `HomSpineFinalWitness.exists_spine_defect_witness`:
  the real cut `E_B = K·(EthmB(m)).toReal`, its measurability, its moment at the
  root's own constant shape and `p`-range.  Its own single edge is `hY`.
* **(C3), (C4)** — supplied per `ω` by `HomSpineClauseSupplier`, at the
  `EthmB(m)`-domination interface: the producer exhibits a REAL defect `D` with
  `ofReal D ≤ EthmB(m)(ω)` (this is the manuscript's "comparing to the
  definition of `EthmB(m)`") and the two printed displays at `K·D`.
  The endpoint converts `K·D` into `E_B(ω)` through the witness's linkage —
  which is where the a.e. finiteness of the `[0,∞]` carrier is spent — and
  produces the root's clause bodies verbatim.

## The data-bracket nonnegativity, derived (not assumed)

The `stepFourEnergyEndpoint` carries `0 ≤ dataBracket …` as a binder.  Here it
is PROVED from the root's own five binders: `□_m` contains two distinct points
(`exists_ne_pair_openCubeSet`), so `HolderSeminormBoundOn.nonneg` gives `0 ≤
K_g` and `0 ≤ K_h`, and the sup binder at the cube centre gives `0 ≤ K_h^∞`.
No frame item is left on the data side.

## The conditional set of `homogenization_spine_endpoint`, itemized

1. `hY` — the Theorem-C minimal-scale exponential moment (`hC`), exactly the
   edge, at the abstract `[0,∞]` carrier.  See `HomSpineFinalWitness` for the
   blocked composition with the `homY_moment_bound_of_gamma_le` (a NAME
   COLLISION in the tree, reported there).
2. `hC1` — the `σ̄_m` closeness display (Section 3's own anchor, or the trivial
   witness).
3. `hclauses` — the per-`ω` clause supplier.  `HomSpineFinalStepFour`'s
   `exists_comparator_stepFourEnergy` produces its (C4) half from ONE `hCG'`
   application and the Schauder external; its (C3) half is the
   `ae_linfty_of_negBesovLp` at the same `hCG'`.  What is NOT bridged here is
   the comparator quantifier (`∃ v` produced by the Schauder package versus the
   root's `∀ v`) and the `hlevel`/`hS` arithmetic that consumes `hC`'s display;
   both are itemized in this file.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Two distinct points of an open cube -/

/-- An open triadic cube in dimension `d ≥ 1` contains two distinct points: its
centre and the centre shifted by half a radius in every coordinate.  This is all
that is needed to turn the root's Hölder binders into `0 ≤ K_g`, `0 ≤ K_h`. -/
theorem exists_ne_pair_openCubeSet [NeZero d] (Q : TriadicCube d) :
    ∃ x y : Vec d, x ∈ openCubeSet Q ∧ y ∈ openCubeSet Q ∧ x ≠ y := by
  have hr : 0 < cubeRadius Q := cubeRadius_pos Q
  have hi0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨cubeCenter Q, fun i => cubeCenter Q i + cubeRadius Q / 2, ?_, ?_, ?_⟩
  · rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self hr
  · rw [← ball_cubeCenter_eq_openCubeSet, Metric.mem_ball, dist_pi_lt_iff hr]
    intro i
    have hval : cubeCenter Q i + cubeRadius Q / 2 - cubeCenter Q i = cubeRadius Q / 2 := by
      ring
    rw [Real.dist_eq, hval, abs_of_pos (by linarith only [hr])]
    linarith only [hr]
  · intro hcon
    have h0 : cubeCenter Q ⟨0, hi0⟩ = cubeCenter Q ⟨0, hi0⟩ + cubeRadius Q / 2 :=
      congrFun hcon ⟨0, hi0⟩
    linarith only [hr, h0]

/-- The printed data bracket is nonnegative under the root's own five binders. -/
theorem dataBracket_nonneg_of_binders [NeZero d] {m : ℤ} {sigmaBarM Kg Kh KhInf : ℝ}
    {h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsig : 0 < sigmaBarM)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKh : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad)
    (hKhInf : ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) :
    0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hKh0 : 0 ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hKhInf0 : 0 ≤ KhInf := le_trans (norm_nonneg _) (hKhInf x0 hx0)
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have h1 : (0 : ℝ) ≤ sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hsig.le) hpow) hKg0
  have h2 : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) * Kh := mul_nonneg hpow hKh0
  rw [dataBracket]
  linarith only [h1, h2, hKhInf0]

/-! ## 2. The per-`ω` clause supplier -/

/-- **The two printed displays, at the `EthmB(m)`-domination interface.**

A producer of clauses (C3) and (C4) exhibits, for every admissible datum, a REAL
defect `D` dominated by the `[0,∞]`-valued carrier `EthmB(m)(ω)` and
the two displays at `K·D`.  This is exactly the shape the Step-3/Step-4
chain delivers: `HomStepThreeCoarse.ethmB_ge_first_summand` and
`HomStepEnvelope.ethmB_ge_gap` are the domination, and the two displays are
`HomFinitePConversion.ae_linfty_of_negBesovLp` and
`HomSpineFinalStepFour.exists_comparator_stepFourEnergy`. -/
def HomSpineClauseSupplier (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    (sigmaBarM Kabs : ℝ) (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      ∃ D : ℝ, 0 ≤ D ∧
        ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ∧
        (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            Kabs * D *
              dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        |volumeAverage (openCubeSet (originCube d m))
              (fun y => M.nu * vecNormSq (u.grad y)) -
            volumeAverage (openCubeSet (originCube d m))
              (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
          Kabs * D *
            energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ^ (2 : ℕ)

/-! ## 3. The spine endpoint -/

/-- **THE SPINE ENDPOINT — the frozen root's conclusion body.**

Every clause of the root is produced, in the root's own quantifier order and at
the root's own carriers.  (C2) is discharged from `hY`; (C1) is re-based from
`hC1`; (C3) and (C4) come from the per-`ω` supplier through the witness's
linkage.  The constant is `C = C_wit + C_flow` and the threshold is the
witness's own `γ₀`.

The remaining step is: discharge `hY` (the `homY_moment_bound_of_gamma_le`,
once the `homGamma0` name collision is resolved), `hC1` (Section 3's
`diffusivity_asymptotics`, or the trivial `σ̄_m`), and `hclauses` (the
Step-3/Step-4 chain off `hCG'`) — and the root is exact. -/
theorem homogenization_spine_endpoint (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar)
    {Cgate Cgap Kabs Cflow : ℝ} (hCgate : 0 < Cgate) (hCgap : 0 ≤ Cgap)
    (hKabs : 0 ≤ Kabs) (hCflow : 0 ≤ Cflow) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          (∀ p : ℝ, 1 ≤ p → p ≤ Cgate⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, Y omega ^ (2 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal 2 ^ (2 * p)) →
          ∀ hs : 0 < homS M, ∀ m : ℤ, ∀ sigmaBarM : ℝ, 0 < sigmaBarM →
            |sigmaBarM -
                Real.sqrt (M.nu ^ (2 : ℕ) +
                  cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
              Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM →
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplier M Cgap Y m hs sigmaBarM Kabs omega) →
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
  obtain ⟨g0, Cwit, hg0, hCwit, hwit⟩ :=
    exists_spine_defect_witness d cstar hcstar hCgate hCgap hKabs
  refine ⟨g0, Cwit + Cflow, hg0, by linarith only [hCwit, hCflow], ?_⟩
  intro M hcs hgamma Y hYm hY hs m sigmaBarM hsig hC1 hclauses
  obtain ⟨EB, hEB0, hEBm, hEBmom, hlink⟩ := hwit M hcs hgamma Y hYm hY hs m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  refine ⟨sigmaBarM, hsig, ?_, EB, hEB0, hEBm, ?_, ?_⟩
  · /- (C1), re-based at the endpoint's own consta -/
    have hT : (0 : ℝ) ≤ Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hsig.le
    refine hC1.trans ?_
    calc Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM
        = Cflow * (Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM) := by ring
      _ ≤ (Cwit + Cflow) * (Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCwit]) hT
      _ = (Cwit + Cflow) * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM := by ring
  · /- (C2), re-based at the endpoint's own consta -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hsub : p ≤ Cwit⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
      range_mono_of_le hCwit (by linarith only [hCflow]) hginv hLinv hrange
    refine (hEBmom p hp hsub).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by positivity
    calc Cwit * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          Real.log M.gamma ^ (2 : ℕ)
        = Cwit * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            Real.log M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ (Cwit + Cflow) * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCflow]) hT
      _ = (Cwit + Cflow) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by ring
  · /- (C3) and (C4), through the linka -/
    refine (hlink.and hclauses).mono ?_
    rintro omega ⟨hlk, hsupply⟩ L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
    obtain ⟨D, hD0, hDdom, hC3, hC4⟩ :=
      hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
    have hKD : Kabs * D ≤ EB omega := hlk D hD0 hDdom
    have hbr : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
    refine ⟨hC3.mono fun x hx => hx.trans ?_, hC4.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hKD hbr
    · exact mul_le_mul_of_nonneg_right hKD (sq_nonneg _)

end

end Algsuperdiff.Section4.Provider.Homogenization
