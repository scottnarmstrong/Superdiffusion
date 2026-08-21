import Algsuperdiff.Frozen.Section3.DiffusivityAsymptotics
import Algsuperdiff.Frozen.Section4.AnomalousRegularity
import Algsuperdiff.Frozen.Section4.GeneratorRenormalization

/-!
# Main results

The headline theorems of the formalization, stated here in full: Theorems B
and C of the paper *Superdiffusion and anomalous regularization in
self-similar random incompressible flows* (Armstrong--Bou-Rabee--Kuusi),
together with the effective-diffusivity asymptotics, the quantitative core of
the paper's Section 3.  (Theorem A of the paper's introduction concerns the
diffusion process itself and is not yet formalized: the theory of diffusion
processes is not yet developed in Mathlib.)  Each theorem below restates its
certified counterpart verbatim and is proved by direct application, so the
statements displayed in this file are byte-faithful to the certified ones.

* `Algsuperdiff.diffusivity_asymptotics` -- the two-sided asymptotics of the
  effective diffusivity: at every scale it tracks the superdiffusive profile
  predicted by the renormalization-group heuristic, with relative error of
  order the square root of the coupling times a logarithm.
* `Algsuperdiff.generator_renormalization` -- Theorem B: renormalization of
  the generator.  At every scale the Dirichlet problem for the random
  operator is comparable, in the uniform norm and in energy, to the
  homogenized problem, with a random error whose moments carry the cubed
  logarithm display.
* `Algsuperdiff.anomalous_regularity` -- Theorem C: anomalous large-scale
  regularity, a quantitative excess-decay estimate down to a random minimal
  scale with stretched-exponential tails.

All three reduce to the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-- **The effective-diffusivity asymptotics.**  The renormalized diffusivity
is comparable, at every scale, to the superdiffusive profile, with a small
relative error; this is the quantitative superdiffusivity of the model. -/
theorem Algsuperdiff.diffusivity_asymptotics
    (d : ℕ) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
    := Algsuperdiff.Frozen.Section3.diffusivity_asymptotics d

/-- **Theorem B (renormalization of the generator).**  For every scale there
are a deterministic coefficient and a random error, with the stated moment
bound, such that almost surely the solution of the random Dirichlet problem
and the solution of the homogenized problem with the same data are comparable
in the uniform norm, and their Dirichlet energies agree, up to the error
times the natural norms of the data. -/
theorem Algsuperdiff.generator_renormalization
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
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
                ∀ (u v h : Homogenization.H1Function
                      (Homogenization.openCubeSet (Homogenization.originCube d m)))
                  (g : Homogenization.Vec d → Homogenization.Vec d)
                  (Kg Kh KhInf : ℝ),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (Homogenization.originCube d m) u h g →
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (fun _ : Homogenization.Vec d => sigmaBarM • (1 : Homogenization.Mat d))
                      (Homogenization.originCube d m) v h g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kg g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d m),
                    ‖h.grad x‖ ≤ KhInf) →
                  Algsuperdiff.Section4.Support.HasGradientOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      h.toFun h.grad →
                  (∀ᵐ x ∂(MeasureTheory.volume.restrict
                        (Homogenization.openCubeSet (Homogenization.originCube d m))),
                      Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                        EB omega *
                          (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    |Homogenization.volumeAverage
                          (Homogenization.openCubeSet (Homogenization.originCube d m))
                          (fun y => M.nu * Homogenization.vecNormSq (u.grad y)) -
                        Homogenization.volumeAverage
                          (Homogenization.openCubeSet (Homogenization.originCube d m))
                          (fun y => sigmaBarM * Homogenization.vecNormSq (v.grad y))| ≤
                      EB omega *
                        (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            Real.sqrt sigmaBarM *
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                          (2 : ℕ)
    := Algsuperdiff.Frozen.Section4.generator_renormalization d cstar _hcstar

/-- **Theorem C (anomalous regularity).**  There is a random minimal scale
with stretched-exponential tails below which solutions of the random
Dirichlet problem satisfy the excess-decay estimate, uniformly over the
stated boundary-data classes. -/
theorem Algsuperdiff.anomalous_regularity
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ, m ≤ L →
                ∀ (u h : Homogenization.H1Function
                      (Homogenization.openCubeSet (Homogenization.originCube d m)))
                  (g : Homogenization.Vec d → Homogenization.Vec d)
                  (Kg Kh : ℝ),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (Homogenization.originCube d m) u h g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kg g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ y ∈ Homogenization.openCubeSet (Homogenization.originCube d m),
                    ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                  Algsuperdiff.Section4.Support.HasGradientOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      h.toFun h.grad →
                  ∀ x : Homogenization.Vec d,
                    x ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
                    ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                      (ENNReal.ofReal (Real.sqrt M.nu) *
                          MeasureTheory.eLpNorm
                            (fun y => Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) ''
                                  Homogenization.openCubeSet (Homogenization.originCube d n)) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m))) ≤
                        ENNReal.ofReal
                            (C *
                              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              MeasureTheory.eLpNorm
                                (fun y =>
                                  Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                                (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                  (Homogenization.openCubeSet
                                    (Homogenization.originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                      (x ∈ Homogenization.openCubeSet (Homogenization.originCube d (m - 1)) →
                        ENNReal.ofReal (Real.sqrt M.nu) *
                            MeasureTheory.eLpNorm
                              (fun y => Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                (((fun y => x + y) ''
                                    Homogenization.openCubeSet
                                      (Homogenization.originCube d n)) ∩
                                  Homogenization.openCubeSet (Homogenization.originCube d m))) ≤
                          ENNReal.ofReal
                              (C *
                                Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            (ENNReal.ofReal (Real.sqrt M.nu) *
                                MeasureTheory.eLpNorm
                                  (fun y =>
                                    Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (Homogenization.openCubeSet
                                      (Homogenization.originCube d m))) +
                              ENNReal.ofReal
                                (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))
    := Algsuperdiff.Frozen.Section4.anomalous_regularity d cstar _hcstar
