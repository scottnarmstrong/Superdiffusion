import Algsuperdiff.Section4.Support.Dirichlet
import Algsuperdiff.Section4.Support.ClassicalGradient
import Algsuperdiff.Section4.Support.ErrorAtoms
import Algsuperdiff.Section3.Disorder.Cstar
import Algsuperdiff.Section4.Provider.Regularity.RootProviderFinal

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-!
# Anomalous regularity — [ABK] Theorem C (`t.regularity`)

For a disorder model of strength `gamma` small enough, and every Hölder
exponent `alpha` below `1 - C sqrt gamma`, there is an almost surely finite
minimal scale `X` with an exponential tail such that, above `X`, every
Dirichlet solution on a triadic cube with `C^{0,1/2}` force `g` and
`C^{1,1/2}` boundary datum `h` satisfies the `C^{0,alpha}` large-scale
excess decay `3^{(1-alpha)(m-n)}` between any two scales `n <= m`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.anomalous_regularity
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
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Regularity.anomalous_regularity_provider_final
    d cstar _hcstar
