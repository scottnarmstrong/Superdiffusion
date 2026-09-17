import Algsuperdiff.Frozen.Introduction.AnomalousRegularity
import Algsuperdiff.Frozen.Introduction.GeneratorRenormalization
import Algsuperdiff.Frozen.Section5.SuperdiffusivityV2

/-!
# Main results

The three headline theorems of the formalization, stated here in full:
Theorems A, B and C of the paper *Superdiffusion and anomalous regularization
in self-similar random incompressible flows* (Armstrong--Bou-Rabee--Kuusi), in
their introduction-level forms.  Each theorem below restates
its certified counterpart verbatim and is proved by direct application, so the
statements displayed in this file are byte-faithful to the certified ones.

* `Algsuperdiff.superdiffusivity` -- Theorem A: quenched power-law
  superdiffusivity of the diffusion in the random flow.  At every positive time
  the quenched mean square displacement agrees with the square of the intrinsic
  length scale, and the quenched mean displacement is negligible beside it,
  in every moment over the disorder up to a large exponent.
* `Algsuperdiff.generator_renormalization` -- Theorem B: renormalization of
  the generator.  At every scale the Dirichlet problem for the random
  operator is comparable, in the uniform norm and in energy, to the
  homogenized problem with a scalar diffusivity, with a random error whose
  moments carry the cubed logarithm display.
* `Algsuperdiff.anomalous_regularity` -- Theorem C: anomalous large-scale
  regularity, a quantitative excess-decay estimate for solutions of the same
  Dirichlet problem, down to a random minimal scale with exponentially
  decaying tails.

All three reduce to the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## The coefficient field, and the statements with an infrared cutoff

Theorems B and C are stated here for the coefficient field `a = ν I + k` of
the model itself, read on the full sample of the disorder, in their
introduction-level forms.  The paper proves them first for the
infrared truncations `a_L` of that field, uniformly in the cutoff `L ≥ m`, and those
uniform statements are formalized as well and remain part of the public
surface, as `Algsuperdiff.Frozen.Section4.generator_renormalization` and
`Algsuperdiff.Frozen.Section4.anomalous_regularity`.  They are the more
general form; the two theorems below follow from them in the limit `L → ∞`,
and outside the law and the coefficient field the two forms share every token.

## The asymptotics of the effective diffusivity

The two-sided asymptotics of the effective diffusivity -- at every scale it
tracks the superdiffusive profile `(ν² + c⋆ γ⁻¹ 3^{2γm})^{1/2}` predicted by
the renormalization-group heuristic, with relative error of order
`√γ |log γ|` -- is the first display of Theorem B below, the comparison
between the effective diffusivity `σ̄_m` and that profile.  The quantitative
form proved in Section 3, which adds the two-sided bounds on `σ̄_m` at the top
scale of the induction, stays public as
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`.

## Non-vacuity

The sample space carrying each statement is inhabited, its law being a
probability measure.  The model clause is another matter: this development
constructs no `ABKModel d`, so each theorem is certified as an implication,
holding for every model that satisfies the paper's assumptions.  The paper's
Gaussian example is the construction that would exhibit such a model, and it
is not formalized here.
-/

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form
open Homogenization MeasureTheory
open scoped ENNReal NNReal

/-- **Theorem A (quenched superdiffusivity).**  For every model whose coupling
`γ` lies below a threshold, every time `t > 0` and every exponent `p` in the
range `p ≤ C⁻¹ γ⁻¹ |log γ|⁻⁶`, the annealed `p`-th moments of the deviation of
the quenched second moment of the displacement at time `t` from `2 d R̃(t)²`,
and of the squared quenched mean displacement, are bounded by
`(C (√p + √|log γ|) √γ |log γ|⁴ R̃(t)²)^p` and
`(C (p + |log γ|) γ |log γ|⁷ R̃(t)²)^p`
respectively, where `R̃(t)` is the intrinsic length scale of the paper
(`intrinsicScale`).  The displacement is read through the compactified
process, on which the retraction `onePointRetract` sends the added point to
the origin. -/
theorem Algsuperdiff.superdiffusivity
    (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t →
      ∀ p : ℝ, 1 ≤ p →
        p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d)))) -
                  2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p ∧
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (p + |Real.log M.gamma|) * M.gamma *
              |Real.log M.gamma| ^ (7 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p
    := Algsuperdiff.Frozen.Section5.superdiffusivity_v2 d cstar hcstar

/-- **Theorem B (renormalization of the generator).**  For every model whose
coupling `γ` lies below a threshold and every scale `m` there are an effective
diffusivity `σ̄_m > 0`, whose relative distance to
`(ν² + c⋆ γ⁻¹ 3^{2γm})^{1/2}` is at most `C √γ |log γ|`, and a nonnegative
random variable `E_B` on the sample of the coefficient field `a = ν I + k`,
whose `p`-th moments over the disorder are bounded by
`(C (√p + √|log γ|) √γ |log γ|³)^p` for every `p` in `[1, C⁻¹ γ⁻¹ |log γ|⁻¹]`,
such that almost surely the following holds for every choice of data at the
scale `m`.  If `u` solves the Dirichlet problem for `a` on the cube `□_m` with
force `g` and boundary datum `h`, and `v` solves the homogenized problem with
the constant coefficient `σ̄_m I` and the same data, then the rescaled uniform
difference `3^{-m} |u - v|` is at most `E_B` times
`σ̄_m⁻¹ 3^{m/2} [g] + (‖∇h‖_∞ + 3^{m/2} [∇h])`, and the two Dirichlet energies
`⨍ ν |∇u|²` and `⨍ σ̄_m |∇v|²` differ by at most `E_B` times the square of
`√(σ̄_m⁻¹) 3^{m/2} [g] + √(σ̄_m) (‖∇h‖_∞ + 3^{m/2} [∇h])`.  Here `[·]` is the
`1/2`-Hölder seminorm over the cube, for which the statement carries the
explicit bounds `Kg`, `Kh` and the sup-norm bound `KhInf`, and the uniform
estimate is read as an almost-everywhere bound on the cube.  A single
exceptional set serves the whole family of data; the moment bound on `E_B` is
the separate annealed clause. -/
theorem Algsuperdiff.generator_renormalization
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
          ∃ EB : Algsuperdiff.Section5.Field.FullSample d M.gamma → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure,
              ∀ (u v h : Homogenization.H1Function
                    (Homogenization.openCubeSet (Homogenization.originCube d m)))
                (g : Homogenization.Vec d → Homogenization.Vec d)
                (Kg Kh KhInf : ℝ),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
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
    := Algsuperdiff.Frozen.Introduction.generator_renormalization d cstar _hcstar

/-- **Theorem C (anomalous regularity).**  For every model whose coupling `γ`
lies below a threshold, every Hölder exponent `α` in `(0, 1 - C √γ]` and every
scale `m` there is a random minimal scale `X`, with values in `ℕ∞` and with
the exponentially decaying tail
`P[X ≥ N] ≤ C exp(-(1 - α)² (N - C) / (C γ))`, such that almost surely the
following excess decay holds for every choice of data at the scale `m`.  If
`u` solves the Dirichlet problem for the coefficient field `a = ν I + k` on
the cube `□_m` with force `g` and boundary datum `h`, then at every point `x`
of the cube and every scale `n ≤ m` with `X ≤ m - n`, the normalized energy
`√ν ‖∇u‖_{L̲²((x + □_n) ∩ □_m)}` is at most `C 3^{(1-α)(m-n)}` times the sum
of the same energy over the whole cube, of `√(σ̄_m⁻¹) 3^{m/2} [g]` and of
`√(σ̄_m) 3^{m/2} [∇h]`, the last term being present only when `x` lies outside
the smaller cube `□_{m-1}`; that indicator is read here as the conjunction of
the estimate with the term, valid at every `x`, and the estimate without it,
valid on `□_{m-1}`.  Here `[·]` is the `1/2`-Hölder seminorm over the cube,
for which the statement carries the explicit bounds `Kg` and `Kh`, the norms
are taken against the normalized volume measure of the set, and `σ̄_m` is the
annealed diffusivity that Theorem B produces, quoted here by name.  The decay
`3^{(1-α)(m-n)}` is the one a `C^{0,α}` function has, uniformly in the
molecular diffusivity `ν`. -/
theorem Algsuperdiff.anomalous_regularity
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Algsuperdiff.Section5.Field.FullSample d M.gamma → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure,
              ∀ (u h : Homogenization.H1Function
                    (Homogenization.openCubeSet (Homogenization.originCube d m)))
                (g : Homogenization.Vec d → Homogenization.Vec d)
                (Kg Kh : ℝ),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
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
    := Algsuperdiff.Frozen.Introduction.anomalous_regularity d cstar _hcstar
