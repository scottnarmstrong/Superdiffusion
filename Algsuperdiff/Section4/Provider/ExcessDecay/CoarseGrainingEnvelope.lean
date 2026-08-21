/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.CoarseGrainingP2

/-!
# The `s`-envelope of the coarse-graining right-hand side at the §4.3 slot

## The slot

ABK26's `e.homogenization.L2.interior` is `p.general.coarse.graining` read at
`p = 2` and `m = n` — i.e. at **depth `j = 0`** — with the manuscript exponents
`(s_prop, s_1, s_2) = (s/2, s/4, s)`.

CoarseGraining's package asks `r < s_prop / 2` where the printed proposition
asks only `s_1 < s_prop`.  Keeping the printed error index `s_1 = s/4` (the
index the `q = 1 ← q = 2` comparison converts into the good event's own `s/8`)
therefore forces the comparison exponent **above** the printed `s/2`.

```text
   s_prop := 3s/4 ,      r := s/4 ,      r₂ := s ,      j := 0 ,
```

which satisfies every CoarseGraining hypothesis on the whole anchor range `s ∈
(0,1]` (`3s/4 < 1` even at the endpoint `s = 1`), keeps the printed
`𝓔_{s/4,∞,1}`, and costs only the harmless factor `4/3` on the `s_prop^{-1}`
prefactor: the comparison exponent enters CoarseGraining's right-hand side
**only** through `s_prop⁻¹`.

## The honest envelope (reported, not hidden)

The `s`-powers proved below are

| term | printed  | proved here |
| --- | --- | --- |
| `𝓔 ·  ν^{1/2}‖∇u‖` | `C s^{-3/2}` | `(1024/3) s^{-4}` |
| forcing `[g]_{H̲^s}` | `C s^{-11/2}` | `(16384/3) s^{-6}` |

Both are *weaker* than the printed envelopes, so nothing here may be presented
as the printed display.  Two of the three forcing summands land on the printed
`s^{-11/2}` exactly; only the `|a₀| λ^{-1}_{r/2,2}` summand costs `s^{-6}`.

## The forcing bracket

The printed proposition writes the forcing prefactor as `(1 + 𝓔²_{s_1/2,∞,2})`;
CoarseGraining writes it through the coarse-grained ellipticity factors.  Both
are capped by `C(d)` on the good event `𝒢` — the first by
`e.good.set.giveth.v2`, the second by `e.bound.Lambdas.by.Es.v2` (the
`l.mathcal.E.to.Lambdas` leg proved in `LambdaCaps.lean`/`GoodEventCaps.lean`)
— so the two forms are interchangeable exactly where §4.3 uses them.
`coarseGrainingForceBracket` below is CoarseGraining's form, carried
explicitly.

## References

* ABK26, `p.general.coarse.graining`.
* ABK26, `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. The two development-facing right-hand terms -/

/-- The energy term of `e.homogenization.L2.interior`, at depth `0`:
`|a₀|^{1/2} 𝓔_{r,∞,1}(Q; a, a₀) ‖∇u‖_{a,L̲²(Q)}`.  For the ABK operator
`a_L = ν Id + κ_L` with `κ_L` antisymmetric, the coefficient-energy norm on the
right *is* `ν^{1/2}‖∇u‖_{L̲²}`, which is what the display prints. -/
def coarseGrainingEnergyTerm [NeZero d] (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) (r : ℝ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  Ch03.constantCoeffMatrixNormHalf a0 *
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 *
    Ch03.h1EnergyNormOnCube Q a u

/-- CoarseGraining's forcing bracket, the replacement for the printed `(1 +
𝓔²_{s_1/2,∞,2})`: it is built from the coarse-grained ellipticity factors
`λ^{-1/2}_{r/2,2}`, `Λ^{1/2}_{r/2,2}` and `λ^{-1}_{r/2,2}`. -/
def coarseGrainingForceBracket [NeZero d] (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) (r : ℝ) : ℝ :=
  Ch03.constantCoeffMatrixNormHalf a0 *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 +
    Ch03.poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) +
    Ch03.constantCoeffMatrixNorm a0 *
      Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ)

/-- The forcing term of `e.homogenization.L2.interior`, at depth `0`. -/
def coarseGrainingForceTerm [NeZero d] (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) (r r₂ : ℝ) (g : Vec d → Vec d) : ℝ :=
  coarseGrainingForceBracket Q a a0 r *
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g

/-! ## 2. Nonnegativity -/

theorem matrixNorm_nonneg (A : Mat d) : 0 ≤ Ch02.matrixNorm A := by
  rw [Ch02.matrixNorm]
  exact norm_nonneg _

theorem constantCoeffMatrixNormHalf_nonneg (a0 : Ch03.ConstantCoeffMatrix d) :
    0 ≤ Ch03.constantCoeffMatrixNormHalf a0 := by
  rw [Ch03.constantCoeffMatrixNormHalf]
  exact Real.rpow_nonneg (matrixNorm_nonneg a0.matrix) _

theorem constantCoeffMatrixNorm_nonneg (a0 : Ch03.ConstantCoeffMatrix d) :
    0 ≤ Ch03.constantCoeffMatrixNorm a0 :=
  matrixNorm_nonneg a0.matrix

theorem h1EnergyNormOnCube_nonneg (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ Ch03.h1EnergyNormOnCube Q a u := by
  rw [Ch03.h1EnergyNormOnCube]
  exact Real.sqrt_nonneg _

/-- Nonnegativity of the coarse-graining homogenization error at depth `j`. -/
theorem coarseGrainingHomogenizationErrorAtDepth_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r : ℝ} (hr : 0 < r)
    (j : ℕ) :
    0 ≤ Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r j := by
  rw [Ch03.coarseGrainingHomogenizationErrorAtDepth]
  exact Ch02.finsetSupReal_nonneg (descendantsAtDepth Q j) _
    fun R _hR => Ch02.HomogenizationErrorOnCube_infinity_one_nonneg R a a0.matrix hr

theorem poincareLowerEllipticityFactor_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) {t : ℝ} (ht : 0 < t) :
    0 ≤ Ch03.poincareLowerEllipticityFactor Q a t (.finite 2) := by
  rw [Ch03.poincareLowerEllipticityFactor]
  exact Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a ht (by norm_num)).le _

theorem poincareUpperEllipticityFactor_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) {t : ℝ} (ht : 0 < t) :
    0 ≤ Ch03.poincareUpperEllipticityFactor Q a t (.finite 2) := by
  rw [Ch03.poincareUpperEllipticityFactor]
  exact Real.rpow_nonneg (Ch02.LambdaSq_finite_pos Q a ht (by norm_num)).le _

theorem coarseGrainingEnergyTerm_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ coarseGrainingEnergyTerm Q a a0 r u :=
  mul_nonneg (mul_nonneg (constantCoeffMatrixNormHalf_nonneg a0)
    (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 hr 0))
    (h1EnergyNormOnCube_nonneg Q a u)

theorem coarseGrainingForceBracket_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r : ℝ} (hr : 0 < r) :
    0 ≤ coarseGrainingForceBracket Q a a0 r := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith only [hr]
  have h1 : 0 ≤ Ch03.constantCoeffMatrixNormHalf a0 *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 :=
    mul_nonneg (mul_nonneg (constantCoeffMatrixNormHalf_nonneg a0)
      (poincareLowerEllipticityFactor_nonneg Q a hr2))
      (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 hr 0)
  have h2 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) :=
    mul_nonneg (poincareUpperEllipticityFactor_nonneg Q a hr2)
      (poincareLowerEllipticityFactor_nonneg Q a hr2)
  have h3 : 0 ≤ Ch03.constantCoeffMatrixNorm a0 *
      Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ) :=
    mul_nonneg (constantCoeffMatrixNorm_nonneg a0)
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a hr2 (by norm_num)).le _)
  rw [coarseGrainingForceBracket]
  linarith only [h1, h2, h3]

/-! ## 3. Depth-zero weights -/

theorem coarseGrainingDepthWeight_zero (r : ℝ) : Ch03.coarseGrainingDepthWeight r 0 = 1 := by
  rw [Ch03.coarseGrainingDepthWeight]
  norm_num

theorem coarseGrainingDepthHalfWeight_zero (r : ℝ) :
    Ch03.coarseGrainingDepthHalfWeight r 0 = 1 := by
  rw [Ch03.coarseGrainingDepthHalfWeight]
  norm_num

theorem coarseGrainingDepthInvWeight_zero (r : ℝ) :
    Ch03.coarseGrainingDepthInvWeight r 0 = 1 := by
  rw [Ch03.coarseGrainingDepthInvWeight, coarseGrainingDepthWeight_zero, inv_one]

/-! ## 4. The depth-zero right-hand side, unpacked -/

/-- CoarseGraining's right-hand side at depth `0`, with its three forcing summands
displayed and their individual `r`-powers intact. -/
theorem generalCoarseGrainingL2TwoExponentRHS_depth_zero_eq [NeZero d]
    (Q : TriadicCube d) (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d)
    (t r r₂ : ℝ) (g : Vec d → Vec d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    Ch03.generalCoarseGrainingL2TwoExponentRHS 1 Q a a0 t r r₂ 0 g u =
      t⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
        (r⁻¹ * coarseGrainingEnergyTerm Q a a0 r u +
          (Real.rpow r (-(5 / 2 : ℝ)) *
                (Ch03.constantCoeffMatrixNormHalf a0 *
                  Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
                  Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0) +
              Real.rpow r (-(5 / 2 : ℝ)) *
                (Ch03.poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
                  Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2)) +
              Real.rpow r (-3 : ℝ) *
                (Ch03.constantCoeffMatrixNorm a0 *
                  Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ))) *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g) := by
  rw [Ch03.generalCoarseGrainingL2TwoExponentRHS,
    Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS,
    coarseGrainingDepthWeight_zero, coarseGrainingDepthHalfWeight_zero,
    coarseGrainingDepthInvWeight_zero, coarseGrainingEnergyTerm]
  ring

/-! ## 5. The `s`-envelope at the §4.3 slot -/

/-- `r^{-3} = (r⁻¹)³` for positive `r`. -/
private theorem rpow_neg_three_eq (r : ℝ) (hr : 0 < r) :
    Real.rpow r (-3 : ℝ) = (r⁻¹) ^ (3 : ℕ) := by
  rw [Real.rpow_eq_pow, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hr.le, Real.rpow_natCast, ← inv_pow]

/-- **The §4.3 slot envelope.**

At `(s_prop, r, r₂, j) = (3s/4, s/4, s, 0)` and `0 < s ≤ 1`,

```text
  RHS₁ ≤ (1024/3) s^{-4} · |a₀|^{1/2} 𝓔_{s/4,∞,1}(Q) ‖∇u‖_a
       + (16384/3) s^{-6} · (CoarseGraining forcing bracket) · [g]_{H̲^s(Q)} .
```

Every constant is explicit and dimension-free; the two `s`-powers are the
honest ones (see the table in the module docstring). -/
theorem generalCoarseGrainingL2TwoExponentRHS_slot_le [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) {g : Vec d → Vec d} (hg : Ch03.ForceBesovRegularity Q s g)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    Ch03.generalCoarseGrainingL2TwoExponentRHS 1 Q a a0 (3 * s / 4) (s / 4) s 0 g u ≤
      (1024 / 3) * (s⁻¹) ^ (4 : ℕ) * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
        (16384 / 3) * (s⁻¹) ^ (6 : ℕ) * coarseGrainingForceTerm Q a a0 (s / 4) s g := by
  have hr : (0 : ℝ) < s / 4 := by linarith only [hs]
  have hr1 : s / 4 ≤ 1 := by linarith only [hs1]
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
  have hrinv : (s / 4)⁻¹ = 4 * s⁻¹ := by
    field_simp
  have hG : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg
  have hET : 0 ≤ coarseGrainingEnergyTerm Q a a0 (s / 4) u :=
    coarseGrainingEnergyTerm_nonneg Q a a0 hr u
  have hBR : 0 ≤ coarseGrainingForceBracket Q a a0 (s / 4) :=
    coarseGrainingForceBracket_nonneg Q a a0 hr
  -- the three forcing summands
  have hr2 : (0 : ℝ) < s / 4 / 2 := by linarith only [hr]
  have hB1 : 0 ≤ Ch03.constantCoeffMatrixNormHalf a0 *
      Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 (s / 4) 0 :=
    mul_nonneg (mul_nonneg (constantCoeffMatrixNormHalf_nonneg a0)
      (poincareLowerEllipticityFactor_nonneg Q a hr2))
      (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 hr 0)
  have hB2 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2) :=
    mul_nonneg (poincareUpperEllipticityFactor_nonneg Q a hr2)
      (poincareLowerEllipticityFactor_nonneg Q a hr2)
  have hB3 : 0 ≤ Ch03.constantCoeffMatrixNorm a0 *
      Real.rpow (Ch02.lambdaSq Q (s / 4 / 2) (.finite 2) a) (-1 : ℝ) :=
    mul_nonneg (constantCoeffMatrixNorm_nonneg a0)
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a hr2 (by norm_num)).le _)
  -- the uniform `r`-power on the forcing side
  have hpow : Real.rpow (s / 4) (-(5 / 2 : ℝ)) ≤ 64 * (s⁻¹) ^ (3 : ℕ) := by
    have hmono : Real.rpow (s / 4) (-(5 / 2 : ℝ)) ≤ Real.rpow (s / 4) (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
    have heq : Real.rpow (s / 4) (-3 : ℝ) = 64 * (s⁻¹) ^ (3 : ℕ) := by
      rw [rpow_neg_three_eq _ hr, hrinv]
      ring
    linarith only [hmono, heq.le, heq.ge]
  have hpow3 : Real.rpow (s / 4) (-3 : ℝ) = 64 * (s⁻¹) ^ (3 : ℕ) := by
    rw [rpow_neg_three_eq _ hr, hrinv]
    ring
  -- the forcing bracket, with its powers replaced by the uniform one
  have hbracket : Real.rpow (s / 4) (-(5 / 2 : ℝ)) *
        (Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 (s / 4) 0) +
        Real.rpow (s / 4) (-(5 / 2 : ℝ)) *
          (Ch03.poincareUpperEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
            Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2)) +
        Real.rpow (s / 4) (-3 : ℝ) *
          (Ch03.constantCoeffMatrixNorm a0 *
            Real.rpow (Ch02.lambdaSq Q (s / 4 / 2) (.finite 2) a) (-1 : ℝ)) ≤
      64 * (s⁻¹) ^ (3 : ℕ) * coarseGrainingForceBracket Q a a0 (s / 4) := by
    have e1 := mul_le_mul_of_nonneg_right hpow hB1
    have e2 := mul_le_mul_of_nonneg_right hpow hB2
    have e3 := mul_le_mul_of_nonneg_right hpow3.le hB3
    rw [coarseGrainingForceBracket]
    linarith only [e1, e2, e3]
  -- the scalar prefactor
  have hP : (3 * s / 4)⁻¹ * ((s / 4)⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - s / 4)⁻¹ ≤
      (256 / 3) * (s⁻¹) ^ (3 : ℕ) := by
    have hq : (0 : ℝ) < (1 / 2 : ℝ) - s / 4 := by linarith only [hs1]
    have hqle : ((1 / 2 : ℝ) - s / 4)⁻¹ ≤ 4 := by
      have hge : (1 : ℝ) / 4 ≤ (1 / 2 : ℝ) - s / 4 := by linarith only [hs1]
      have h := inv_anti₀ (show (0 : ℝ) < 1 / 4 by norm_num) hge
      rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h
      exact h
    have hfac : (3 * s / 4)⁻¹ * ((s / 4)⁻¹) ^ (2 : ℕ) = (64 / 3) * (s⁻¹) ^ (3 : ℕ) := by
      rw [hrinv]
      field_simp
      ring
    rw [hfac]
    have hpos : (0 : ℝ) < (64 / 3) * (s⁻¹) ^ (3 : ℕ) := by positivity
    have := mul_le_mul_of_nonneg_left hqle hpos.le
    linarith only [this]
  -- assembly
  rw [generalCoarseGrainingL2TwoExponentRHS_depth_zero_eq]
  set B : ℝ := Real.rpow (s / 4) (-(5 / 2 : ℝ)) *
        (Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 (s / 4) 0) +
        Real.rpow (s / 4) (-(5 / 2 : ℝ)) *
          (Ch03.poincareUpperEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
            Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2)) +
        Real.rpow (s / 4) (-3 : ℝ) *
          (Ch03.constantCoeffMatrixNorm a0 *
            Real.rpow (Ch02.lambdaSq Q (s / 4 / 2) (.finite 2) a) (-1 : ℝ)) with hBdef
  have hBnonneg : 0 ≤ B := by
    have e1 : 0 ≤ Real.rpow (s / 4) (-(5 / 2 : ℝ)) *
        (Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 (s / 4) 0) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) hB1
    have e2 : 0 ≤ Real.rpow (s / 4) (-(5 / 2 : ℝ)) *
        (Ch03.poincareUpperEllipticityFactor Q a (s / 4 / 2) (.finite 2) *
          Ch03.poincareLowerEllipticityFactor Q a (s / 4 / 2) (.finite 2)) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) hB2
    have e3 : 0 ≤ Real.rpow (s / 4) (-3 : ℝ) *
        (Ch03.constantCoeffMatrixNorm a0 *
          Real.rpow (Ch02.lambdaSq Q (s / 4 / 2) (.finite 2) a) (-1 : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) hB3
    rw [hBdef]
    linarith only [e1, e2, e3]
  have hinner : (s / 4)⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u + B *
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤
      4 * s⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
        64 * (s⁻¹) ^ (3 : ℕ) * coarseGrainingForceTerm Q a a0 (s / 4) s g := by
    have hb := mul_le_mul_of_nonneg_right hbracket hG
    rw [coarseGrainingForceTerm, hrinv]
    linarith only [hb]
  have hinner_nonneg : 0 ≤ (s / 4)⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u + B *
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
    add_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) hET) (mul_nonneg hBnonneg hG)
  have hupper_nonneg : 0 ≤ 4 * s⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
      64 * (s⁻¹) ^ (3 : ℕ) * coarseGrainingForceTerm Q a a0 (s / 4) s g := by
    rw [coarseGrainingForceTerm]
    have e1 : 0 ≤ 4 * s⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u := by positivity
    have e2 : 0 ≤ 64 * (s⁻¹) ^ (3 : ℕ) *
        (coarseGrainingForceBracket Q a a0 (s / 4) *
          Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by positivity
    linarith only [e1, e2]
  calc (3 * s / 4)⁻¹ * ((s / 4)⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - s / 4)⁻¹ *
        ((s / 4)⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
          B * Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g)
      ≤ (256 / 3) * (s⁻¹) ^ (3 : ℕ) *
          ((s / 4)⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
            B * Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) :=
        mul_le_mul_of_nonneg_right hP hinner_nonneg
    _ ≤ (256 / 3) * (s⁻¹) ^ (3 : ℕ) *
          (4 * s⁻¹ * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
            64 * (s⁻¹) ^ (3 : ℕ) * coarseGrainingForceTerm Q a a0 (s / 4) s g) := by
        refine mul_le_mul_of_nonneg_left hinner ?_
        positivity
    _ = (1024 / 3) * (s⁻¹) ^ (4 : ℕ) * coarseGrainingEnergyTerm Q a a0 (s / 4) u +
          (16384 / 3) * (s⁻¹) ^ (6 : ℕ) * coarseGrainingForceTerm Q a a0 (s / 4) s g := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
