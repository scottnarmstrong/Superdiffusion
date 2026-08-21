/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineMultiscaleClause
import Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeAssembly
import Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierRHS

/-!
# The multiscale clause from ONE gauge inequality

## What this file does

`HomSpineMultiscaleClause` reduced clause 1 of `HomFinitePSource`'s transcribed
source hypothesis to `CzFluxMultiscale`, i.e. to the Calderón--Zygmund flux
comparison lemma read at the multiscale grid gauge.  This file discharges that
reduction down to a SINGLE inequality of pure fractional-Sobolev type, with no
PDE content and no carrier of this repository in it:

```text
  [F]_{B̲^{-s}_{p,p}(Q)}  ≤  C(p,d) · ‖F‖_{Ŵ̲^{-s,p}(Q)}          (★)
```

— the CONVERSE of `CoarseGraining`'s proved
`cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`
(`EuclideanWspSmoothDualBesovBound`), on the range `s·p' < 1` where `p' =
p/(p-1)` is the conjugate exponent.  `(★)` is carried here as the named
hypothesis `NegativeBesovGridSmoothDualConverse`; it is the ONLY thing this
file assumes, and it is not proved in this repository, in `CoarseGraining`, or
in Mathlib (grep-verified by this file).

Everything else is discharged:

* the CZ step at the smooth-dual reading is `CoarseGraining`'s proved
  `exists_centeredCubeFluxComparison_cz` (the print's the Calderón--Zygmund flux comparison lemma
  verbatim at that reading);
* the descendant transfer is
  `HomCGDischargeBridge.localFluxDefect_smoothDualAverage_le` (`CoarseGraining`'s line-449
  comparison applied cubewise and lifted through the `ℓ^p` descendant average);
* the coarse-graining half is `CoarseGraining`'s unconditional `exists_localCoarseGrainingLp`;
* the whole smooth-dual composition is already assembled as
  `HomCGDischargeAssembly.exists_printedCoarseGrainingFiniteP_smoothDual`;
* this development-carrier identification (`§2` below) is proved here.

## The carrier identification (`§2`)

`HomFinitePGauge.negBesovLpPartialNorm Q s p N F` is the printed grid gauge
`3^{-ms}[F]_{B̲^{-s}_{p,p}(□_m)}` truncated at depth `N`, built on the
Euclidean magnitude of the cell averages.  `CoarseGraining`'s
`cubeEuclideanNegativeBesovESeminorm` is the same lattice sum without the
`3^{-ms}` normalization and with the *sup* magnitude of the cell averages.
Hence

```text
  negBesovLpPartialNorm Q s p N F  ≤  √d · 3^{-s·Q.scale} · [F]_{B̲^{-s}_{p,p}(Q)}
```

(`ofReal_negBesovLpPartialNorm_le`): a partial sum against a `tsum`, a depth
reindexing (`descendantsAtScale_eq_descendantsAtDepth`), and the Euclidean/sup
comparison `√(Σ xᵢ²) ≤ √d · sup|xᵢ|`.  No constant beyond `√d` is spent.

## The products

* `czFluxMultiscale_of_gridConverse` — `CzFluxMultiscale` at a genuine `C(p,d)`,
  i.e. the exact input
  `HomSpineMultiscaleClause.exists_coarseGrainingFinitePMultiscale_of_cz`
  consumes, produced from `(★)` plus the print's own Dirichlet-pair data;
* `exists_coarseGrainingFinitePMultiscale_of_gridConverse` — the clause itself,
  produced from `(★)` and the printed hypotheses only;
* `negativeBesovGridSmoothDualConverse_of_testFamily` (`§6`) — `(★)` itself from
  a bare CONSTRUCTION of dual test fields, and
  `exists_coarseGrainingFinitePMultiscale_of_testFamily`, the clause from that
  construction alone.

## The smoothness question, CLOSED (`§6`)

The grid gauge's own dual tests are multi-depth grid-piecewise constants, which
are not `C^∞`; the natural worry is that `CoarseGraining`'s smooth-dual carrier
does not see them.  It does.  `CoarseGraining` proves, unconditionally,

```text
  ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le:
    |⟨F, G⟩|  ≤  ‖F‖_{Ŵ̲^{-s,p}(Q)} · ‖G‖_{W̲^{s,p'}(Q)}
```

for EVERY `G ∈ W̲^{s,p'}(Q) ∩ L²(Q)` (`EuclideanWspSmoothDualFieldPairing`; the
mechanism is the completed-graph extension of
`EuclideanWspCompletedDualExtension`, built on the smooth density theorem
`exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt`).  So `(★)` carries
no smoothness obligation whatsoever, and `GridDualTestFamily` — the existence of
normalized `W̲^{s,p'} ∩ L²` tests that see the truncated grid mass — is the
exact and only remaining analytic content of the multiscale clause.

## The one narrowing, disclosed

Both statements carry the gate `s·p' < 1` of `(★)`.  It is not a restriction at
the consumer: `gate_of_le_quarter` shows that `s ≤ 1/4` and `2 ≤ p` suffice, and
the Step-3 pin is exactly `s = |log γ|⁻¹ ≤ 1/4` at `p = 4d`.
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The Euclidean magnitude against the carrier's sup norm -/

/-- **`√(Σ xᵢ²) ≤ √d · sup|xᵢ|`.**  `Vec d` carries the product (sup) norm; the
gauge of this repository is built on the Euclidean magnitude.  This is the only constant
the identification of the two gauges costs. -/
theorem sqrt_vecNormSq_le_sqrt_dim_mul_norm (x : Vec d) :
    Real.sqrt (vecNormSq x) ≤ Real.sqrt d * ‖x‖ := by
  have hb : ∀ i : Fin d, x i * x i ≤ ‖x‖ * ‖x‖ := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    have h2 := mul_self_le_mul_self (abs_nonneg (x i)) h1
    rwa [abs_mul_abs_self] at h2
  have hsum : vecNormSq x ≤ (d : ℝ) * (‖x‖ * ‖x‖) := by
    have hrw : vecNormSq x = ∑ i : Fin d, x i * x i := rfl
    rw [hrw]
    calc ∑ i : Fin d, x i * x i ≤ ∑ _i : Fin d, ‖x‖ * ‖x‖ :=
          Finset.sum_le_sum fun i _ => hb i
      _ = (d : ℝ) * (‖x‖ * ‖x‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq x) ≤ Real.sqrt ((d : ℝ) * (‖x‖ * ‖x‖)) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg x)]

/-! ## 2. This repository's gauge against `CoarseGraining`'s grid seminorm -/

/-- The scale factor relating the two gauges: `√d · 3^{-s·m}`. -/
def gridScaleGauge (d : ℕ) (s : ℝ) (m : ℤ) : ℝ :=
  Real.sqrt d * (3 : ℝ) ^ (-s * (m : ℝ))

theorem gridScaleGauge_nonneg (d : ℕ) (s : ℝ) (m : ℤ) : 0 ≤ gridScaleGauge d s m :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)

/-- `CoarseGraining`'s `Real.rpow`-spelling of the base-`3` power, in the
 notation used here. -/
theorem real_rpow_three_eq (x : ℝ) : Real.rpow 3 x = (3 : ℝ) ^ x := rfl

/-- Every depth term of this development gauge is nonnegative. -/
theorem negBesovLpDepthSeminorm_rpow_nonneg (Q : TriadicCube d) (s t : ℝ)
    (G : Vec d → Vec d) (j : ℕ) : (0 : ℝ) ≤ negBesovLpDepthSeminorm Q s t G j ^ t :=
  Real.rpow_nonneg (negBesovLpDepthSeminorm_nonneg Q s t G j) t

/-- The depth-`j` term of this development gauge against the depth-`j` term of `CoarseGraining`'s
running-scale negative Besov seminorm. -/
theorem ofReal_negBesovLpDepthSeminorm_rpow_le (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^ p.exponent.toReal) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
  classical
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hD
  have hDcard : (0 : ℝ) < (D.card : ℝ) := descendantsAtDepth_card_pos Q j
  set M : ℝ := descendantsAverage Q j
      (fun R => Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal) with hM
  have hMnn : 0 ≤ M :=
    descendantsAverage_nonneg Q j _ fun R _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  set S : ℝ≥0∞ := ∑ R ∈ D,
    (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal with hS
  /- the depth seminorm, in closed fo -/
  have hLHS : negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^ p.exponent.toReal
      = (3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ)) * M := by
    rw [negBesovLpDepthSeminorm_def, negBesovLpDepthMean_def,
      Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hMnn _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_mul hMnn,
      one_div, inv_mul_cancel₀ (ne_of_gt ht), Real.rpow_one]
    congr 2
    ring
  /- the Euclidean/sup comparison, averag -/
  have hMbound : ENNReal.ofReal M ≤
      ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) * ((D.card : ℝ≥0∞)⁻¹ * S) := by
    have hMeq : M = ((D.card : ℝ)⁻¹) *
        ∑ R ∈ D, Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal := rfl
    have hcard : ENNReal.ofReal ((D.card : ℝ)⁻¹) = ((D.card : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hDcard, ENNReal.ofReal_natCast]
    rw [hMeq, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hDcard)),
      ENNReal.ofReal_sum_of_nonneg
        (fun R _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p.exponent.toReal),
      hcard, ← mul_assoc,
      mul_comm (ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal)) ((D.card : ℝ≥0∞))⁻¹,
      mul_assoc]
    refine mul_le_mul' le_rfl ?_
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun R _ => ?_
    have hpt : Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal ≤
        Real.sqrt d ^ p.exponent.toReal *
          ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal := by
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)]
      exact Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (sqrt_vecNormSq_le_sqrt_dim_mul_norm _) ht.le
    calc ENNReal.ofReal
          (Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal)
        ≤ ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal *
            ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal) := ENNReal.ofReal_le_ofReal hpt
      _ = ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) *
            (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg _) _),
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht.le]
  /- `CoarseGraining`'s depth term, flattened and reindex -/
  have hscale : descendantsAtScale Q (Q.scale - (j : ℤ)) = D := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q (by omega : Q.scale - (j : ℤ) ≤ Q.scale)]
    congr 1
    omega
  have hexp : Real.rpow 3 (s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ))) =
      (3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ))) := by
    show (3 : ℝ) ^ (s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ))) = _
    congr 1
    push_cast
    ring
  have hEnergy : cubeEuclideanNegativeBesovDepthEnergy Q s p F j =
      ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)))) *
        ((D.card : ℝ≥0∞))⁻¹ * S := by
    rw [cubeEuclideanNegativeBesovDepthEnergy,
      Finset.sum_attach (descendantsAtScale Q (Q.scale - (j : ℤ)))
        (fun R => (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal),
      hscale, ← hS, hexp]
  /- the coefficient identi -/
  have hcoeff : ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) *
      ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) =
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)))) := by
    have hR : gridScaleGauge d s.1 Q.scale ^ p.exponent.toReal *
        (3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ))) =
        Real.sqrt d ^ p.exponent.toReal *
          (3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ)) := by
      have hsum : -s.1 * (Q.scale : ℝ) * p.exponent.toReal +
          s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)) =
          -s.1 * p.exponent.toReal * (j : ℝ) := by ring
      rw [gridScaleGauge,
        Real.mul_rpow (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hsum]
    rw [ENNReal.ofReal_rpow_of_nonneg (gridScaleGauge_nonneg d s.1 Q.scale) ht.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (gridScaleGauge_nonneg d s.1 Q.scale) p.exponent.toReal),
      hR, mul_comm (Real.sqrt d ^ p.exponent.toReal)]
  /- assemb -/
  rw [hLHS, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hEnergy]
  calc ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) * ENNReal.ofReal M
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) *
          (ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) * ((D.card : ℝ≥0∞)⁻¹ * S)) :=
        mul_le_mul' le_rfl hMbound
    _ = (ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) *
          ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal)) * ((D.card : ℝ≥0∞)⁻¹ * S) := by
        ring
    _ = (ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
          ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ))))) *
          ((D.card : ℝ≥0∞)⁻¹ * S) := by rw [hcoeff]
    _ = ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
          (ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)))) *
            (D.card : ℝ≥0∞)⁻¹ * S) := by ring

/-- **THE CARRIER IDENTIFICATION** (item (C)).

This repository's finite-depth grid gauge is dominated by `CoarseGraining`'s
running-scale negative Besov seminorm at the cost of `√d · 3^{-s·Q.scale}`: the
`√d` is the Euclidean/sup comparison of the cell averages, the `3^{-s·Q.scale}`
is exactly the normalization the printed left-hand side carries and
`CoarseGraining`'s seminorm does not. -/
theorem ofReal_negBesovLpPartialNorm_le (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (N : ℕ) (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    ENNReal.ofReal (negBesovLpPartialNorm Q s.1 p.exponent.toReal N F.toField) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        cubeEuclideanNegativeBesovESeminorm Q s p F := by
  classical
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  set kappa : ℝ≥0∞ := ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) with hkappa
  set T : ℝ≥0∞ := ∑' j : ℕ, cubeEuclideanNegativeBesovDepthEnergy Q s p F j with hT
  have hpartial : ENNReal.ofReal (negBesovLpPartialNorm Q s.1 p.exponent.toReal N F.toField) =
      (∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal
          (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^
            p.exponent.toReal)) ^ (1 / p.exponent.toReal) := by
    rw [negBesovLpPartialNorm_def,
      ← ENNReal.ofReal_rpow_of_nonneg
        (Finset.sum_nonneg fun j _ =>
          negBesovLpDepthSeminorm_rpow_nonneg Q s.1 p.exponent.toReal F.toField j)
        (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun j _ =>
        negBesovLpDepthSeminorm_rpow_nonneg Q s.1 p.exponent.toReal F.toField j]
  have hsum : (∑ j ∈ Finset.range (N + 1),
      ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^ p.exponent.toReal)) ≤
      kappa ^ p.exponent.toReal * T := by
    calc (∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal
            (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^ p.exponent.toReal))
        ≤ ∑ j ∈ Finset.range (N + 1),
            kappa ^ p.exponent.toReal * cubeEuclideanNegativeBesovDepthEnergy Q s p F j :=
          Finset.sum_le_sum fun j _ => ofReal_negBesovLpDepthSeminorm_rpow_le Q s p F j
      _ = kappa ^ p.exponent.toReal * ∑ j ∈ Finset.range (N + 1),
            cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by rw [Finset.mul_sum]
      _ ≤ kappa ^ p.exponent.toReal * T := mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)
  rw [hpartial, cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy, ← hT]
  calc (∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal
          (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^
            p.exponent.toReal)) ^ (1 / p.exponent.toReal)
      ≤ (kappa ^ p.exponent.toReal * T) ^ (1 / p.exponent.toReal) :=
        ENNReal.rpow_le_rpow hsum (by positivity)
    _ = (kappa ^ p.exponent.toReal) ^ (1 / p.exponent.toReal) *
          T ^ (1 / p.exponent.toReal) := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = kappa * T ^ (p.exponent.toReal)⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt ht), ENNReal.rpow_one, one_div]

/-! ## 3. The named gauge hypothesis `(★)`, and its gate -/

/-- **`(★)`: the grid gauge is dominated by the smooth fractional dual.**

The converse of `CoarseGraining`'s proved
`cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`
(`EuclideanWspSmoothDualBesovBound`), on the range `s·p' < 1` where `p'` is the
conjugate exponent.

THIS IS A HYPOTHESIS.  It is never proved in this repository, and this file
grep-verified that no converse exists anywhere in `CoarseGraining`.  The gate
`s·p' < 1` is the range in which the grid's own dual tests (multi-depth
grid-piecewise constants) belong to `W̲^{s,p'}`. -/
def NegativeBesovGridSmoothDualConverse (d : ℕ) (p : FiniteLpExponent) (CA : ℝ≥0∞) : Prop :=
  ∀ (Q : TriadicCube d) (s : FractionalOrder),
    s.1 * p.conjugate.exponent.toReal < 1 →
    ∀ F : CubeEuclideanLpField Q FiniteLpExponent.two,
      cubeEuclideanNegativeBesovESeminorm Q s p F ≤
        CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F

/-- For `2 ≤ p` the conjugate exponent is at most `2`. -/
theorem conjugate_exponent_le_two {p : FiniteLpExponent} (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    p.conjugate.exponent ≤ 2 := by
  have hsub : (1 : ℝ≥0∞) ≤ p.exponent - 1 := by
    refine ENNReal.le_sub_of_add_le_left (by simp) ?_
    simpa only [one_add_one_eq_two] using hp
  have hinv : (p.exponent - 1)⁻¹ ≤ 1 := by
    simpa only [inv_one] using ENNReal.inv_le_inv.mpr hsub
  have hval : p.conjugate.exponent = 1 + (p.exponent - 1)⁻¹ := rfl
  rw [hval]
  calc (1 : ℝ≥0∞) + (p.exponent - 1)⁻¹ ≤ 1 + 1 := add_le_add le_rfl hinv
    _ = 2 := one_add_one_eq_two

/-- **The gate of `(★)` is satisfied at the Step-3 pin.**  `s ≤ 1/4` and
`2 ≤ p` give `s·p' ≤ 1/2 < 1`. -/
theorem gate_of_le_quarter {p : FiniteLpExponent} (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) : s * p.conjugate.exponent.toReal < 1 := by
  have hle : p.conjugate.exponent.toReal ≤ 2 := by
    have h := ENNReal.toReal_mono (by simp) (conjugate_exponent_le_two hp)
    simpa using h
  have hnn : 0 ≤ p.conjugate.exponent.toReal := ENNReal.toReal_nonneg
  nlinarith [hs0, hs, hle, hnn]

/-! ## 4. the Calderón--Zygmund flux comparison lemma at the multiscale reading, PRODUCED -/

/-- **`CzFluxMultiscale` from `(★)`** — the exact input
`HomSpineMultiscaleClause.exists_coarseGrainingFinitePMultiscale_of_cz` consumes.

The chain is: the carrier identification (`§2`), then `(★)` on `□_m`, then
`CoarseGraining`'s proved smooth-dual CZ step
`exists_centeredCubeFluxComparison_cz`, then the descendant transfer
`localFluxDefect_smoothDualAverage_le`.  The three scale powers `3^{-sm} ·
3^{s(m-n)} · 3^{sn}` multiply to one (`ofReal_three_rpow_scale_triple`), so the
constant is a genuine `C(p,d)`: `√d · C_(★) · C_cz · C_d`. -/
theorem czFluxMultiscale_of_gridConverse (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    {CA : ℝ≥0∞} (hCA : CA ≠ ⊤) (hconv : NegativeBesovGridSmoothDualConverse d p CA) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Ccz : ℝ, 0 ≤ Ccz ∧
      ∀ (m n : ℤ), n < m → ∀ hn : n ≤ (originCube d m).scale,
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ),
        0 < sigma0 →
      ∀ s : FractionalOrder, s.1 * p.conjugate.exponent.toReal < 1 →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsCenteredCubeFluxBalanced m a sigma0 u v →
        HasCenteredCubeH10Difference m u v →
        localFluxDefectNegativeBesovLpAverage (originCube d m) n hn a sigma0 u s p ≠ ⊤ →
      ∀ Fgrad Fflux : Vec d → Vec d,
        Fgrad = (centeredCubeGradientDifferenceL2Field m u v).toField →
        Fflux = (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField →
        CzFluxMultiscale (originCube d m) n hn a sigma0 u s p Ccz Fgrad Fflux := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨Ccz0, hCcz0top, hCcz0⟩ := exists_centeredCubeFluxComparison_cz d hd p hp
  set Cd : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualBesovConstant d with hCd
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt d) * CA * Ccz0 * Cd with hK
  have hKne : K ≠ ⊤ := by
    rw [hK]
    refine (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) hCcz0top) ?_).ne
    · exact ENNReal.ofReal_lt_top
    · exact lt_of_le_of_ne le_top hCA
    · exact cubeEuclideanNegativeWspSmoothDualBesovConstant_lt_top d
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m n hnm hn a sigma0 hsigma0 s hgate u v hbal hzero hBfin Fgrad Fflux hFg hFf N
  set Ggrad := centeredCubeGradientDifferenceL2Field m u v with hGgrad
  set Gflux := centeredCubeFluxDifferenceL2Field m a sigma0 u v with hGflux
  set B : ℝ≥0∞ := localFluxDefectNegativeBesovLpAverage (originCube d m) n hn a sigma0 u s p
    with hB
  set W : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) with hW
  set Wmn : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ)))) with hWmn
  set Wn : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) with hWn
  have hsplit : ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) =
      ENNReal.ofReal (Real.sqrt d) * W := by
    have hms : (originCube d m).scale = m := rfl
    rw [gridScaleGauge, hms, ENNReal.ofReal_mul (Real.sqrt_nonneg _), hW, real_rpow_three_eq]
  have hCgrad := ofReal_negBesovLpPartialNorm_le (originCube d m) s p N Ggrad
  have hCflux := ofReal_negBesovLpPartialNorm_le (originCube d m) s p N Gflux
  have hAgrad := hconv (originCube d m) s hgate Ggrad
  have hAflux := hconv (originCube d m) s hgate Gflux
  have h1 := hCcz0 m n hnm a sigma0 hsigma0 s u v hbal hzero
  have h2 := localFluxDefect_smoothDualAverage_le hnm hn a sigma0 u s p
  have htriple : W * Wmn * Wn = 1 := ofReal_three_rpow_scale_triple s.1 m n
  have hchain : ENNReal.ofReal
      (sigma0 * negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Fgrad +
        negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Fflux) ≤ K * B := by
    rw [hFg, hFf,
      ENNReal.ofReal_add (mul_nonneg hsigma0.le (negBesovLpPartialNorm_nonneg _ _ _ _ _))
        (negBesovLpPartialNorm_nonneg _ _ _ _ _),
      ENNReal.ofReal_mul hsigma0.le]
    calc ENNReal.ofReal sigma0 *
          ENNReal.ofReal
            (negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Ggrad.toField) +
          ENNReal.ofReal
            (negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Gflux.toField)
        ≤ ENNReal.ofReal sigma0 *
            (ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              cubeEuclideanNegativeBesovESeminorm (originCube d m) s p Ggrad) +
            ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              cubeEuclideanNegativeBesovESeminorm (originCube d m) s p Gflux :=
          add_le_add (mul_le_mul' le_rfl hCgrad) hCflux
      _ ≤ ENNReal.ofReal sigma0 *
            (ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Ggrad)) +
            ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Gflux) :=
          add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl hAgrad))
            (mul_le_mul' le_rfl hAflux)
      _ = ENNReal.ofReal (Real.sqrt d) * CA *
            (W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p) := by
          rw [hsplit]
          simp only [centeredCubeFluxComparisonSmoothDualLHS, ← hGgrad, ← hGflux]
          ring
      _ ≤ ENNReal.ofReal (Real.sqrt d) * CA * (W * (Ccz0 * Wmn *
            centeredCubeLocalFluxDefectSmoothDualLpAverage m n hnm a sigma0 u s p)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl h1)
      _ ≤ ENNReal.ofReal (Real.sqrt d) * CA * (W * (Ccz0 * Wmn * (Cd * Wn * B))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl h2))
      _ = (W * Wmn * Wn) * (K * B) := by rw [hK]; ring
      _ = K * B := by rw [htriple, one_mul]
  have hKB : K * B ≠ ⊤ := ENNReal.mul_ne_top hKne hBfin
  have hfinal := (ENNReal.ofReal_le_iff_le_toReal hKB).mp hchain
  rwa [ENNReal.toReal_mul] at hfinal

/-! ## 5. The multiscale clause, produced from `(★)` alone -/

/-- **THE MULTISCALE CLAUSE, PRODUCED FROM `(★)`.**

`HomSpineRecutSupport.CoarseGrainingFinitePMultiscale` — clause 1 of the
transcribed source hypothesis (the general coarse-graining proposition at
finite `p`), at the MULTISCALE reading of its undefined negative-norm symbol —
holds under exactly the printed hypotheses, plus the single gauge inequality
`(★)`.

Compared with
`HomSpineMultiscaleClause.exists_coarseGrainingFinitePMultiscale_of_cz`, the
bespoke input `CzFluxMultiscale` is gone; what remains is `(★)`, a statement
about two norms on one cube with no PDE, no `σ₀`, no coefficient field and no
carrier of this repository in it.  The comparison field `v` and the two printed
equations are the print's own Dirichlet-pair setting; `Fgrad`, `Fflux` are the
printed `∇u - ∇v` and `𝐚∇u - σ₀∇v`.

The constant is `√d · C_(★) · C(p,d)` with `C(p,d)` the constant of
`exists_printedCoarseGrainingFiniteP_smoothDual`, i.e. a genuine `C(p,d)` fixed
before the cube, the orders, the coefficient field, the forcing and the
solutions. -/
theorem exists_coarseGrainingFinitePMultiscale_of_gridConverse (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    {CA : ℝ≥0∞} (hCA : CA ≠ ⊤) (hconv : NegativeBesovGridSmoothDualConverse d p CA) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Ccg : ℝ, 0 ≤ Ccg ∧
      ∀ (m : ℤ) (jn : ℕ), 0 < jn →
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        s.1 * p.conjugate.exponent.toReal < 1 →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u v : H1Function (openCubeSet (originCube d m))),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
      ∀ (E1 E2 Dg : ℝ) (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d),
        0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg →
        (∀ R, 0 ≤ Gen R) →
        (∀ R, printedLocalEnergy a u R ≤ Gen R) →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0 s1 ≤
          ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0
            (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
        Fgrad = (centeredCubeGradientDifferenceL2Field m u v).toField →
        Fflux = (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField →
          CoarseGrainingFinitePMultiscale (originCube d m) jn Ccg s.1 s1.1 s2.1
            p.exponent.toReal sigma0 E1 E2 Dg Gen Fgrad Fflux := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hsd⟩ := exists_printedCoarseGrainingFiniteP_smoothDual d hd p hp
  set Kd : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt d) * CA with hKd
  have hKdne : Kd ≠ ⊤ := by
    rw [hKd]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCA
  have hKdC : Kd * C ≠ ⊤ := ENNReal.mul_ne_top hKdne hCtop.ne
  refine ⟨(Kd * C).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m jn hjn s1 s s2 hs1s hss2 hgate a sigma0 hsigma0 g u v hg hu hv hzero
    E1 E2 Dg Gen Fgrad Fflux hE10 hE20 hDg0 hGen0 hGen hE1 hE2 hDg hFg hFf S hS N
  have hms : (originCube d m).scale = m := rfl
  have hn : (originCube d m).scale - (jn : ℤ) ≤ (originCube d m).scale := by omega
  have hnm : (originCube d m).scale - (jn : ℤ) < m := by rw [hms]; omega
  /- the energy slot, from the clause's own hypothes -/
  have hS0 : (0 : ℝ) ≤ S := by
    have hge := hS 0
    have h0 : (0 : ℝ) ≤ coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
        (s.1 - s1.1) jn 0 Gen := by
      rw [coarseGrainingEnergyPartial_def]
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _)) _
    linarith only [hge, h0]
  have hSlot : weightedLocalSymmetricEnergyLp (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) hn a u s1 s p ≤ ENNReal.ofReal S :=
    weightedLocalSymmetricEnergyLp_le_ofReal hn a u s1 s p (wgap := s.1 - s1.1) le_rfl
      (by omega) hGen0 hGen hS0 hS
  /- the smooth-dual composition, already assembl -/
  have hdisplay := hsd m ((originCube d m).scale - (jn : ℤ)) hnm s1 s s2 hs1s hss2 a
    sigma0 hsigma0 g hg u v hu hv hzero
  set Ggrad := centeredCubeGradientDifferenceL2Field m u v with hGgrad
  set Gflux := centeredCubeFluxDifferenceL2Field m a sigma0 u v with hGflux
  set W : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) with hW
  have hsplit : ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) =
      ENNReal.ofReal (Real.sqrt d) * W := by
    rw [gridScaleGauge, hms, ENNReal.ofReal_mul (Real.sqrt_nonneg _), hW, real_rpow_three_eq]
  have hCgrad := ofReal_negBesovLpPartialNorm_le (originCube d m) s p N Ggrad
  have hCflux := ofReal_negBesovLpPartialNorm_le (originCube d m) s p N Gflux
  have hAgrad := hconv (originCube d m) s hgate Ggrad
  have hAflux := hconv (originCube d m) s hgate Gflux
  have hchain : ENNReal.ofReal
      (sigma0 * negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Fgrad +
        negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Fflux) ≤
      ENNReal.ofReal (coarseGrainingFinitePRHS (Kd * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ))) := by
    rw [hFg, hFf,
      ENNReal.ofReal_add (mul_nonneg hsigma0.le (negBesovLpPartialNorm_nonneg _ _ _ _ _))
        (negBesovLpPartialNorm_nonneg _ _ _ _ _),
      ENNReal.ofReal_mul hsigma0.le]
    calc ENNReal.ofReal sigma0 *
          ENNReal.ofReal
            (negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Ggrad.toField) +
          ENNReal.ofReal
            (negBesovLpPartialNorm (originCube d m) s.1 p.exponent.toReal N Gflux.toField)
        ≤ ENNReal.ofReal sigma0 *
            (ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              cubeEuclideanNegativeBesovESeminorm (originCube d m) s p Ggrad) +
            ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              cubeEuclideanNegativeBesovESeminorm (originCube d m) s p Gflux :=
          add_le_add (mul_le_mul' le_rfl hCgrad) hCflux
      _ ≤ ENNReal.ofReal sigma0 *
            (ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Ggrad)) +
            ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Gflux) :=
          add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl hAgrad))
            (mul_le_mul' le_rfl hAflux)
      _ = Kd * (W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p) := by
          rw [hKd, hsplit]
          simp only [centeredCubeFluxComparisonSmoothDualLHS, ← hGgrad, ← hGflux]
          ring
      _ ≤ Kd * localCoarseGrainingLpRHS C (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p :=
          mul_le_mul' le_rfl hdisplay
      _ = localCoarseGrainingLpRHS (Kd * C) (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p :=
          localCoarseGrainingLpRHS_const_mul Kd C (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p
      _ ≤ ENNReal.ofReal (coarseGrainingFinitePRHS (Kd * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
            ((originCube d m).scale - (jn : ℤ))) :=
          localCoarseGrainingLpRHS_le_ofReal hn a hsigma0 g u s1 s s2 p hss2
            ENNReal.toReal_nonneg hE10 hE20 hDg0 hS0
            (le_of_eq (ENNReal.ofReal_toReal hKdC).symm) hE1 hE2 hDg hSlot
  exact (ENNReal.ofReal_le_ofReal_iff
    (coarseGrainingFinitePRHS_nonneg ENNReal.toReal_nonneg s.2.1 hss2 hE10 hE20 hDg0
      hS0)).mp hchain

/-! ## 6. `(★)` reduced to a test-field construction

The smooth-dual carrier does NOT restrict the dual tests to `C^∞`:
`CoarseGraining` proves
`ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le` unconditionally,
i.e. the smooth dual norm already dominates the pairing against EVERY
`W̲^{s,p'}(Q) ∩ L²(Q)` field.  (The mechanism is the completed-graph extension
of `EuclideanWspCompletedDualExtension`, itself built on the smooth density
theorem `exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt`.)  So the
multi-depth grid-piecewise-constant dual tests the grid gauge needs are
ADMISSIBLE tests, and `(★)` carries no smoothness obligation at all: what
remains is to build them and bound their Gagliardo norm. -/

/-- The depth-`≤ N` truncation of `CoarseGraining`'s running-scale negative Besov
 seminorm. -/
def negativeBesovPartialE (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (N : ℕ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (N + 1), cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ^
    (p.exponent.toReal)⁻¹

/-- The full seminorm is the supremum of its depth truncations: a bound uniform
in the truncation depth is a bound on the seminorm. -/
theorem cubeEuclideanNegativeBesovESeminorm_le_of_partial
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {F : CubeEuclideanLpField Q FiniteLpExponent.two} {X : ℝ≥0∞}
    (h : ∀ N : ℕ, negativeBesovPartialE Q s p F N ≤ X) :
    cubeEuclideanNegativeBesovESeminorm Q s p F ≤ X := by
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hpow : ∀ N : ℕ,
      (∑ j ∈ Finset.range (N + 1), cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ≤
        X ^ p.exponent.toReal := by
    intro N
    have h1 := ENNReal.rpow_le_rpow (h N) ht.le
    rwa [negativeBesovPartialE, ← ENNReal.rpow_mul, inv_mul_cancel₀ (ne_of_gt ht),
      ENNReal.rpow_one] at h1
  have hsum : (∑' j : ℕ, cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ≤
      X ^ p.exponent.toReal := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    have hsub : Finset.range n ⊆ Finset.range (n + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    exact le_trans (Finset.sum_le_sum_of_subset hsub) (hpow n)
  rw [cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy]
  calc (∑' j : ℕ, cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ^ (p.exponent.toReal)⁻¹
      ≤ (X ^ p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ :=
        ENNReal.rpow_le_rpow hsum (by positivity)
    _ = X := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (ne_of_gt ht), ENNReal.rpow_one]

/-- **The residual of `(★)`, in constructive form.**

For every cube, every admissible order pair and every depth truncation, a
`W̲^{s,p'}(Q) ∩ L²(Q)` field of full norm at most one whose pairing against `F`
sees the truncated grid mass, at a fixed `C(p,d)`.

This is the boundary-layer statement: the dual test of the depth-`≤ N` grid mass
is the multi-depth grid-piecewise-constant aggregate, and `‖·‖_{W̲^{s,p'}}` of a
depth-`j` piecewise constant concentrates on the `3^{-k}`-neighbourhoods of the
depth-`j` skeleton, which is where `s·p' < 1` buys the geometric decay.  NO
smoothness is required of the test: see the section header. -/
def GridDualTestFamily (d : ℕ) (p : FiniteLpExponent) (CA : ℝ≥0∞) : Prop :=
  ∀ (Q : TriadicCube d) (s : FractionalOrder),
    s.1 * p.conjugate.exponent.toReal < 1 →
    ∀ (F : CubeEuclideanLpField Q FiniteLpExponent.two) (N : ℕ),
      ∃ G : CubeEuclideanWspL2Field Q s p.conjugate,
        cubeEuclideanWspFullENorm Q s p.conjugate G.toField ≤ 1 ∧
          negativeBesovPartialE Q s p F N ≤
            CA * ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G|

/-- **`(★)` FROM THE TEST FAMILY.**  The only analytic content left in the
multiscale clause is the construction of the dual tests; the passage from those
tests to the smooth-dual norm is `CoarseGraining`'s proved
`ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le`, and the passage from
the truncations to the seminorm is `cubeEuclideanNegativeBesovESeminorm_le_of_partial`. -/
theorem negativeBesovGridSmoothDualConverse_of_testFamily {p : FiniteLpExponent}
    {CA : ℝ≥0∞} (h : GridDualTestFamily d p CA) :
    NegativeBesovGridSmoothDualConverse d p CA := by
  intro Q s hgate F
  refine cubeEuclideanNegativeBesovESeminorm_le_of_partial fun N => ?_
  obtain ⟨G, hG1, hG2⟩ := h Q s hgate F N
  refine hG2.trans ?_
  have hpair := ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le F G
  calc CA * ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G|
      ≤ CA * (cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
          cubeEuclideanWspFullENorm Q s p.conjugate G.toField) := mul_le_mul' le_rfl hpair
    _ ≤ CA * (cubeEuclideanNegativeWspSmoothDualENorm Q s p F * 1) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hG1)
    _ = CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by rw [mul_one]

/-- **The multiscale clause from the test family alone.**  The composition of
`negativeBesovGridSmoothDualConverse_of_testFamily` with
`exists_coarseGrainingFinitePMultiscale_of_gridConverse`: the printed clause 1 of
the general coarse-graining proposition at finite `p`, at the multiscale reading, from ONE
construction of dual test fields. -/
theorem exists_coarseGrainingFinitePMultiscale_of_testFamily (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    {CA : ℝ≥0∞} (hCA : CA ≠ ⊤) (h : GridDualTestFamily d p CA) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Ccg : ℝ, 0 ≤ Ccg ∧
      ∀ (m : ℤ) (jn : ℕ), 0 < jn →
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        s.1 * p.conjugate.exponent.toReal < 1 →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u v : H1Function (openCubeSet (originCube d m))),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
      ∀ (E1 E2 Dg : ℝ) (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d),
        0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg →
        (∀ R, 0 ≤ Gen R) →
        (∀ R, printedLocalEnergy a u R ≤ Gen R) →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0 s1 ≤
          ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0
            (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
        Fgrad = (centeredCubeGradientDifferenceL2Field m u v).toField →
        Fflux = (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField →
          CoarseGrainingFinitePMultiscale (originCube d m) jn Ccg s.1 s1.1 s2.1
            p.exponent.toReal sigma0 E1 E2 Dg Gen Fgrad Fflux :=
  exists_coarseGrainingFinitePMultiscale_of_gridConverse d hd p hp hCA
    (negativeBesovGridSmoothDualConverse_of_testFamily h)

end

end Algsuperdiff.Section4.Provider.Homogenization
