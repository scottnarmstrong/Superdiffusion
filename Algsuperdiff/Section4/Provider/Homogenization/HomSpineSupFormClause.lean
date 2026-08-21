/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridGauge

/-!
# The D1 re-cut, fork (iii): the SUP-over-depths clause carrier

## Why a sup-over-depths carrier

The manuscript aggregates depths by SUP, not by `ℓ^p`.  Its Step-3 display reads

```text
  3^{-ms} σ̄_m ‖∇u - ∇v‖_{Ŵ̲^{-s,∞}(□_m)}
    ≤ C s^{-1} σ̄_m^{1/2} 𝓔_{s₁,∞,1} ·
        sup_{k ≤ n} 3^{-(s-s₁)(n-k)} max_{z ∈ 3^k ℤ^d ∩ □_m}
          ν^{1/2} ‖∇u‖_{L̲²(z+□_k)}  +  (forcing term),
```

i.e. `p = ∞` on BOTH sides.  This repository's clause carrier
`HomSpineRecutSupport.CoarseGrainingFinitePMultiscale` puts
`negBesovLpPartialNorm` — the `ℓ^p`-over-depths aggregate — on the left.  That
was a transcription choice, not the print's shape, and the refutation record
(`HomSpineCzGridGaugeRefuted`) together with its `|log γ|^{1/p}` necessity are
properties OF THAT CHOICE: the flat field's sup is `O(1)` while its `ℓ^p`
aggregate is not.

This file gives the sup-over-depths sibling and the one fact that makes the
re-cut worth doing:

* `negBesovSupPartialNorm` — `sup_{j ≤ N}` of the SAME per-depth gauge terms
  (`negBesovLpDepthSeminorm`) the `ℓ^p` carrier sums.  No new geometry:
  the depth weight is the print's own `3^{-s j}`.
* `NegBesovSupGaugeBound` — the unbounded-`N` form, `∀ j`, which is exactly
  what every downstream consumer of the `ℓ^p` gauge actually uses (see
  `HomSpineSupFormRethread`).
* `CoarseGrainingSupMultiscale` — the clause sibling at the sup left-hand side,
  with the energy slot LEFT AT ITS `ℓ^p` SPELLING (that slot is where the
  finite-`p` `CoarseGraining` theorem enters; see the D3 section below).
* `CoarseGrainingFinitePMultiscale.toSup` — the regression direction: the
  clause implies the sup clause, at the same constants.
One caveat.  The depth-`j` GLOBAL comparison named below is not
realizable at a `γ`-uniform constant: there is a far-band
Gagliardo cost `Σ_{i<j} 3^{-i s p'} ≍ min(j, (s p')⁻¹)` for the depth-`j`
checkerboard test, saturating at `≈|log γ|^{1/p'}` over the Step-3 depth range
`⌈10|log γ|⌉`.  The print's carrier is per CELL, not per depth; see
`HomSpineSupFormCell`, which re-cuts §§1--4 of this file at
`sup_j max_{R ∈ D_j}` and needs only a single-CELL test.  Everything here
remains correct and is the intermediate reading (sup over depths of the `ℓ^p`
cell mean); §5 (D3) is independent of the cut.

* `NegativeBesovGridSmoothDualConverseAtDepth` +
  `ofReal_negBesovSupPartialNorm_le_of_depthConverse` — THE CONSUMPTION
  INTERFACE.  The sup-form clause needs the grid/smooth-dual comparison only ONE
  DEPTH AT A TIME; the depth-uniform constant `CA` is the only input, and no sum
  over depths is ever formed.  This is the slot the single-depth
  `GridDualTestFamily` fills; it is a NAMED INPUT here, never proved.
* `exists_coarseGrainingSupMultiscale_of_depthConverseOn` (§6) — THE CLAUSE,
  PRODUCED from that single-depth input plus the `CoarseGraining` machinery, at the
  constant `√d · CA · C(p,d)`.  So the supply's clause conjunct is producible at
  a `γ`-uniform constant exactly when `CA` is `γ`-uniform; the refuted
  depth-summed `(★)` is never used.

## The D3 arithmetic (section 5)

`coarseGrainingGeomFactor p w = (1 - 3^{-wp})^{-1/p}` is the price the finite-`p`
energy slot pays over the print's sup-form energy datum
(the mesoscale energy bound).  Two facts are checked:

* `coarseGrainingGeomFactor_le_three_halves` — the factor is `≤ 3/2`, with NO
  `γ`-dependence, as soon as `1 ≤ w·p`;
* `coarseGrainingGeomFactor_ge_inv_rpow` — and it is at least
  `(w·p·log 3)^{-1/p}` always, so on the complementary range `w·p ≤ 1` it is
  genuinely of size `(w p)^{-1/p}`.

At the §4.5 pin `w = s/4` this says: the factor is `O(1)` iff `s·p ≳ 4`, i.e.
iff `p` is allowed to grow like `|log γ|`.  So D3 is not a second, independent
obstruction — it is the SAME question as item (a) (a `p`-uniform
Calderón--Zygmund constant on a range reaching `p ≈ 4/s`), quantified.
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The sup-over-depths gauge carrier -/

/-- **The sup-over-depths partial gauge**, `sup_{j ≤ N} 3^{-sj} [·]_{depth j}`.

The `p = ∞` sibling of `negBesovLpPartialNorm`: the SAME per-depth terms, with
the outer `ℓ^p` sum replaced by the maximum.  This is the aggregation shape the
manuscript's `Ŵ̲^{-s,∞}` display uses. -/
def negBesovSupPartialNorm (Q : TriadicCube d) (s p : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j =>
    negBesovLpDepthSeminorm Q s p F j

theorem negBesovSupPartialNorm_def (Q : TriadicCube d) (s p : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    negBesovSupPartialNorm Q s p N F =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j =>
        negBesovLpDepthSeminorm Q s p F j := rfl

/-- Every depth term the sup reaches is below it. -/
theorem negBesovLpDepthSeminorm_le_negBesovSupPartialNorm (Q : TriadicCube d) (s p : ℝ)
    (F : Vec d → Vec d) {j N : ℕ} (hjN : j ≤ N) :
    negBesovLpDepthSeminorm Q s p F j ≤ negBesovSupPartialNorm Q s p N F :=
  Finset.le_sup' (f := fun i => negBesovLpDepthSeminorm Q s p F i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hjN))

/-- The sup is below any bound on the depth terms it reaches. -/
theorem negBesovSupPartialNorm_le {Q : TriadicCube d} {s p B : ℝ} {N : ℕ}
    {F : Vec d → Vec d} (h : ∀ j ≤ N, negBesovLpDepthSeminorm Q s p F j ≤ B) :
    negBesovSupPartialNorm Q s p N F ≤ B :=
  Finset.sup'_le _ _ fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem negBesovSupPartialNorm_nonneg (Q : TriadicCube d) (s p : ℝ) (N : ℕ)
    (F : Vec d → Vec d) : 0 ≤ negBesovSupPartialNorm Q s p N F :=
  le_trans (negBesovLpDepthSeminorm_nonneg Q s p F 0)
    (negBesovLpDepthSeminorm_le_negBesovSupPartialNorm Q s p F (Nat.zero_le N))

/-- **THE REGRESSION DIRECTION.**  The `ℓ^p` aggregate dominates the sup, at
constant one: `B^{-s}_{p,p} ↪ B^{-s}_{p,∞}`.  So every sup-form statement is
implied by its `ℓ^p` sibling and the re-cut only forgets. -/
theorem negBesovSupPartialNorm_le_negBesovLpPartialNorm (Q : TriadicCube d) (s : ℝ) {p : ℝ}
    (hp : 0 < p) (N : ℕ) (F : Vec d → Vec d) :
    negBesovSupPartialNorm Q s p N F ≤ negBesovLpPartialNorm Q s p N F :=
  negBesovSupPartialNorm_le fun _ hj =>
    negBesovLpDepthSeminorm_le_negBesovLpPartialNorm Q hp F hj

/-! ## 2. The unbounded-depth form, and its two equivalent readings -/

/-- **The sup-form gauge bound at level `A`**: every depth term of the printed
grid gauge is below `A`.  This is `3^{-ms}[F]_{B̲^{-s}_{p,∞}(□_m)} ≤ A`, the
`p = ∞` depth aggregation the manuscript's display carries. -/
def NegBesovSupGaugeBound (Q : TriadicCube d) (s p A : ℝ) (F : Vec d → Vec d) : Prop :=
  ∀ j : ℕ, negBesovLpDepthSeminorm Q s p F j ≤ A

/-- The two readings agree: a level for every truncation is a level for every
depth. -/
theorem negBesovSupGaugeBound_iff_forall_partial {Q : TriadicCube d} {s p A : ℝ}
    {F : Vec d → Vec d} :
    NegBesovSupGaugeBound Q s p A F ↔ ∀ N : ℕ, negBesovSupPartialNorm Q s p N F ≤ A := by
  constructor
  · intro h N
    exact negBesovSupPartialNorm_le fun j _ => h j
  · intro h j
    exact le_trans (negBesovLpDepthSeminorm_le_negBesovSupPartialNorm Q s p F (le_refl j)) (h j)

/-- The `ℓ^p` gauge bound gives the sup-form one, at the same level. -/
theorem NegBesovSupGaugeBound.of_partialBound {Q : TriadicCube d} {s p A : ℝ}
    (hp : 0 < p) {F : Vec d → Vec d}
    (h : ∀ N : ℕ, negBesovLpPartialNorm Q s p N F ≤ A) :
    NegBesovSupGaugeBound Q s p A F :=
  fun j => negBesovLpDepthSeminorm_le_of_partialBound Q hp F h j

theorem NegBesovSupGaugeBound.nonneg {Q : TriadicCube d} {s p A : ℝ} {F : Vec d → Vec d}
    (h : NegBesovSupGaugeBound Q s p A F) : 0 ≤ A :=
  le_trans (negBesovLpDepthSeminorm_nonneg Q s p F 0) (h 0)

theorem NegBesovSupGaugeBound.mono {Q : TriadicCube d} {s p A B : ℝ} {F : Vec d → Vec d}
    (h : NegBesovSupGaugeBound Q s p A F) (hAB : A ≤ B) : NegBesovSupGaugeBound Q s p B F :=
  fun j => (h j).trans hAB

/-! ## 3. The clause sibling at the sup left-hand side -/

/-- **THE SUP-FORM MULTISCALE CLAUSE** — the print's own aggregation.

`HomSpineRecutSupport.CoarseGrainingFinitePMultiscale` with the left-hand
`ℓ^p`-over-depths aggregate replaced by the sup, i.e. the manuscript's Step-3
display shape.  The energy slot is deliberately LEFT at its
`ℓ^p` spelling: that slot is the one the finite-`p` `CoarseGraining` theorem
(`exists_localCoarseGrainingLp`) supplies, and moving it to the sup is the D3
question, not a transcription choice (section 5).

THIS IS A HYPOTHESIS.  It is never proved in this repository. -/
def CoarseGrainingSupMultiscale (Q : TriadicCube d) (jn : ℕ)
    (Ccg s s1 s2 p sigma E1 E2 Dg : ℝ)
    (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d) : Prop :=
  ∀ S : ℝ, (∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) →
    ∀ N : ℕ,
      sigma * negBesovSupPartialNorm Q s p N Fgrad +
          negBesovSupPartialNorm Q s p N Fflux ≤
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))

/-- **The re-cut only forgets.**  The `ℓ^p` clause implies the sup-form
clause at the same constants. -/
theorem CoarseGrainingFinitePMultiscale.toSup {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d} (hp : 0 < p) (hsigma : 0 ≤ sigma)
    (h : CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux) :
    CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux := by
  intro S hS N
  have hmain := h S hS N
  have hgrad := negBesovSupPartialNorm_le_negBesovLpPartialNorm Q s hp N Fgrad
  have hflux := negBesovSupPartialNorm_le_negBesovLpPartialNorm Q s hp N Fflux
  have hg : sigma * negBesovSupPartialNorm Q s p N Fgrad ≤
      sigma * negBesovLpPartialNorm Q s p N Fgrad :=
    mul_le_mul_of_nonneg_left hgrad hsigma
  linarith only [hmain, hg, hflux]

/-- **The Step-3c leg of the sup-form clause.**

The flux leg is discarded (the source's own route (ii) in the paper) and the
printed `σ̄_m` weight stripped; the output is the sup-form gauge bound at the
level the Step-3c consumers take. -/
theorem CoarseGrainingSupMultiscale.gradGauge {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S)
    (hsigma : 0 < sigma) :
    NegBesovSupGaugeBound Q s p
      (sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)))
      Fgrad := by
  refine negBesovSupGaugeBound_iff_forall_partial.mpr fun N => ?_
  have hmain := h S hS N
  have hflux : (0 : ℝ) ≤ negBesovSupPartialNorm Q s p N Fflux :=
    negBesovSupPartialNorm_nonneg Q s p N Fflux
  have hstep : sigma * negBesovSupPartialNorm Q s p N Fgrad ≤
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
    linarith only [hmain, hflux]
  have hne : sigma ≠ 0 := ne_of_gt hsigma
  calc negBesovSupPartialNorm Q s p N Fgrad
      = sigma⁻¹ * (sigma * negBesovSupPartialNorm Q s p N Fgrad) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hsigma.le)

/-! ## 4. THE CONSUMPTION INTERFACE: one depth at a time -/

/-- **The single-depth grid/smooth-dual comparison.**

`HomSpineCzGridGauge.NegativeBesovGridSmoothDualConverse` asks for the FULL
`ℓ^p`-over-depths Besov seminorm against the smooth dual — that is the shape
refuted above, because the depth sum contributes `(1-3^{-sp})^{-1/p}`.  The
sup-form clause never forms that sum: it needs the comparison at ONE depth `j`
at a time, with the constant `CA` uniform in `j`,

```text
  ( 3^{sp(m-j)} avsum_{R ∈ D_j} ‖(F)_R‖^p )^{1/p}
      ≤ CA · ‖F‖_{Ŵ̲^{-s,p}(□_m), smooth dual}.
```

THIS IS A HYPOTHESIS, and it is the ONLY external input of
`supGauge_of_depthConverse`.  It is the slot the single-depth dual-test family
(the `GridDualTestFamily` at one depth) fills: one test function per depth, not
one test function per depth-tower. -/
def NegativeBesovGridSmoothDualConverseAtDepth (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (j : ℕ) (CA : ℝ≥0∞) : Prop :=
  ∀ F : CubeEuclideanLpField Q FiniteLpExponent.two,
    cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (1 / p.exponent.toReal) ≤
      CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F

/-- **One depth term of this development gauge against the smooth dual.**

The depth-`j` bridge `ofReal_negBesovLpDepthSeminorm_rpow_le`, rooted, composed
with the single-depth comparison.  No sum over depths occurs. -/
theorem ofReal_negBesovLpDepthSeminorm_le_of_depthConverse (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {CA : ℝ≥0∞} {j : ℕ}
    (hconv : NegativeBesovGridSmoothDualConverseAtDepth Q s p j CA)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    ENNReal.ofReal (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) := by
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hbase := ofReal_negBesovLpDepthSeminorm_rpow_le Q s p F j
  have hpow : (ENNReal.ofReal
      (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j)) ^ p.exponent.toReal ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
    rw [ENNReal.ofReal_rpow_of_nonneg
      (negBesovLpDepthSeminorm_nonneg Q s.1 p.exponent.toReal F.toField j) ht.le]
    exact hbase
  have hroot := ENNReal.rpow_le_rpow hpow
    (by positivity : (0 : ℝ) ≤ 1 / p.exponent.toReal)
  have hleft : ((ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j)) ^ p.exponent.toReal) ^
        (1 / p.exponent.toReal) =
      ENNReal.ofReal (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j) := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt ht), ENNReal.rpow_one]
  have hright : (ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ^ (1 / p.exponent.toReal) =
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (1 / p.exponent.toReal) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.exponent.toReal),
      ← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt ht), ENNReal.rpow_one]
  rw [hleft, hright] at hroot
  exact hroot.trans (mul_le_mul' le_rfl (hconv F))

/-- **THE SUP-FORM GAUGE, FROM THE SINGLE-DEPTH COMPARISON ALONE.**

Given the single-depth comparison at every depth with one constant `CA`, the
whole sup-over-depths partial gauge is below `√d · 3^{-sm} · CA` times the
smooth dual norm — with NO geometric factor and NO depth sum, because the sup
is realized depth-wise.

This is the exact shape in which the sup-form clause consumes the family. -/
theorem ofReal_negBesovSupPartialNorm_le_of_depthConverse (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {CA : ℝ≥0∞} (N : ℕ)
    (hconv : ∀ j : ℕ, NegativeBesovGridSmoothDualConverseAtDepth Q s p j CA)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    ENNReal.ofReal (negBesovSupPartialNorm Q s.1 p.exponent.toReal N F.toField) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) := by
  classical
  set B : ℝ≥0∞ := ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
    (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) with hB
  by_cases hBtop : B = ⊤
  · rw [hBtop]; exact le_top
  have hreal : ∀ j : ℕ, negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ≤
      B.toReal := by
    intro j
    have hj := ofReal_negBesovLpDepthSeminorm_le_of_depthConverse Q s p (hconv j) F
    have hle : ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j) ≤ B := hj
    have := ENNReal.toReal_mono hBtop hle
    rwa [ENNReal.toReal_ofReal
      (negBesovLpDepthSeminorm_nonneg Q s.1 p.exponent.toReal F.toField j)] at this
  have hsup : negBesovSupPartialNorm Q s.1 p.exponent.toReal N F.toField ≤ B.toReal :=
    negBesovSupPartialNorm_le fun j _ => hreal j
  calc ENNReal.ofReal (negBesovSupPartialNorm Q s.1 p.exponent.toReal N F.toField)
      ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal hsup
    _ = B := ENNReal.ofReal_toReal hBtop

/-! ## 5. THE D3 ARITHMETIC: when the `ℓ^p` energy slot is free -/

/-- **The finite-`p` energy factor is `γ`-uniform once `1 ≤ w·p`.**

`coarseGrainingGeomFactor p w = (1-3^{-wp})^{-1/p}` is what the `ℓ^p` energy
slot pays over the manuscript's sup-form energy datum
the mesoscale energy bound.  As soon as the product `w·p` reaches `1` the ratio
`3^{-wp}` is at most `1/3` and the whole factor is at most `3/2`: no `s`, no
`γ`, no `d`.

At the §4.5 pin `w = s/4` this is the condition `4 ≤ s·p`. -/
theorem coarseGrainingGeomFactor_le_three_halves {p w : ℝ} (hp : 1 ≤ p) (hwp : 1 ≤ w * p) :
    coarseGrainingGeomFactor p w ≤ 3 / 2 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have hratio : (3 : ℝ) ^ (-(w * p)) ≤ 1 / 3 := by
    have hmono : (3 : ℝ) ^ (-(w * p)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hwp])
    have hval : (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 := by
      rw [Real.rpow_neg_one]
      norm_num
    rwa [hval] at hmono
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(w * p)) := three_rpow_pos _
  have hden : (2 : ℝ) / 3 ≤ 1 - (3 : ℝ) ^ (-(w * p)) := by linarith only [hratio]
  have hden0 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(w * p)) := by linarith only [hden]
  have hinv : (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ ≤ 3 / 2 := by
    have hstep : (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ ≤ ((2 : ℝ) / 3)⁻¹ :=
      inv_anti₀ (by norm_num) hden
    have hval : ((2 : ℝ) / 3)⁻¹ = 3 / 2 := by norm_num
    linarith only [hstep, hval.le, hval.ge]
  have hinv0 : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ := le_of_lt (inv_pos.mpr hden0)
  have hstep : ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p) ≤ (3 / 2 : ℝ) ^ (1 / p) :=
    Real.rpow_le_rpow hinv0 hinv (by positivity)
  have hexp : (3 / 2 : ℝ) ^ (1 / p) ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [div_le_one hp0]
    exact hp
  rw [coarseGrainingGeomFactor_def]
  calc ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p)
      ≤ (3 / 2 : ℝ) ^ (1 / p) := hstep
    _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := hexp
    _ = 3 / 2 := Real.rpow_one _

/-- The §4.5 reading: at the weight gap `w = s/4` the energy factor is
`γ`-uniform exactly on the range `4 ≤ s·p`. -/
theorem coarseGrainingGeomFactor_quarter_le_three_halves {p s : ℝ} (hp : 1 ≤ p)
    (hsp : 4 ≤ s * p) : coarseGrainingGeomFactor p (s / 4) ≤ 3 / 2 := by
  refine coarseGrainingGeomFactor_le_three_halves hp ?_
  have : s / 4 * p = s * p / 4 := by ring
  rw [this]
  linarith only [hsp]

/-- **And below that range the factor is genuinely large.**

`1 - 3^{-t} ≤ t·log 3` (convexity of `exp`), so
`coarseGrainingGeomFactor p w ≥ (w p log 3)^{-1/p}`.  At the §4.5 pins
`w = s/4`, `p = 4d`, `s ≍ |log γ|^{-1}` this is `≍ |log γ|^{1/(4d)}`: the
factor recorded in `HomSpineEnergySlot.recutEnergySlotConst` is not an artifact
of the estimate used, it is the size of `(1-3^{-wp})^{-1/p}` itself. -/
theorem coarseGrainingGeomFactor_ge_inv_rpow {p w : ℝ} (hp : 0 < p) (hw : 0 < w) :
    ((w * p * Real.log 3)⁻¹) ^ (1 / p) ≤ coarseGrainingGeomFactor p w := by
  have ht : 0 < w * p := mul_pos hw hp
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htl : 0 < w * p * Real.log 3 := mul_pos ht hlog
  have hexp : (1 : ℝ) - w * p * Real.log 3 ≤ (3 : ℝ) ^ (-(w * p)) := by
    have hbase := Real.add_one_le_exp (Real.log 3 * -(w * p))
    have hrw : (3 : ℝ) ^ (-(w * p)) = Real.exp (Real.log 3 * -(w * p)) :=
      Real.rpow_def_of_pos (by norm_num) _
    rw [hrw]
    linarith only [hbase]
  have hden : 1 - (3 : ℝ) ^ (-(w * p)) ≤ w * p * Real.log 3 := by linarith only [hexp]
  have hden0 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(w * p)) := by
    have hlt : (3 : ℝ) ^ (-(w * p)) < 1 := three_rpow_neg_lt_one ht
    linarith only [hlt]
  have hinv : (w * p * Real.log 3)⁻¹ ≤ (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ :=
    inv_anti₀ hden0 hden
  rw [coarseGrainingGeomFactor_def]
  exact Real.rpow_le_rpow (le_of_lt (inv_pos.mpr htl)) hinv (by positivity)

/-! ## 6. THE SUP-FORM CLAUSE, PRODUCED FROM THE SINGLE-DEPTH COMPARISON -/

/-- **THE SUP-FORM MULTISCALE CLAUSE, PRODUCED.**

`HomSpineCzGridGaugeBanded.exists_coarseGrainingFinitePMultiscale_of_gridConverseOn`
re-cut at fork (iii): the `ℓ^p`-over-depths left-hand side is replaced by the
print's sup, and the ONE hypothesis is the SINGLE-DEPTH grid/smooth-dual
comparison at a depth-uniform `CA` — never the depth-summed `(★)` refuted
above, and no geometric factor is formed anywhere in this proof.

The constant is `√d · CA · C(p,d)` with `C(p,d)` the constant of
`exists_printedCoarseGrainingFiniteP_smoothDual`, i.e. a genuine `C(p,d)` fixed
before the cube, the orders, the coefficient field, the forcing and the
solutions: `γ`-uniform as soon as `CA` is.

The energy slot is unchanged, so this theorem is silent about D3 (§5). -/
theorem exists_coarseGrainingSupMultiscale_of_depthConverseOn (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    {CA : ℝ≥0∞} (hCA : CA ≠ ⊤) (Pred : FractionalOrder → Prop)
    (hconv : ∀ (m : ℤ) (j : ℕ) (s : FractionalOrder), Pred s →
      NegativeBesovGridSmoothDualConverseAtDepth (originCube d m) s p j CA) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Ccg : ℝ, 0 ≤ Ccg ∧
      ∀ (m : ℤ) (jn : ℕ), 0 < jn →
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 → Pred s →
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
          CoarseGrainingSupMultiscale (originCube d m) jn Ccg s.1 s1.1 s2.1
            p.exponent.toReal sigma0 E1 E2 Dg Gen Fgrad Fflux := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hsd⟩ := exists_printedCoarseGrainingFiniteP_smoothDual d hd p hp
  set Kd : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt d) * CA with hKd
  have hKdne : Kd ≠ ⊤ := by
    rw [hKd]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCA
  have hKdC : Kd * C ≠ ⊤ := ENNReal.mul_ne_top hKdne hCtop.ne
  refine ⟨(Kd * C).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m jn hjn s1 s s2 hs1s hss2 hband a sigma0 hsigma0 g u v hg hu hv hzero
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
  /- the ONE input, one depth at a ti -/
  have hSgrad := ofReal_negBesovSupPartialNorm_le_of_depthConverse (originCube d m) s p N
    (fun j => hconv m j s hband) Ggrad
  have hSflux := ofReal_negBesovSupPartialNorm_le_of_depthConverse (originCube d m) s p N
    (fun j => hconv m j s hband) Gflux
  have hchain : ENNReal.ofReal
      (sigma0 * negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Fgrad +
        negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Fflux) ≤
      ENNReal.ofReal (coarseGrainingFinitePRHS (Kd * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ))) := by
    rw [hFg, hFf,
      ENNReal.ofReal_add (mul_nonneg hsigma0.le (negBesovSupPartialNorm_nonneg _ _ _ _ _))
        (negBesovSupPartialNorm_nonneg _ _ _ _ _),
      ENNReal.ofReal_mul hsigma0.le]
    calc ENNReal.ofReal sigma0 *
          ENNReal.ofReal
            (negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Ggrad.toField) +
          ENNReal.ofReal
            (negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Gflux.toField)
        ≤ ENNReal.ofReal sigma0 *
            (ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Ggrad)) +
            ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Gflux) :=
          add_le_add (mul_le_mul' le_rfl hSgrad) hSflux
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

end

end Algsuperdiff.Section4.Provider.Homogenization
