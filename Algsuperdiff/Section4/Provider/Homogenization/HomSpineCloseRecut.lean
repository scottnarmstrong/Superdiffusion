/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepThreeCoarse
import Algsuperdiff.Section4.Provider.Homogenization.HomStepFourEnergy
import Algsuperdiff.Section4.Provider.Homogenization.HomFinitePSource

/-!
# Theorem B, §4.5: the Step-2b/3b re-cuts (`hlevel`, `hS`)

## What this module is

Two re-cuts of statements, needed because the frozen root's clause bodies carry
GENERAL data `(K_g, K_h^∞, K_h)` while the Step-2/Step-3 chain was cut at the
special data `(1, 0, 1)`.

### (a) The data-general Step-2 majorant

`HomStepThreeCoarse.homStepTwoMajorant Cr Xfac Eq σ̄ m` carries the bracket
`σ̄^{-1/2}3^{m/2} + σ̄^{1/2}3^{m/2}`, which is EXACTLY the `energyBracket σ̄
3^{m/2} 1 0 1` (`homStepTwoMajorant_eq_data`).  Replacing the `(1,0,1)` by the
root's own `(K_g, K_h^∞, K_h)` gives `homStepTwoMajorantData`, and the two
printed brackets are related by the identity

```text
  √σ̄ · energyBracket σ̄ … / σ̄  =  dataBracket σ̄ …      (`sqrt_mul_energyBracket_div`)
```

i.e. the introduction's energy display bracket divided by `σ̄` and re-weighted
by `√σ̄` is the introduction's homogenization estimate bracket — the (C3)
bracket.  Nothing is approximated: `sqrt_mul_energyBracket_div` is an equality,
and it is exactly the arithmetic Step 3a performs silently when it divides the
display by `σ̄_m`.

### (c) The energy slot at the `s₁ = s/4` pin — A MEASURED PRINT DEFECT

The `coarseGrainingEnergyPartial_le_of_bound` feeds the printed `ℓ^p` energy
slot from a UNIFORM bound `Gen R ≤ S`.  What Step 2b actually delivers is a
WEIGHTED bound: at the §4.5 parameter web the family bound `F j z ≤
K·3^{(1-α)(m-j)}` (the `stepTwoLocal_sectionFive` / `HomStepTwoLocal`) grows
like `3^{a i}` in the depth index `i = (m-n)+i` with

```text
  a = 1 - α = s/2.
```

The printed weight of the energy slot is `3^{-(s-s₁)p i}`.  So the summand is
`3^{-((s-s₁)-a)p i}` and the slot converges **iff `s₁ < s - a = s/2`**.  The
manuscript's `s₁ = s/2` is EXACTLY the borderline: `(s - s₁) - a = 0`, every
summand is the same, the partial sums grow linearly in `N`, and NO `S`-bound
survives.  This is machine-visible in `stepTwo_weightGap_borderline` (the
`s₁ = s/2` gap is `0`) and `stepTwo_weightGap_quarterPin` (the `s₁ = s/4` gap
is `s/4 > 0`).

The choice below is free at the hypothesis level and stays inside the printed
range `s₁ ∈ (0,s)` of the source proposition itself — it is a choice the printed
statement already offers, i.e. pre-authorized `s`-power territory, not a
statement change:

```text
  s₁:= s/4    ⟹    (s - s₁) - a = 3s/4 - s/2 = s/4 > 0.
```

`coarseGrainingEnergyPartial_le_of_weightedBound` is the weighted-hypothesis
variant; `coarseGrainingEnergyPartial_le_at_quarterPin` is its instance at the
pin.  The price is the explicit geometric factor
`(1 - 3^{-((w-a)p)})^{-1/p}` in place of `(1 - 3^{-(wp)})^{-1/p}`, i.e. a
displayed constant and nothing else.

### (b) THE `ν` VERSUS `σ̄` SEAM — NOTED, NOT CONVERTED

The printed energy slot sums `‖σ^{1/2}∇u‖_{L̲²(z+□_k)}^p` (transcribed in
`HomFinitePSource`), while Step 2b's family (`HomStepTwoLocal`) is the
manuscript's `ν^{1/2}‖∇u‖_{L̲²(z+□_j)}`.  The printed `σ` of the energy slot
is UNSUBSCRIPTED and therefore ambiguous between

* the coefficient field's own symmetric part — here `symmPart a_L = ν Id`, in
  which case `‖σ^{1/2}∇u‖ = ν^{1/2}‖∇u‖` and the Step-2b family feeds the slot
  with NO conversion; and
* the constant comparator `σ₀ = σ̄_m`, in which case feeding the Step-2b family
  into the slot would require a `ν ↔ σ̄` conversion.

This module refuses the second reading and performs NO conversion: the per-cube
energy `Gen` is left ABSTRACT in every statement below (as it is in
`GeneralCoarseGrainingFiniteP`), so the caller pins it, and the units doctrine
is not touched anywhere in this file.  The seam is reported, not crossed.
-/

open Homogenization Homogenization.Book.Ch03 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The data-general Step-2 majorant -/

/-- **The Step-2 majorant at GENERAL data.**

`homStepTwoMajorant` with the printed bracket `σ̄^{-1/2}3^{m/2} +
σ̄^{1/2}3^{m/2}` replaced by the `energyBracket σ̄ pow K_g K_h^∞ K_h`.  The
special case is `homStepTwoMajorant_eq_data` below. -/
def homStepTwoMajorantData (Cr Xfac Eq sigma pow Kg KhInf Kh : ℝ) : ℝ :=
  Cr * Xfac * (1 + Eq) * energyBracket sigma pow Kg KhInf Kh

/-- The majorant IS the data-general one at the data `(K_g, K_h^∞, K_h)
= (1, 0, 1)` and `pow = 3^{m/2}`.  No inequality is spent. -/
theorem homStepTwoMajorant_eq_data (Cr Xfac Eq sigma : ℝ) (m : ℤ) :
    homStepTwoMajorant Cr Xfac Eq sigma m =
      homStepTwoMajorantData Cr Xfac Eq sigma ((3 : ℝ) ^ ((m : ℝ) / 2)) 1 0 1 := by
  rw [homStepTwoMajorant, homStepTwoMajorantData, energyBracket]
  ring

theorem homStepTwoMajorantData_nonneg {Cr Xfac Eq sigma pow Kg KhInf Kh : ℝ}
    (hCr : 0 ≤ Cr) (hXfac : 0 ≤ Xfac) (hEq : 0 ≤ Eq) (hpow : 0 ≤ pow) (hKg : 0 ≤ Kg)
    (hKhInf : 0 ≤ KhInf) (hKh : 0 ≤ Kh) :
    0 ≤ homStepTwoMajorantData Cr Xfac Eq sigma pow Kg KhInf Kh := by
  have h1 : (0 : ℝ) ≤ Real.sqrt sigma⁻¹ * pow * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hpow) hKg
  have h2 : (0 : ℝ) ≤ Real.sqrt sigma * (KhInf + pow * Kh) :=
    mul_nonneg (Real.sqrt_nonneg _) (by
      have := mul_nonneg hpow hKh
      linarith only [hKhInf, this])
  have hbr : (0 : ℝ) ≤ energyBracket sigma pow Kg KhInf Kh := by
    rw [energyBracket]
    linarith only [h1, h2]
  rw [homStepTwoMajorantData]
  exact mul_nonneg (mul_nonneg (mul_nonneg hCr hXfac) (by linarith only [hEq])) hbr

/-- **THE BRACKET IDENTITY, exact** (the hand-verified step, formalized).

`√σ̄ · (e.intro.energies bracket) / σ̄  =  (e.intro.homogenization.estimate
bracket)`.  This is Step 3a's silent division by `σ̄_m` combined with the
`√σ̄`-weight the Proposition's first term carries: the two printed brackets are
the same object up to this exact factor, and no inequality is spent. -/
theorem sqrt_mul_energyBracket_div (sigma pow Kg KhInf Kh : ℝ) (hsig : 0 < sigma) :
    Real.sqrt sigma * energyBracket sigma pow Kg KhInf Kh / sigma =
      dataBracket sigma pow Kg KhInf Kh := by
  have hkey : Real.sqrt sigma * dataBracket sigma pow Kg KhInf Kh =
      energyBracket sigma pow Kg KhInf Kh :=
    sqrt_mul_dataBracket sigma pow Kg KhInf Kh hsig
  have hsq : Real.sqrt sigma * Real.sqrt sigma = sigma :=
    Real.mul_self_sqrt (le_of_lt hsig)
  have hprod : Real.sqrt sigma * energyBracket sigma pow Kg KhInf Kh =
      sigma * dataBracket sigma pow Kg KhInf Kh := by
    rw [← hkey, ← mul_assoc, hsq]
  rw [hprod, mul_comm, mul_div_assoc, div_self (ne_of_gt hsig), mul_one]

/-- The Step-3a `σ̄` bookkeeping at GENERAL data: `√σ̄ ·
(data-general majorant)` is the printed `σ̄ · dataBracket` form. -/
theorem sqrt_mul_homStepTwoMajorantData (Cr Xfac Eq : ℝ) {sigma : ℝ} (hsig : 0 < sigma)
    (pow Kg KhInf Kh : ℝ) :
    Real.sqrt sigma * homStepTwoMajorantData Cr Xfac Eq sigma pow Kg KhInf Kh =
      Cr * Xfac * (1 + Eq) * (sigma * dataBracket sigma pow Kg KhInf Kh) := by
  have hkey : Real.sqrt sigma * dataBracket sigma pow Kg KhInf Kh =
      energyBracket sigma pow Kg KhInf Kh :=
    sqrt_mul_dataBracket sigma pow Kg KhInf Kh hsig
  have hsq : Real.sqrt sigma * Real.sqrt sigma = sigma :=
    Real.mul_self_sqrt (le_of_lt hsig)
  have hprod : Real.sqrt sigma * energyBracket sigma pow Kg KhInf Kh =
      sigma * dataBracket sigma pow Kg KhInf Kh := by
    rw [← hkey, ← mul_assoc, hsq]
  rw [homStepTwoMajorantData]
  calc Real.sqrt sigma * (Cr * Xfac * (1 + Eq) * energyBracket sigma pow Kg KhInf Kh)
      = Cr * Xfac * (1 + Eq) *
          (Real.sqrt sigma * energyBracket sigma pow Kg KhInf Kh) := by ring
    _ = Cr * Xfac * (1 + Eq) * (sigma * dataBracket sigma pow Kg KhInf Kh) := by
        rw [hprod]

/-! ## 2. The `s₁` weight gap: the borderline and the pin -/

/-- **The `s₁ = s/2` BORDERLINE, displayed.**  The printed energy weight
`3^{-(s-s₁)p i}` and the Step-2b growth `3^{(1-α) i} = 3^{(s/2) i}` cancel
EXACTLY at the manuscript's `s₁ = s/2`: the gap `(s - s₁) - s/2` is zero, so the
`ℓ^p` slot's summands do not decay and no `S`-bound survives the partial
sums. -/
theorem stepTwo_weightGap_borderline (s : ℝ) : (s - s / 2) - s / 2 = 0 := by ring

/-- **The `s₁ = s/4` PIN, displayed.**  The same gap at `s₁ = s/4` is `s/4 > 0`,
so the slot converges.  `s/4 ∈ (0,s)` is inside the printed range of `s₁` in
the general coarse-graining proposition itself, so this is a choice the source offers, not a
statement change. -/
theorem stepTwo_weightGap_quarterPin {s : ℝ} (hs : 0 < s) :
    (s - s / 4) - s / 2 = s / 4 ∧ 0 < (s - s / 4) - s / 2 := by
  refine ⟨by ring, ?_⟩
  have h : (s - s / 4) - s / 2 = s / 4 := by ring
  rw [h]
  linarith only [hs]

/-- `s/4` lies in the printed range `(0, s)` of `s₁`. -/
theorem quarterPin_mem_printedRange {s : ℝ} (hs : 0 < s) : 0 < s / 4 ∧ s / 4 < s := by
  constructor
  · linarith only [hs]
  · linarith only [hs]

/-! ## 3. The energy slot from a WEIGHTED Step-2b family bound -/

/-- **The finite-`p` energy slot from the WEIGHTED Step-2b datum.**

The `coarseGrainingEnergyPartial_le_of_bound` asks for a UNIFORM per-cube bound
`Gen R ≤ S`.  What Step 2b delivers is `Gen R ≤ S·3^{a i}` at depth `jn + i`.
As long as the printed weight strictly dominates that growth (`a < w`, i.e. `s₁
< s - (1-α)`), the slot is still bounded by `S` times an explicit geometric
factor, now at the GAP exponent `w - a`.

`Gen` is abstract here: no coefficient field, no `ν`, no `σ̄` (see the module
docstring's seam disclosure). -/
theorem coarseGrainingEnergyPartial_le_of_weightedBound {Q : TriadicCube d}
    {p w a S : ℝ} {jn N : ℕ} {Gen : TriadicCube d → ℝ}
    (hp : 0 < p) (haw : a < w) (hS : 0 ≤ S)
    (hG : ∀ i : ℕ, ∀ R ∈ descendantsAtDepth Q (jn + i),
      Gen R ≤ S * (3 : ℝ) ^ (a * (i : ℝ)))
    (hG0 : ∀ R : TriadicCube d, 0 ≤ Gen R) :
    coarseGrainingEnergyPartial Q p w jn N Gen ≤ S * coarseGrainingGeomFactor p (w - a) := by
  classical
  have hgap : 0 < w - a := by linarith only [haw]
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-((w - a) * p)) := three_rpow_pos _
  have hr1 : (3 : ℝ) ^ (-((w - a) * p)) < 1 :=
    three_rpow_neg_lt_one (mul_pos hgap hp)
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-((w - a) * p)) := by linarith only [hr1]
  have hSp : (0 : ℝ) ≤ S ^ p := Real.rpow_nonneg hS p
  /- each depth average is at most `S^p · 3^{a i p}` -/
  have hdepth : ∀ i : ℕ,
      (descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
        S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p) := by
    intro i
    have hcell : ∀ R ∈ descendantsAtDepth Q (jn + i),
        Gen R ^ p ≤ S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p) := by
      intro R hR
      have h1 : Gen R ^ p ≤ (S * (3 : ℝ) ^ (a * (i : ℝ))) ^ p :=
        Real.rpow_le_rpow (hG0 R) (hG i R hR) hp.le
      refine h1.trans (le_of_eq ?_)
      rw [Real.mul_rpow hS (three_rpow_nonneg _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hmono := descendantsAverage_le_descendantsAverage Q (jn + i)
      (F := fun R => Gen R ^ p) (G := fun _ => S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p)) hcell
    rwa [descendantsAverage_const_eq Q (jn + i) (S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p))] at hmono
  have hdepth0 : ∀ i : ℕ, (0 : ℝ) ≤ descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
    fun i => descendantsAverage_nonneg Q (jn + i) _
      fun R _ => Real.rpow_nonneg (hG0 R) p
  /- the weighted summand is a geometric term at the GAP expone -/
  have hkey : ∀ i : ℕ,
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          (descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
        ((3 : ℝ) ^ (-((w - a) * p))) ^ i * S ^ p := by
    intro i
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(w * p) * (i : ℝ)) := three_rpow_nonneg _
    have hmerge : (3 : ℝ) ^ (-(w * p) * (i : ℝ)) * (3 : ℝ) ^ (a * (i : ℝ) * p) =
        ((3 : ℝ) ^ (-((w - a) * p))) ^ i := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_natCast ((3 : ℝ) ^ (-((w - a) * p))) i,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          (descendantsAverage Q (jn + i) fun R => Gen R ^ p)
        ≤ (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
            (S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p)) :=
          mul_le_mul_of_nonneg_left (hdepth i) hw0
      _ = ((3 : ℝ) ^ (-(w * p) * (i : ℝ)) * (3 : ℝ) ^ (a * (i : ℝ) * p)) * S ^ p := by ring
      _ = ((3 : ℝ) ^ (-((w - a) * p))) ^ i * S ^ p := by rw [hmerge]
  have hsum : (∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
      S ^ p * (1 - (3 : ℝ) ^ (-((w - a) * p)))⁻¹ := by
    calc (∑ i ∈ Finset.range (N + 1),
          (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
            descendantsAverage Q (jn + i) fun R => Gen R ^ p)
        ≤ ∑ i ∈ Finset.range (N + 1),
            ((3 : ℝ) ^ (-((w - a) * p))) ^ i * S ^ p :=
          Finset.sum_le_sum fun i _ => hkey i
      _ ≤ S ^ p * (1 - (3 : ℝ) ^ (-((w - a) * p)))⁻¹ :=
          sum_geom_weighted_le hr0.le hr1 hSp (fun _ => le_rfl) N
  have hnnsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (three_rpow_nonneg _) (hdepth0 i)
  have hfin : coarseGrainingEnergyPartial Q p w jn N Gen ≤
      (S ^ p * (1 - (3 : ℝ) ^ (-((w - a) * p)))⁻¹) ^ (1 / p) := by
    rw [coarseGrainingEnergyPartial_def]
    exact Real.rpow_le_rpow hnnsum hsum (one_div_nonneg.mpr hp.le)
  refine hfin.trans (le_of_eq ?_)
  rw [Real.mul_rpow hSp (inv_nonneg.mpr hden.le), ← Real.rpow_mul hS,
    mul_one_div_cancel (ne_of_gt hp), Real.rpow_one, coarseGrainingGeomFactor_def]

/-- **The energy slot at the `s₁ = s/4` pin.**

The Step-2b family grows like `3^{(s/2) i}` (the §4.5 web's `1 - α = s/2`), the
printed weight at `s₁ = s/4` is `3^{-(3s/4)p i}`, and the gap is `s/4 > 0`.
This is the instance of `coarseGrainingEnergyPartial_le_of_weightedBound` the
Step-3/Step-4 chain consumes; the printed `s₁ = s/2` would give gap `0`
(`stepTwo_weightGap_borderline`) and no bound. -/
theorem coarseGrainingEnergyPartial_le_at_quarterPin {Q : TriadicCube d}
    {p s S : ℝ} {jn N : ℕ} {Gen : TriadicCube d → ℝ}
    (hp : 0 < p) (hs : 0 < s) (hS : 0 ≤ S)
    (hG : ∀ i : ℕ, ∀ R ∈ descendantsAtDepth Q (jn + i),
      Gen R ≤ S * (3 : ℝ) ^ (s / 2 * (i : ℝ)))
    (hG0 : ∀ R : TriadicCube d, 0 ≤ Gen R) :
    coarseGrainingEnergyPartial Q p (s - s / 4) jn N Gen ≤
      S * coarseGrainingGeomFactor p (s / 4) := by
  have hgap : (s - s / 4) - s / 2 = s / 4 := by ring
  have haw : s / 2 < s - s / 4 := by linarith only [hs]
  have hmain := coarseGrainingEnergyPartial_le_of_weightedBound (Q := Q) (p := p)
    (w := s - s / 4) (a := s / 2) (S := S) (jn := jn) (N := N) (Gen := Gen) hp haw hS hG hG0
  rwa [hgap] at hmain

end

end Algsuperdiff.Section4.Provider.Homogenization
