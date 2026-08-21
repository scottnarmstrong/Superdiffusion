/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomFinitePGauge
import Algsuperdiff.Section4.Provider.Homogenization.HomStepFourPairing

/-!
# the general coarse-graining proposition at finite `p`: the transcribed source hypothesis

## THE CONDITIONAL EDGE — `hCG'`, transcribed, NOT proved here

The general coarse-graining proposition is a declared dependency and a declared
source hypothesis of the Step-3a node of Theorem B. It is a **hypothesis** of
this tree, exactly as `hCG` and `hC` are entered elsewhere in it.  Nothing
below proves it; `GeneralCoarseGrainingFiniteP` is the named transcription, and
every consumer carries it as an explicit binder.

This file replaces the `hCG` hypothesis (the *`p → ∞`* reading) by the
**printed finite-`p` proposition**:

> Let `m,n ∈ ℤ` with `n < m`, `𝐚: □_m → ℝ^{d×d}_+` uniformly elliptic and
> `σ₀ ∈ (0,∞)`.  Fix `p ∈ [2,∞)` and `s, s₁, s₂ ∈ (0,1)` with `s₁ < s < s₂ < 1`.
> There is `C(p,d) < ∞` such that for every `𝐠 ∈ W^{s₂,p}(□_m;ℝ^d)` and every
> pair `u, v ∈ H¹(□_m)` with `-∇·𝐚∇u = ∇·𝐠`, `-∇·σ₀∇v = ∇·𝐠` in `□_m` and
> `u - v ∈ H¹₀(□_m)`,
>
> ```text
>   3^{-ms} σ₀ ‖∇u - ∇v‖_{Ŵ̲^{-s,p}(□_m)} + 3^{-ms} ‖𝐚∇u - σ₀∇v‖_{Ŵ̲^{-s,p}(□_m)}
>     ≤ C s^{-1} σ₀^{1/2} 𝓔_{s₁,∞,1}(□_m,n;𝐚,σ₀)
>         ( Σ_{k ≤ n} 3^{-(s-s₁)p(n-k)} avsum_{z ∈ 3^k ℤ^d ∩ □_m}
>              ‖σ^{1/2}∇u‖_{L̲²(z+□_k)}^p )^{1/p}
>       + C s^{-9/2} (s₂-s)^{-1} (1 + 𝓔²_{s₁/2,∞,2}(□_m,n;𝐚,σ₀))
>           3^{s₂ n} [𝐠]_{W̲^{s₂,p}(□_m)}.
> ```

No extension, no `p`-limit and no correction is used: `p = 4d` is inside the
printed range `[2,∞)`, and `C(p,d)` is the printed constant.

## Which parts are pinned, and which are carried abstractly

Following the established conditional-edge device (the
`stepThreeCoarseGraining_of_display`), the objects this file does **not**
consume are carried as abstract reals: the coefficient field, the two `𝓔`
quantities (`E1`, `E2`), the forcing seminorm (`Dg`), the constant (`Ccg`) and
the elliptic pair itself.  Two things ARE pinned, because they are consumed:

* the **energy slot** — the printed `ℓ^p` sum over the printed grid, at
  `coarseGrainingEnergyPartial`: the grid of the sum is the pure lattice
  `3^k ℤ^d ∩ □_m`, i.e. `CoarseGraining`'s `descendantsAtDepth`, and the outer index is a
  partial sum (no summability side hypothesis);
* the **left-hand negative norms**, at BOTH readings — see next.

## TWO READINGS, both transcribed

The manuscript never defines `‖·‖_{Ŵ̲^{-s,p}(□_m)}` (the manuscript defines
only the order `-1` duals).  The correction records — machine-checked  — that
the two consumption sites need **inequivalent** objects:

* Step 3c (the `L^∞` upgrade) needs the **multiscale** reading: a single-scale
  duality bound loses `r^{-d}`;
* Step 4 (the pairing) needs the **duality** reading:
  pairing a Hölder test field against the multiscale depth maxima diverges
  logarithmically over the triadic depths.

Neither implies the other.  The honest transcription of ONE printed display
whose symbol is undefined is therefore a hypothesis carrying **both** readings
of that display, which is what `GeneralCoarseGrainingFiniteP` does.  Its
multiscale clause is the finite-`p` grid carrier of `HomFinitePGauge`; its
duality clauses are the `WeakNegDualBoundOn` at the two printed levels.  No
clause is derived from another anywhere in this tree, and the disclosure
travels with every consumer.

## Main definitions and results

* `coarseGrainingEnergyPartial` — the printed `ℓ^p` mesoscale energy slot;
* `coarseGrainingFinitePRHS` — the printed right-hand side;
* `GeneralCoarseGrainingFiniteP` — **the transcribed hypothesis** `hCG'`;
* `GeneralCoarseGrainingFiniteP.multiscale`, `.dualGrad`, `.dualFlux` — the
  three per-site projections;
* `coarseGrainingEnergyPartial_le_of_bound` — the finite-`p` energy slot is
  bounded by the SAME Step-2b sup datum the `p = ∞` route used, at the
  explicit geometric factor `(1 - 3^{-(s-s₁)p})^{-1/p}`;
* `weakNegDualBounds_of_coarseGraining` — the Step-4 supply: the two exact
  `WeakNegDualBoundOn` slots from `hCG'` in one application.
-/

open Homogenization Homogenization.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The printed `ℓ^p` mesoscale energy slot -/

/-- **The printed energy slot**, as a partial sum.

With `k = n - i` and the mesoscale depth `jn = m - n`, the printed
`Σ_{k ≤ n} 3^{-(s-s₁)p(n-k)} avsum_{z ∈ 3^k ℤ^d ∩ □_m} G(z+□_k)^p` becomes a
sum over `i ≥ 0` of `3^{-(w p) i}` times the depth-`(jn + i)` grid average of
`G^p`, where `w = s - s₁`.  The grid is the printed one: the pure lattice,
i.e. `CoarseGraining`'s `descendantsAtDepth`. -/
def coarseGrainingEnergyPartial (Q : TriadicCube d) (p w : ℝ) (jn N : ℕ)
    (Gen : TriadicCube d → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p) ^ (1 / p)

theorem coarseGrainingEnergyPartial_def (Q : TriadicCube d) (p w : ℝ) (jn N : ℕ)
    (Gen : TriadicCube d → ℝ) :
    coarseGrainingEnergyPartial Q p w jn N Gen =
      (∑ i ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          descendantsAverage Q (jn + i) fun R => Gen R ^ p) ^ (1 / p) := rfl

/-- **The printed right-hand side**, with the energy slot
supplied as the abstract upper bound `S`.

Every factor is the printed one: `C s^{-1} σ₀^{1/2} 𝓔₁ · S` and
`C s^{-9/2} (s₂-s)^{-1} (1 + 𝓔₂²) · 3^{s₂ n} [𝐠]`. -/
def coarseGrainingFinitePRHS (Ccg s s2 sigma E1 E2 Dg S : ℝ) (n : ℤ) : ℝ :=
  Ccg * s⁻¹ * Real.sqrt sigma * E1 * S +
    Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)

theorem coarseGrainingFinitePRHS_def (Ccg s s2 sigma E1 E2 Dg S : ℝ) (n : ℤ) :
    coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n =
      Ccg * s⁻¹ * Real.sqrt sigma * E1 * S +
        Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) := rfl

/-! ## 2. `hCG'` — the transcribed source hypothesis -/

/-- **the general coarse-graining proposition at finite `p`, transcribed**.

`Q = □_m` is the window, `jn = m - n` the mesoscale depth, `Fgrad = ∇u - ∇v`,
`Fflux = 𝐚∇u - σ₀∇v`, `Gen R = ‖σ^{1/2}∇u‖_{L̲²(R)}` the printed per-cube
energy, and `Ccg = C(p,d)` the printed constant.

The display is asserted at both readings of its undefined left-hand symbol:

* clause 1 (**multiscale**, consumed at Step 3c): the finite-`p` grid gauge of
  `HomFinitePGauge`, at the printed combination `σ₀·(gradient) + (flux)`;
* clauses 2 and 3 (**duality**, consumed at Step 4): the `WeakNegDualBoundOn`
  for each leg at the level the same display gives it, i.e. `3^{ms}σ₀^{-1}·RHS`
  for the gradient and `3^{ms}·RHS` for the flux.

THIS IS A HYPOTHESIS.  It is never proved in this repository. -/
def GeneralCoarseGrainingFiniteP (Q : TriadicCube d) (jn : ℕ)
    (Ccg s s1 s2 p sigma E1 E2 Dg : ℝ)
    (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d) : Prop :=
  ∀ S : ℝ, (∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) →
    (∀ N : ℕ,
        sigma * negBesovLpPartialNorm Q s p N Fgrad +
            negBesovLpPartialNorm Q s p N Fflux ≤
          coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))) ∧
      WeakNegDualBoundOn Q s
        ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * sigma⁻¹ *
          coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))) Fgrad ∧
      WeakNegDualBoundOn Q s
        ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
          coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))) Fflux

/-- The multiscale clause: the Step-3c reading. -/
theorem GeneralCoarseGrainingFiniteP.multiscale {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : GeneralCoarseGrainingFiniteP Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) (N : ℕ) :
    sigma * negBesovLpPartialNorm Q s p N Fgrad + negBesovLpPartialNorm Q s p N Fflux ≤
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) :=
  (h S hS).1 N

/-- The gradient duality clause: the Step-4 reading. -/
theorem GeneralCoarseGrainingFiniteP.dualGrad {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : GeneralCoarseGrainingFiniteP Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) :
    WeakNegDualBoundOn Q s
      ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * sigma⁻¹ *
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))) Fgrad :=
  (h S hS).2.1

/-- The flux duality clause: the Step-4 reading. -/
theorem GeneralCoarseGrainingFiniteP.dualFlux {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : GeneralCoarseGrainingFiniteP Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) :
    WeakNegDualBoundOn Q s
      ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))) Fflux :=
  (h S hS).2.2

/-- The single gradient leg of the multiscale clause, with the flux leg
discarded — the source's own route (ii) in the paper, "we just discarded it". -/
theorem GeneralCoarseGrainingFiniteP.gradPartial {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : GeneralCoarseGrainingFiniteP Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S)
    (hsigma : 0 < sigma) (N : ℕ) :
    negBesovLpPartialNorm Q s p N Fgrad ≤
      sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
  have hflux : (0 : ℝ) ≤ negBesovLpPartialNorm Q s p N Fflux :=
    negBesovLpPartialNorm_nonneg Q s p N Fflux
  have hmain := h.multiscale hS N
  have hstep : sigma * negBesovLpPartialNorm Q s p N Fgrad ≤
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
    linarith only [hmain, hflux]
  have hne : sigma ≠ 0 := ne_of_gt hsigma
  calc negBesovLpPartialNorm Q s p N Fgrad
      = sigma⁻¹ * (sigma * negBesovLpPartialNorm Q s p N Fgrad) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hsigma.le)

/-! ## 3. The energy slot is fed by the SAME Step-2b datum as the `p = ∞` route -/

/-- The geometric factor the finite-`p` energy slot pays over the `p = ∞` sup:
`(1 - 3^{-(s-s₁)p})^{-1/p}`. -/
def coarseGrainingGeomFactor (p w : ℝ) : ℝ :=
  ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p)

theorem coarseGrainingGeomFactor_def (p w : ℝ) :
    coarseGrainingGeomFactor p w = ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p) := rfl

/-- The geometric ratio `3^{-(w p)}` lies in `(0,1)` when `w, p > 0`. -/
theorem three_rpow_neg_lt_one {t : ℝ} (ht : 0 < t) : (3 : ℝ) ^ (-t) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ht])

/-- The truncated geometric series is below `(1-r)^{-1}`. -/
theorem geom_sum_range_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), r ^ i) ≤ (1 - r)⁻¹ := by
  have hden : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hid : (∑ i ∈ Finset.range (N + 1), r ^ i) * (1 - r) = 1 - r ^ (N + 1) := by
    have h := geom_sum_mul r (N + 1)
    have hneg : (∑ i ∈ Finset.range (N + 1), r ^ i) * (1 - r) =
        -((∑ i ∈ Finset.range (N + 1), r ^ i) * (r - 1)) := by ring
    rw [hneg, h]
    ring
  have hnn : (0 : ℝ) ≤ r ^ (N + 1) := pow_nonneg hr0 _
  rw [show (1 - r)⁻¹ = 1 / (1 - r) by rw [one_div], le_div_iff₀ hden, hid]
  linarith only [hnn]

/-- The weighted geometric sum bound used by the energy slot. -/
theorem sum_geom_weighted_le {r B : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hB : 0 ≤ B)
    {a : ℕ → ℝ} (haB : ∀ i, a i ≤ B) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), r ^ i * a i) ≤ B * (1 - r)⁻¹ := by
  have hden : (0 : ℝ) < 1 - r := by linarith only [hr1]
  calc (∑ i ∈ Finset.range (N + 1), r ^ i * a i)
      ≤ ∑ i ∈ Finset.range (N + 1), r ^ i * B :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (haB i) (pow_nonneg hr0 i)
    _ = (∑ i ∈ Finset.range (N + 1), r ^ i) * B := by rw [Finset.sum_mul]
    _ ≤ (1 - r)⁻¹ * B :=
        mul_le_mul_of_nonneg_right (geom_sum_range_le_inv_one_sub hr0 hr1 N) hB
    _ = B * (1 - r)⁻¹ := by ring

/-- **The finite-`p` energy slot, fed by the `p = ∞` datum.**

If the printed per-cube energy `Gen` is at most `S` on every grid cell at every
depth the sum reaches, then the whole `ℓ^p` slot is at most `S · (1 -
3^{-(s-s₁)p})^{-1/p}`.  So the finite-`p` proposition consumes EXACTLY the
Step-2b family bound the `p = ∞` route consumed (the `stepThreeSupBound`), at
one displayed extra factor and nothing else. -/
theorem coarseGrainingEnergyPartial_le_of_bound {Q : TriadicCube d} {p w S : ℝ}
    {jn N : ℕ} {Gen : TriadicCube d → ℝ} (hp : 0 < p) (hw : 0 < w) (hS : 0 ≤ S)
    (hG : ∀ i : ℕ, ∀ R ∈ descendantsAtDepth Q (jn + i), Gen R ≤ S)
    (hG0 : ∀ R : TriadicCube d, 0 ≤ Gen R) :
    coarseGrainingEnergyPartial Q p w jn N Gen ≤ S * coarseGrainingGeomFactor p w := by
  classical
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(w * p)) := three_rpow_pos _
  have hr1 : (3 : ℝ) ^ (-(w * p)) < 1 := three_rpow_neg_lt_one (mul_pos hw hp)
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(w * p)) := by linarith only [hr1]
  have hSp : (0 : ℝ) ≤ S ^ p := Real.rpow_nonneg hS p
  /- each depth average is at most `S ^ p` -/
  have hdepth : ∀ i : ℕ,
      (descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤ S ^ p := by
    intro i
    have hmono := descendantsAverage_le_descendantsAverage Q (jn + i)
      (F := fun R => Gen R ^ p) (G := fun _ => S ^ p)
      (fun R hR => Real.rpow_le_rpow (hG0 R) (hG i R hR) hp.le)
    rwa [descendantsAverage_const_eq Q (jn + i) (S ^ p)] at hmono
  have hdepth0 : ∀ i : ℕ, (0 : ℝ) ≤ descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
    fun i => descendantsAverage_nonneg Q (jn + i) _
      fun R _ => Real.rpow_nonneg (hG0 R) p
  /- the weight is a geometric rat -/
  have hpow : ∀ i : ℕ,
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) = ((3 : ℝ) ^ (-(w * p))) ^ i := by
    intro i
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(w * p))) i,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hsum : (∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
      S ^ p * (1 - (3 : ℝ) ^ (-(w * p)))⁻¹ := by
    have hrw : (∑ i ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          descendantsAverage Q (jn + i) fun R => Gen R ^ p) =
        ∑ i ∈ Finset.range (N + 1), ((3 : ℝ) ^ (-(w * p))) ^ i *
          descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
      Finset.sum_congr rfl fun i _ => by rw [hpow i]
    rw [hrw]
    exact sum_geom_weighted_le hr0.le hr1 hSp hdepth N
  have hnnsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (three_rpow_nonneg _) (hdepth0 i)
  have hfin : coarseGrainingEnergyPartial Q p w jn N Gen ≤
      (S ^ p * (1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p) := by
    rw [coarseGrainingEnergyPartial_def]
    exact Real.rpow_le_rpow hnnsum hsum (one_div_nonneg.mpr hp.le)
  refine hfin.trans (le_of_eq ?_)
  rw [Real.mul_rpow hSp (inv_nonneg.mpr hden.le), ← Real.rpow_mul hS,
    mul_one_div_cancel (ne_of_gt hp), Real.rpow_one, coarseGrainingGeomFactor_def]

/-! ## 4. The Step-4 supply, in one application -/

/-- **the two `WeakNegDualBoundOn` slots, from `hCG'`.**

The `stepFourEnergyDisplay` consumes the flux leg at level `3^{ms}·σ₀·(C_w E_B
D)` and the gradient leg at level `3^{ms}·(C_w E_B D)`. Both are the printed
display's own levels, transported by `WeakNegDualBoundOn.mono`, as soon as the
printed right-hand side is below `σ₀·(C_w E_B D)` — the single arithmetic
condition.  This is the whole Step-4 half of the coarse-graining application.

Disclosure: the duality clauses of `GeneralCoarseGrainingFiniteP` are the
DUALITY reading of the undefined printed symbol; the correction records that
this reading is inequivalent to the multiscale reading consumed at Step 3c, and
that the source hypothesis must carry both. -/
theorem weakNegDualBounds_of_coarseGraining {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg S Level : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d} (hsigma : 0 < sigma)
    (h : GeneralCoarseGrainingFiniteP Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S)
    (hlevel : coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) ≤
      sigma * Level) :
    WeakNegDualBoundOn Q s
        ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * sigma * Level) Fflux ∧
      WeakNegDualBoundOn Q s ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * Level) Fgrad := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) := three_rpow_nonneg _
  have hgradLevel : sigma⁻¹ *
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) ≤ Level := by
    have hstep := mul_le_mul_of_nonneg_left hlevel (inv_nonneg.mpr hsigma.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsigma), one_mul] at hstep
  refine ⟨(h.dualFlux hS).mono ?_, (h.dualGrad hS).mono ?_⟩
  · calc (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
          coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))
        ≤ (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * (sigma * Level) :=
          mul_le_mul_of_nonneg_left hlevel h3
      _ = (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * sigma * Level := by ring
  · calc (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * sigma⁻¹ *
          coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))
        = (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
            (sigma⁻¹ *
              coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))) := by
          ring
      _ ≤ (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) * Level :=
          mul_le_mul_of_nonneg_left hgradLevel h3

end

end Algsuperdiff.Section4.Provider.Homogenization
