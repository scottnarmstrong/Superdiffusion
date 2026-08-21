/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStabilityEndpoints
import Algsuperdiff.Section4.Provider.ExcessDecay.MeanControlWindowCube

/-!
# The mean comparison, step 2: the homogenization-error split, and its loop-free
account

## What is proved

The single number `S` is controlled by the homogenization error.  That
mechanism is reduced here to its exact arithmetic skeleton and machine-checked.
With

```text
  ρ = u − h ,   V₁ = the covering cube c+□_{n+2} ,
  V₂ = the boundary-flush cube of MeanControlWindowCube ,
  W  = the frozen window (z+□_{n+3}) ∩ □_m ⊇ V₁ ∪ V₂ ,
```

and comparators `v̄` (any function on `V₂`; intended: the `Δ`-harmonic
replacement of `u` there) and `h̄` (intended: the `Δ`-harmonic replacement of the
datum `h`), the module proves

```text
  S = |⨍_{V₁} ρ|
      ≤ (r₁ + r₂)·‖ρ − (ρ)_W‖_{L̲²(W)}          (§1, §4: two window transfers)
        + ‖u − v̄‖_{L̲²(V₂)}                      (the homogenization error)
        + ‖h̄ − h‖_{L̲²(V₂)}                      (the datum comparator, data-only)
        + |⨍_{V₂} (v̄ − h̄)| ,                     (§2: THE remaining scalar)
```

```text
  ‖(v̄ − h̄) − (v̄ − h̄)_{V₂}‖_{L̲²(V₂)}
      ≤ 2‖u − v̄‖ + 2‖h − h̄‖ + ‖u − (u)_{V₂}‖ + ‖h − (h)_{V₂}‖      (§3, §5)
```

## What this buys, and what remains

Every summand except the last is a frozen-statement leg or a legal data step:
the window oscillation of `ρ` splits into the frozen leg `‖u − (u)_W‖` and the
datum oscillation `‖h − (h)_W‖` (the mean-zero Poincaré on the datum), and
`‖h̄ − h‖` is a Dirichlet-comparison step on
the datum alone.  The single remaining analytic obligation is

```text
  |⨍_{V₂} (v̄ − h̄)| ≤ C(d) · ‖(v̄ − h̄) − (v̄ − h̄)_{V₂}‖_{L̲²(V₂)}
```

for the `Δ`-harmonic difference `v̄ − h̄` on the **boundary-flush** cube `V₂`,
whose trace vanishes on the face `V₂` shares with `∂□_m` (that face exists by
`MeanControlWindowCube.wellPlacedCentre_faceLevel`, and `u − h ∈ H¹₀(□_m)`).
That obligation is a statement about `Δ`-harmonic functions and Lebesgue
measure alone (the comparator class of `BoundaryLaneMaxPrinciple`), so flat
estimates suffice for it.  §6 records the arithmetic that converts the
boundary-trace form of that obligation into the stated form.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open Homogenization
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 0. Elementary identities for the normalized average -/

/-- The volume average of a constant is that constant. -/
theorem volumeAverage_const_of_toReal_pos {V : Set (Vec d)}
    (hVpos : 0 < (volume V).toReal) (b : ℝ) :
    volumeAverage V (fun _ => b) = b := by
  have hVne : ((volume V).toReal) ≠ 0 := ne_of_gt hVpos
  have hconst : ∫ _x in V, b ∂volume = (volume V).toReal * b := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
  unfold volumeAverage
  rw [hconst, ← mul_assoc, inv_mul_cancel₀ hVne, one_mul]

/-- The normalized seminorm of a constant is its absolute value. -/
theorem normalizedL2On_const_abs {V : Set (Vec d)} (hVpos : 0 < (volume V).toReal)
    (b : ℝ) : normalizedL2On V (fun _ => b) = |b| := by
  have hconst : volumeAverage V (fun _ => b ^ 2) = b ^ 2 :=
    volumeAverage_const_of_toReal_pos hVpos (b ^ 2)
  unfold normalizedL2On
  rw [hconst, Real.sqrt_sq_eq_abs]

/-- The volume average is additive on integrable summands. -/
theorem volumeAverage_add_eq {V : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (hg : IntegrableOn g V volume) :
    volumeAverage V (fun x => f x + g x) =
      volumeAverage V f + volumeAverage V g := by
  unfold volumeAverage
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- The volume average is additive on integrable differences. -/
theorem volumeAverage_sub_eq {V : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (hg : IntegrableOn g V volume) :
    volumeAverage V (fun x => f x - g x) =
      volumeAverage V f - volumeAverage V g := by
  unfold volumeAverage
  rw [MeasureTheory.integral_sub hf hg]
  ring

/-- Subtracting a constant shifts the volume average by that constant. -/
theorem volumeAverage_sub_const_eq {V : Set (Vec d)}
    (hVpos : 0 < (volume V).toReal) (hVtop : volume V ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (c : ℝ) :
    volumeAverage V (fun x => f x - c) = volumeAverage V f - c := by
  haveI : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have hc : IntegrableOn (fun _ : Vec d => c) V volume := MeasureTheory.integrable_const c
  rw [volumeAverage_sub_eq hf hc, volumeAverage_const_of_toReal_pos hVpos]

/-! ## 1. The two-window mean transfer -/

/-- **The mean transfer.**

For a subwindow `V ⊆ W`, the gap between the two normalized means is at most the
oscillation of `f` on the big window, at the square root of the volume ratio.
No equation, no coefficient field: Jensen on `V` followed by the volume-ratio
comparison of the normalized seminorms. -/
theorem abs_volumeAverage_sub_windowAverage_le {W V : Set (Vec d)}
    (hVm : MeasurableSet V) (hsub : V ⊆ W)
    (hWpos : 0 < (volume W).toReal) (hVpos : 0 < (volume V).toReal)
    (hVtop : volume V ≠ ⊤) {f : Vec d → ℝ} (hfV : IntegrableOn f V volume)
    (hfV2 : IntegrableOn (fun x => (f x - volumeAverage W f) ^ 2) V volume)
    (hfW2 : IntegrableOn (fun x => (f x - volumeAverage W f) ^ 2) W volume) :
    |volumeAverage V f - volumeAverage W f| ≤
      Real.sqrt ((volume W).toReal / (volume V).toReal) *
        normalizedL2On W (fun x => f x - volumeAverage W f) := by
  haveI : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have hc : IntegrableOn (fun _ : Vec d => volumeAverage W f) V volume :=
    MeasureTheory.integrable_const _
  have hsubint : IntegrableOn (fun x => f x - volumeAverage W f) V volume := hfV.sub hc
  have hJ := abs_volumeAverage_le_normalizedL2On hVm hVpos hsubint hfV2
  rw [volumeAverage_sub_const_eq hVpos hVtop hfV] at hJ
  exact hJ.trans (normalizedL2On_le_of_subset hsub hWpos hVpos hfW2)

/-! ## 2. The split through the comparators -/

/-- **The split.**

`u − h = (u − v̄) + (h̄ − h) + (v̄ − h̄)` pointwise, so the mean of `u − h` over
the flush cube is controlled by the homogenization error `‖u − v̄‖`, the datum
comparison `‖h̄ − h‖`, and the mean of the comparator difference `v̄ − h̄`.

The first two summands are the pieces the proved machinery prices; the third is
the single remaining analytic obligation, and it is a statement about the
comparators alone. -/
theorem abs_volumeAverage_sub_le_comparatorSplit {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal)
    {u h vbar hbar : Vec d → ℝ}
    (huv : IntegrableOn (fun x => u x - vbar x) V volume)
    (hhh : IntegrableOn (fun x => hbar x - h x) V volume)
    (hvh : IntegrableOn (fun x => vbar x - hbar x) V volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V volume)
    (hhh2 : IntegrableOn (fun x => (hbar x - h x) ^ 2) V volume) :
    |volumeAverage V (fun x => u x - h x)| ≤
      normalizedL2On V (fun x => u x - vbar x) +
        normalizedL2On V (fun x => hbar x - h x) +
        |volumeAverage V (fun x => vbar x - hbar x)| := by
  have hdecomp : (fun x => u x - h x) =
      fun x => ((u x - vbar x) + (hbar x - h x)) + (vbar x - hbar x) := by
    funext x; ring
  have hsum : IntegrableOn (fun x => (u x - vbar x) + (hbar x - h x)) V volume :=
    huv.add hhh
  rw [hdecomp, volumeAverage_add_eq hsum hvh, volumeAverage_add_eq huv hhh]
  have hJ1 := abs_volumeAverage_le_normalizedL2On hVm hVpos huv huv2
  have hJ2 := abs_volumeAverage_le_normalizedL2On hVm hVpos hhh hhh2
  have habs := abs_add_le (volumeAverage V (fun x => u x - vbar x) +
    volumeAverage V (fun x => hbar x - h x)) (volumeAverage V (fun x => vbar x - hbar x))
  have habs2 := abs_add_le (volumeAverage V (fun x => u x - vbar x))
    (volumeAverage V (fun x => hbar x - h x))
  linarith only [habs, habs2, hJ1, hJ2]

/-! ## 3. The oscillation of a comparator -/

/-- **The comparator's oscillation, in terms of the original's.**

`‖v̄ − (v̄)_V‖ ≤ 2‖u − v̄‖ + ‖u − (u)_V‖`: the comparator oscillates no more than
the original does, up to twice the comparison error.  The proof is Minkowski
with the constant `(u)_V` inserted, plus Jensen on the mean gap; mean-minimality
is deliberately **not** used, so that the module needs no Pythagoras identity and
its import cone stays minimal. -/
theorem oscillation_comparator_le {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal) (hVtop : volume V ≠ ⊤)
    {u vbar : Vec d → ℝ} (hu : IntegrableOn u V volume)
    (hv : IntegrableOn vbar V volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V volume)
    (hvuM : MemLp (fun x => vbar x - u x) 2 (volume.restrict V))
    (hoscM : MemLp (fun x => u x - volumeAverage V u) 2 (volume.restrict V)) :
    normalizedL2On V (fun x => vbar x - volumeAverage V vbar) ≤
      2 * normalizedL2On V (fun x => u x - vbar x) +
        normalizedL2On V (fun x => u x - volumeAverage V u) := by
  haveI : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have huv : IntegrableOn (fun x => u x - vbar x) V volume := hu.sub hv
  have hconstM : MemLp (fun _ : Vec d => volumeAverage V u - volumeAverage V vbar) 2
      (volume.restrict V) := memLp_const _
  have hdecomp : (fun x => vbar x - volumeAverage V vbar) =
      fun x => (vbar x - u x) +
        ((u x - volumeAverage V u) +
          (volumeAverage V u - volumeAverage V vbar)) := by
    funext x; ring
  have hinner : MemLp (fun x => (u x - volumeAverage V u) +
      (volumeAverage V u - volumeAverage V vbar)) 2 (volume.restrict V) :=
    hoscM.add hconstM
  have hstep1 : normalizedL2On V (fun x => vbar x - volumeAverage V vbar) ≤
      normalizedL2On V (fun x => vbar x - u x) +
        normalizedL2On V (fun x => (u x - volumeAverage V u) +
          (volumeAverage V u - volumeAverage V vbar)) := by
    rw [hdecomp]
    exact normalizedL2On_add_le hvuM hinner
  have hstep2 : normalizedL2On V (fun x => (u x - volumeAverage V u) +
      (volumeAverage V u - volumeAverage V vbar)) ≤
      normalizedL2On V (fun x => u x - volumeAverage V u) +
        |volumeAverage V u - volumeAverage V vbar| := by
    refine (normalizedL2On_add_le hoscM hconstM).trans (le_of_eq ?_)
    rw [normalizedL2On_const_abs hVpos]
  have hgap : |volumeAverage V u - volumeAverage V vbar| ≤
      normalizedL2On V (fun x => u x - vbar x) := by
    have hJ := abs_volumeAverage_le_normalizedL2On hVm hVpos huv huv2
    rwa [volumeAverage_sub_eq hu hv] at hJ
  have hsym : normalizedL2On V (fun x => vbar x - u x) =
      normalizedL2On V (fun x => u x - vbar x) :=
    normalizedL2On_sub_comm V vbar u
  rw [hsym] at hstep1
  linarith only [hstep1, hstep2, hgap]

/-- The oscillation of a difference splits into the two oscillations. -/
theorem oscillation_sub_le {V : Set (Vec d)}
    {vbar hbar : Vec d → ℝ} (hv : IntegrableOn vbar V volume)
    (hh : IntegrableOn hbar V volume)
    (hvM : MemLp (fun x => vbar x - volumeAverage V vbar) 2 (volume.restrict V))
    (hhM : MemLp (fun x => -(hbar x - volumeAverage V hbar)) 2 (volume.restrict V)) :
    normalizedL2On V (fun x => (vbar x - hbar x) -
        volumeAverage V (fun y => vbar y - hbar y)) ≤
      normalizedL2On V (fun x => vbar x - volumeAverage V vbar) +
        normalizedL2On V (fun x => hbar x - volumeAverage V hbar) := by
  have hmean := volumeAverage_sub_eq hv hh
  have hdecomp : (fun x => (vbar x - hbar x) -
      volumeAverage V (fun y => vbar y - hbar y)) =
      fun x => (vbar x - volumeAverage V vbar) +
        (-(hbar x - volumeAverage V hbar)) := by
    funext x
    rw [hmean]
    ring
  rw [hdecomp]
  refine (normalizedL2On_add_le hvM hhM).trans (le_of_eq ?_)
  rw [normalizedL2On_neg]

/-! ## 4. The composite reduction -/

/-- **The mean comparison reduced: the homogenization-error route, assembled.**

The scalar `S = |⨍_{V₁}(u − h)|` is bounded by

* the window oscillation of `u − h`, at the two volume-ratio factors — which
  splits into the frozen leg and the datum oscillation;
* the homogenization error `‖u − v̄‖_{L̲²(V₂)}` on the boundary-flush cube;
* the datum comparison `‖h̄ − h‖_{L̲²(V₂)}` (a data-only step);
* the mean `|⨍_{V₂}(v̄ − h̄)|` of the comparator difference.

Nothing on the right-hand side is `S`: the reduction is loop-free. -/
theorem abs_volumeAverage_sub_le_meanControlReduction {W V₁ V₂ : Set (Vec d)}
    (hV₁m : MeasurableSet V₁) (hV₂m : MeasurableSet V₂)
    (hsub₁ : V₁ ⊆ W) (hsub₂ : V₂ ⊆ W)
    (hWpos : 0 < (volume W).toReal) (hV₁pos : 0 < (volume V₁).toReal)
    (hV₂pos : 0 < (volume V₂).toReal)
    (hV₁top : volume V₁ ≠ ⊤) (hV₂top : volume V₂ ≠ ⊤)
    {u h vbar hbar : Vec d → ℝ}
    (hρ₁ : IntegrableOn (fun x => u x - h x) V₁ volume)
    (hρ₂ : IntegrableOn (fun x => u x - h x) V₂ volume)
    (hρ₁sq : IntegrableOn (fun x => ((u x - h x) -
      volumeAverage W (fun y => u y - h y)) ^ 2) V₁ volume)
    (hρ₂sq : IntegrableOn (fun x => ((u x - h x) -
      volumeAverage W (fun y => u y - h y)) ^ 2) V₂ volume)
    (hρWsq : IntegrableOn (fun x => ((u x - h x) -
      volumeAverage W (fun y => u y - h y)) ^ 2) W volume)
    (huv : IntegrableOn (fun x => u x - vbar x) V₂ volume)
    (hhh : IntegrableOn (fun x => hbar x - h x) V₂ volume)
    (hvh : IntegrableOn (fun x => vbar x - hbar x) V₂ volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V₂ volume)
    (hhh2 : IntegrableOn (fun x => (hbar x - h x) ^ 2) V₂ volume) :
    |volumeAverage V₁ (fun x => u x - h x)| ≤
      (Real.sqrt ((volume W).toReal / (volume V₁).toReal) +
          Real.sqrt ((volume W).toReal / (volume V₂).toReal)) *
          normalizedL2On W (fun x => (u x - h x) -
            volumeAverage W (fun y => u y - h y)) +
        (normalizedL2On V₂ (fun x => u x - vbar x) +
          normalizedL2On V₂ (fun x => hbar x - h x) +
          |volumeAverage V₂ (fun x => vbar x - hbar x)|) := by
  have h₁ := abs_volumeAverage_sub_windowAverage_le hV₁m hsub₁ hWpos hV₁pos hV₁top
    hρ₁ hρ₁sq hρWsq
  have h₂ := abs_volumeAverage_sub_windowAverage_le hV₂m hsub₂ hWpos hV₂pos hV₂top
    hρ₂ hρ₂sq hρWsq
  have h₃ := abs_volumeAverage_sub_le_comparatorSplit hV₂m hV₂pos
    (u := u) (h := h) (vbar := vbar) (hbar := hbar) huv hhh hvh huv2 hhh2
  have htri : |volumeAverage V₁ (fun x => u x - h x)| ≤
      |volumeAverage V₁ (fun x => u x - h x) -
          volumeAverage W (fun y => u y - h y)| +
        |volumeAverage V₂ (fun x => u x - h x) -
          volumeAverage W (fun y => u y - h y)| +
        |volumeAverage V₂ (fun x => u x - h x)| := by
    have hA := abs_sub_abs_le_abs_sub (volumeAverage V₁ (fun x => u x - h x))
      (volumeAverage W (fun y => u y - h y))
    have hB := abs_sub_abs_le_abs_sub (volumeAverage W (fun y => u y - h y))
      (volumeAverage V₂ (fun x => u x - h x))
    have hC := abs_sub_comm (volumeAverage W (fun y => u y - h y))
      (volumeAverage V₂ (fun x => u x - h x))
    rw [hC] at hB
    linarith only [hA, hB]
  linarith only [htri, h₁, h₂, h₃]

/-! ## 5. The loop-free certificate -/

/-- **The remaining obligation's own oscillation carries no `S`.**

The oscillation of the comparator difference `v̄ − h̄` on the flush cube is
bounded by twice the two comparison errors plus the oscillations of `u` and of
the datum `h` — and by nothing else. -/
theorem oscillation_comparatorDifference_le {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal) (hVtop : volume V ≠ ⊤)
    {u h vbar hbar : Vec d → ℝ}
    (hu : IntegrableOn u V volume) (hh : IntegrableOn h V volume)
    (hv : IntegrableOn vbar V volume) (hhb : IntegrableOn hbar V volume)
    (huv2 : IntegrableOn (fun x => (u x - vbar x) ^ 2) V volume)
    (hhh2 : IntegrableOn (fun x => (h x - hbar x) ^ 2) V volume)
    (hvuM : MemLp (fun x => vbar x - u x) 2 (volume.restrict V))
    (hhbM : MemLp (fun x => hbar x - h x) 2 (volume.restrict V))
    (huoscM : MemLp (fun x => u x - volumeAverage V u) 2 (volume.restrict V))
    (hhoscM : MemLp (fun x => h x - volumeAverage V h) 2 (volume.restrict V))
    (hvoscM : MemLp (fun x => vbar x - volumeAverage V vbar) 2 (volume.restrict V))
    (hhboscM : MemLp (fun x => -(hbar x - volumeAverage V hbar)) 2
      (volume.restrict V)) :
    normalizedL2On V (fun x => (vbar x - hbar x) -
        volumeAverage V (fun y => vbar y - hbar y)) ≤
      2 * normalizedL2On V (fun x => u x - vbar x) +
        2 * normalizedL2On V (fun x => h x - hbar x) +
        normalizedL2On V (fun x => u x - volumeAverage V u) +
        normalizedL2On V (fun x => h x - volumeAverage V h) := by
  have hsplit := oscillation_sub_le hv hhb hvoscM hhboscM
  have hv' := oscillation_comparator_le hVm hVpos hVtop hu hv huv2 hvuM huoscM
  have hh' := oscillation_comparator_le hVm hVpos hVtop hh hhb hhh2 hhbM hhoscM
  linarith only [hsplit, hv', hh']

/-! ## 6. The boundary-trace form of the remaining obligation -/

/-- **The absorption arithmetic of the remaining obligation.**

The intended proof of `|⨍_V w| ≤ C·‖w − (w)_V‖` for a `Δ`-harmonic `w` vanishing
on a face of `V` runs through a cross-section trace inequality and produces, at
first, the *quadratic* form

```text
  β² ≤ A·osc² + B·osc·(osc + |β|)
```

with `A`, `B` the (explicit, `d`-only) trace and Caccioppoli constants.  This
lemma is the elementary absorption that turns that form into the linear bound

```text
  |β| ≤ (B + √(A+B)) · osc  ,
```

recorded here so that the remaining obligation is exactly one analytic
inequality with no further arithmetic attached.  The constant is the positive
root of `t² − B t − (A+B) = 0` rounded up, and it is sharp in order: at `B = 0`
it reads `|β| ≤ √A · osc`, which is exactly what `β² ≤ A·osc²` gives. -/
theorem abs_le_of_sq_le_quadratic {beta osc A B : ℝ} (hosc : 0 ≤ osc)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hquad : beta ^ 2 ≤ A * osc ^ 2 + B * osc * (osc + |beta|)) :
    |beta| ≤ (B + Real.sqrt (A + B)) * osc := by
  have hAB : (0 : ℝ) ≤ A + B := by linarith only [hA, hB]
  set s : ℝ := Real.sqrt (A + B) with hs
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = A + B := Real.mul_self_sqrt hAB
  clear_value s
  clear hs
  have hb : 0 ≤ |beta| := abs_nonneg beta
  have hsq : |beta| * |beta| = beta ^ 2 := by
    rw [← sq_abs beta]; ring
  have hquad' : |beta| * |beta| ≤ (A + B) * (osc * osc) + B * osc * |beta| := by
    rw [hsq]
    linarith only [hquad]
  by_contra hcon
  push_neg at hcon
  have hBsnn : 0 ≤ B + s := by linarith only [hB, hsnn]
  have hprodnn : 0 ≤ (B + s) * osc := mul_nonneg hBsnn hosc
  have hbpos : 0 < |beta| := lt_of_le_of_lt hprodnn hcon
  have hmul : ((B + s) * osc) * |beta| < |beta| * |beta| :=
    mul_lt_mul_of_pos_right hcon hbpos
  have hsoscnn : 0 ≤ s * osc := mul_nonneg hsnn hosc
  have hsooo : (s * osc) * ((B + s) * osc) ≤ (s * osc) * |beta| :=
    mul_le_mul_of_nonneg_left hcon.le hsoscnn
  have hexpand : (s * osc) * ((B + s) * osc) =
      B * s * (osc * osc) + (A + B) * (osc * osc) := by
    calc (s * osc) * ((B + s) * osc)
        = B * s * (osc * osc) + (s * s) * (osc * osc) := by ring
      _ = B * s * (osc * osc) + (A + B) * (osc * osc) := by rw [hss]
  have hoscsq : 0 ≤ osc * osc := mul_nonneg hosc hosc
  have hnn : 0 ≤ B * s * (osc * osc) := mul_nonneg (mul_nonneg hB hsnn) hoscsq
  have hlow : (A + B) * (osc * osc) ≤ (s * osc) * |beta| := by
    rw [hexpand] at hsooo
    linarith only [hsooo, hnn]
  have hid : (B + s) * osc * |beta| = B * osc * |beta| + (s * osc) * |beta| := by ring
  linarith only [hquad', hmul, hlow, hid]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
