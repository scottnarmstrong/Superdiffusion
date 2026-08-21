/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.SealCaccioppoliGeometry

/-!
# The residue routes, measured: three machine-checked obstructions

This module records, as theorems, the exact inequalities that block the two
candidate producers for the harmonic-approximation residue `‖u − w‖_{L̲²(K')}`
of `ResidueBudget`, with `K' = flushSubCentre z m n i σ + □_n` the flush
scale-`n` sub-cube of the boundary branch and `w` a `Δ`-harmonic comparator of
`u` there.  Nothing here is an analytic estimate; each theorem is the arithmetic
or geometric core of one measured route, isolated so that the STOP table is
checked rather than asserted.

## The room (the legal-producer contract)

So a residue producer may output exactly

```text
  ‖u − w‖_{L̲²(K')} ≤ K1 · ‖u − (u)_{W'}‖_{L̲²(W')}
                    + K2 · 3^n ‖∇h‖_{L̲²(W')}
                    + K3 · s^{-2} 3^{(1+s)n} [∇h]_{H̲^s(W')}
                    + K4 · s^{-3} σ̄_n^{-1} 3^{(1+s)n} [g]_{H̲^s(W')}
```

with `K1..K4` constants: the four allowed `s`-powers are `0, 0, −2, −3` and
only the last carries a `σ̄^{-1}`.  Both routes below fail *against this
contract*, each by one uniform factor.

## Route 1 — the `p = 2` coarse-graining comparison at `K'`

The proved interior chain
(`InteriorEllipticitySlot.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased`
composed with `AssemblyEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs`)
prices a comparator distance in the shape

```text
  ‖u − w‖ ≤ A · s^{-4} · 𝓔 · ( ‖u − (u)_{W'}‖ + S ) + (s^{-6}, s^{-7}σ̄^{-1} legs) ,
```

so the budget's first-leg coefficient would be `K1 = A·s^{-4}·𝓔`, **not** a
constant.  `coarseGrainingResidue_coefficient_unbounded` is the refutation: for
any fixed error level `E > 0` — in particular for the level the frozen good
event pins, `𝓔 ≤ C_E·ε` at `ε = 1/2` — and any candidate constant, some
admissible `s ∈ (0,1]` exceeds it.  `coarseGrainingResidue_loop_not_contraction`
is the same statement read as the self-consistency loop `S ≤ a + θ·S`: the loop
coefficient `θ = A·s^{-4}·𝓔` is not below `1` uniformly, so the residue cannot be
solved for either.  Closing the route needs `𝓔 ≲ s^4`, i.e. the good event's
`ε` re-pinned at `c·s^4` — a change to the frozen statement.

## Route 1′/option (ii) — the fitted boundary Caccioppoli at `K'`

`SealCaccioppoliGeometry.flushSubCube_boundaryOuterAssembly_fits` prices the
`ν`-weighted energy `ν·⨍_{K'}|∇u|²` against a coarse-grained `Λ_t`-weighted
right-hand side, so extracting a `ν`-free comparator distance costs
`√(Λ_t/ν) ≤ C√(σ̄/ν)`.  `energyRatio_sqrt_unbounded` records that no constant
absorbs `√(σ̄/ν)` over `0 < ν ≤ σ̄`.  (That the ratio really is unbounded on the
model family is ABK26's Theorem A; it is cited, not proved here.)

## Route 2 — the anchor's own good event at the sub-scale

Every proved transfer that would put an error cap, an ellipticity cap, or the
anchor's own conclusion on a scale-`n` cube requires the anchor's geometry
binder `x + □_n ⊆ (z+□_{n+1}) ∩ □_m` — see
`InteriorGlueCap.ae_offGridChildError_le_representative_harmonicSlot` and
`AssemblyEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs`.
`exists_flushSubCube_not_subset_anchorGeometry` exhibits an admissible
boundary-branch configuration in which
`K'` satisfies `K' ⊆ □_m` but **not** `K' ⊆ z + □_{n+1}`: the flush sub-cube is
pushed `4·3^n` off `z` while `z + □_{n+1}` reaches only `3^n`.  And
`no_flushCentre_within_anchorGeometry` shows this is intrinsic, not a bad
choice of `K'`: on the whole sub-range `½·3^m − 9/2·3^n < σ·zᵢ < ½·3^m −
3/2·3^n` of the boundary branch (nonempty by
`wellPlacedHalfGap_lt_farThreshold`, width `3·3^n`) **no** flush scale-`n`
centre satisfies the binder.  So the caps are not available at `K'` as proved,
independently of the arithmetic above.

The scope of that obstruction: it is a statement about the proved *binders*,
not a proof that the underlying apparatus cannot be re-instantiated.
`InteriorGlueCap.ae_offGridChildError_le_representative_translate` is already
stated for an arbitrary real translate with `w + □_n ⊆ □_{n+2}`, and `K'` does
satisfy the corresponding gap-three containment `c' − z + □_n ⊆ □_{n+3}` at the
frozen `(n+3, z)` frame; re-cutting that cap and the ellipticity caps at the
`(n+3)` parent is bounded provider work.  The arithmetic obstruction of Route 1
is the one that does not move.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2;
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. Route 1: the `s^{-4}·𝓔` coefficient is not a constant -/

/-- The display's `s^{-4}` written as a natural power of `s⁻¹`. -/
theorem rpow_neg_four_eq_inv_pow {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(4 : ℝ)) = (s⁻¹) ^ (4 : ℕ) := by
  have h1 : Real.rpow s (-(4 : ℝ)) = (Real.rpow s (4 : ℝ))⁻¹ := Real.rpow_neg hs.le 4
  have h2 : Real.rpow s (4 : ℝ) = s ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
    exact Real.rpow_natCast s 4
  rw [h1, h2, inv_pow]

/-- Auxiliary: an unbounded family of admissible `s`. -/
private theorem exists_small_s_gt {A E K : ℝ} (hA : 0 < A) (hE : 0 < E) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ K < A * (s⁻¹) ^ (4 : ℕ) * E := by
  have hAE : (0 : ℝ) < A * E := mul_pos hA hE
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (K / (A * E)))
  have h1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN.le
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one h1
  have hinvpos : (0 : ℝ) < ((N : ℝ))⁻¹ := inv_pos.mpr hNpos
  have hmul : ((N : ℝ))⁻¹ * (N : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hNpos)
  have hle1 : ((N : ℝ))⁻¹ ≤ 1 := by nlinarith only [hmul, h1, hinvpos]
  refine ⟨((N : ℝ))⁻¹, hinvpos, hle1, ?_⟩
  have hinv : ((((N : ℝ))⁻¹))⁻¹ = (N : ℝ) := inv_inv _
  rw [hinv]
  have hKlt : K / (A * E) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hK : K < (N : ℝ) * (A * E) := by
    rw [div_lt_iff₀ hAE] at hKlt
    linarith only [hKlt]
  have hpow : (N : ℝ) ≤ (N : ℝ) ^ (4 : ℕ) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (N : ℝ) ^ (4 : ℕ) := pow_le_pow_right₀ h1 (by norm_num)
  calc K < (N : ℝ) * (A * E) := hK
    _ ≤ (N : ℝ) ^ (4 : ℕ) * (A * E) := mul_le_mul_of_nonneg_right hpow hAE.le
    _ = A * (N : ℝ) ^ (4 : ℕ) * E := by ring

/-- **Route 1's absorption fails.**

The coarse-graining producer's first-leg coefficient is `A·s^{-4}·E`, with `A`
dimensional and `E` a fixed positive error level.  No candidate constant `K1`
dominates it over the admissible range `s ∈ (0,1]`. -/
theorem coarseGrainingResidue_coefficient_unbounded {A E : ℝ} (hA : 0 < A)
    (hE : 0 < E) (K1 : ℝ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ K1 < A * Real.rpow s (-(4 : ℝ)) * E := by
  obtain ⟨s, hs, hs1, hlt⟩ := exists_small_s_gt (K := K1) hA hE
  refine ⟨s, hs, hs1, ?_⟩
  rw [rpow_neg_four_eq_inv_pow hs]
  exact hlt

/-- **Route 1's self-consistency loop is not a contraction.** -/
theorem coarseGrainingResidue_loop_not_contraction {A E : ℝ} (hA : 0 < A)
    (hE : 0 < E) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ 1 < A * Real.rpow s (-(4 : ℝ)) * E :=
  coarseGrainingResidue_coefficient_unbounded hA hE 1

/-- **The exact closing condition for route 1.**

If the error level obeys `A·E ≤ s^4` then — and, by
`coarseGrainingResidue_coefficient_unbounded`, essentially only then — the
coefficient is bounded by `1`.  This is the `ε ≤ c·s^4` re-pinning of the good
event: a change to the frozen statement. -/
theorem coarseGrainingResidue_coefficient_le_of_error_small {A E s : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hE : 0 ≤ E) (hsmall : A * E ≤ s ^ (4 : ℕ)) :
    A * Real.rpow s (-(4 : ℝ)) * E ≤ 1 := by
  rw [rpow_neg_four_eq_inv_pow hs]
  have hs4 : (0 : ℝ) < s ^ (4 : ℕ) := pow_pos hs 4
  have hinv : (s⁻¹) ^ (4 : ℕ) = (s ^ (4 : ℕ))⁻¹ := inv_pow s 4
  rw [hinv]
  have hAE : (0 : ℝ) ≤ A * E := mul_nonneg hA hE
  have hmul := mul_le_mul_of_nonneg_left hsmall (le_of_lt (inv_pos.mpr hs4))
  rw [inv_mul_cancel₀ (ne_of_gt hs4)] at hmul
  calc A * (s ^ (4 : ℕ))⁻¹ * E = (s ^ (4 : ℕ))⁻¹ * (A * E) := by ring
    _ ≤ 1 := hmul

/-! ## 2. Route 1′ / option (ii): the `√(σ̄/ν)` cost is not absorbable -/

/-- **No constant absorbs `√(σ̄/ν)`.**

The fitted boundary Caccioppoli prices `ν·⨍_{K'}|∇u|²` against a `Λ_t`-weighted
right-hand side; converting to a `ν`-free residue multiplies the first leg by
`√(Λ_t/ν)`, and `Λ_t` is capped only by `C·σ̄`.  Over free reals `0 < nu ≤
sigmabar` the factor is unbounded. -/
theorem energyRatio_sqrt_unbounded (K : ℝ) :
    ∃ nu sigmabar : ℝ, 0 < nu ∧ nu ≤ sigmabar ∧ K < Real.sqrt (sigmabar / nu) := by
  refine ⟨1, (max K 0) ^ (2 : ℕ) + 1, one_pos, ?_, ?_⟩
  · have := sq_nonneg (max K 0)
    have h2 : (max K 0) ^ (2 : ℕ) = (max K 0) ^ 2 := rfl
    rw [h2]
    linarith only [this]
  · have h0 : (0 : ℝ) ≤ max K 0 := le_max_right _ _
    have hK : K ≤ max K 0 := le_max_left _ _
    have hdiv : ((max K 0) ^ (2 : ℕ) + 1) / 1 = (max K 0) ^ (2 : ℕ) + 1 := div_one _
    rw [hdiv]
    have hs : Real.sqrt ((max K 0) ^ (2 : ℕ)) = max K 0 := by
      have h2 : (max K 0) ^ (2 : ℕ) = (max K 0) ^ 2 := rfl
      rw [h2]
      exact Real.sqrt_sq h0
    have hlt : Real.sqrt ((max K 0) ^ (2 : ℕ)) <
        Real.sqrt ((max K 0) ^ (2 : ℕ) + 1) :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith only [])
    rw [hs] at hlt
    linarith only [hK, hlt]

/-! ## 3. Route 2: the anchor's geometry binder fails at the flush sub-cube -/

/-- **No flush scale-`n` cube sits inside the anchor's geometry window.**

A cube `c + □_n` whose `σeᵢ` face lies in `∂□_m` has `σ·cᵢ = ½·3^m − ½·3^n`.
If `z` is farther than `3/2·3^n` from that face, `c + □_n ⊆ z + □_{n+1}` is
impossible: the containment forces `|cᵢ − zᵢ| ≤ 3^n` while the flush condition
forces `σ·(cᵢ − zᵢ) > 3^n`.  No choice of flush centre avoids this. -/
theorem no_flushCentre_within_anchorGeometry {n m : ℤ} {z c : Vec d} {i : Fin d}
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfar : σ * z i < (1 / 2 : ℝ) * (3 : ℝ) ^ m - (3 / 2 : ℝ) * (3 : ℝ) ^ n)
    (hflush : σ * c i = (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ n)
    (hsub : ((fun y => c + y) '' openCubeSet (originCube d n)) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1)))) : False := by
  have hbound := abs_centre_sub_add_half_le_half_of_image_add_subset hsub i
  have h3 : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) n 1, zpow_one]
    ring
  rw [h3] at hbound
  have habs : |c i - z i| ≤ (3 : ℝ) ^ n := by linarith only [hbound]
  have hsigma : σ * (c i - z i) ≤ |c i - z i| := by
    rcases hσ with h | h <;> subst h
    · rw [one_mul]
      exact le_abs_self _
    · rw [neg_one_mul]
      exact neg_le_abs _
  have hval : σ * (c i - z i) =
      ((1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ n) - σ * z i := by
    have hexp : σ * (c i - z i) = σ * c i - σ * z i := by ring
    rw [hexp, hflush]
  linarith only [hval, hfar, habs, hsigma]

/-- **The flush sub-cube `K'` itself, at any far boundary-branch position.** -/
theorem flushSubCube_not_subset_anchorGeometry_of_far {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} {i : Fin d} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hover : wellPlacedHalfGap m (n + 2) < σ * z i)
    (hfar : σ * z i < (1 / 2 : ℝ) * (3 : ℝ) ^ m - (3 / 2 : ℝ) * (3 : ℝ) ^ n) :
    ¬ (((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n)) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1)))) := by
  intro hsub
  have hlevel := flushSubCentre_faceLevel hnm hσ hover
  exact no_flushCentre_within_anchorGeometry hσ hfar (by linarith only [hlevel]) hsub

/-- **The obstruction window is a genuine sub-range of the boundary branch.**

The gate's overhang threshold `wellPlacedHalfGap m (n+2) = ½·3^m − 9/2·3^n` is
strictly below the far threshold `½·3^m − 3/2·3^n`, so positions satisfying both
`hover` and `hfar` exist, at width `3·3^n`. -/
theorem wellPlacedHalfGap_lt_farThreshold (m n : ℤ) :
    wellPlacedHalfGap m (n + 2) <
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (3 / 2 : ℝ) * (3 : ℝ) ^ n := by
  have h9 : (3 : ℝ) ^ (n + 2) = 9 * (3 : ℝ) ^ n := three_zpow_add_two n
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  rw [wellPlacedHalfGap, h9]
  linarith only [hpos]

/-- **The flush sub-cube is outside the anchor's geometry binder.**

At an admissible boundary-branch configuration (`n = 0`, `m = 2`, `σ = 1`, `z`
just inside the face) the flush scale-`n` sub-cube `K'` sits inside `□_m` but
**not** inside `z + □_{n+1}`.  Consequently none of the proved transfers that
require the anchor's geometry binder — the off-grid child error cap, the
coarse-grained ellipticity caps, the boundary energy leg, and the anchor
itself read at `x := flushSubCentre z m n i σ` — is available at `K'`. -/
theorem exists_flushSubCube_not_subset_anchorGeometry (d : ℕ) [NeZero d] :
    ∃ (n m : ℤ) (z : Vec d) (i : Fin d) (σ : ℝ),
      n + 2 ≤ m ∧
      z ∈ openCubeSet (originCube d m) ∧
      (σ = 1 ∨ σ = -1) ∧
      wellPlacedHalfGap m (n + 2) < σ * z i ∧
      ((fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)) ⊆
        openCubeSet (originCube d m) ∧
      ¬ (((fun y => flushSubCentre z m n i σ + y) ''
            openCubeSet (originCube d n)) ⊆
          ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
            openCubeSet (originCube d m)) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  set z : Vec d := (fun r => if r = i0 then (1 / 2 : ℝ) else 0) with hzdef
  have hzi : z i0 = 1 / 2 := by
    rw [hzdef]
    simp
  have hnm : (0 : ℤ) + 2 ≤ 2 := by norm_num
  have hσ : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hgap : wellPlacedHalfGap (2 : ℤ) ((0 : ℤ) + 2) = 0 := by
    rw [wellPlacedHalfGap]
    norm_num
  refine ⟨0, 2, z, i0, 1, hnm, ?_, hσ, ?_, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro r
    by_cases hr : r = i0
    · have hzr : z r = 1 / 2 := by
        rw [hr]
        exact hzi
      rw [hzr]
      constructor
      · norm_num
      · norm_num
    · have hzr : z r = 0 := by
        rw [hzdef]
        simp only [if_neg hr]
      rw [hzr]
      constructor
      · norm_num
      · norm_num
  · rw [hgap, hzi]
    norm_num
  · exact flushSubCube_subset_openCubeSet hnm z i0 hσ
  · intro hsubset
    have hzero : (0 : Vec d) ∈ openCubeSet (originCube d 0) := by
      rw [mem_openCubeSet_originCube_iff]
      intro r
      constructor
      · show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (0 : ℤ) < (0 : ℝ)
        norm_num
      · show (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ (0 : ℤ)
        norm_num
    have hmem : flushSubCentre z (2 : ℤ) 0 i0 1 ∈
        (fun y => flushSubCentre z (2 : ℤ) 0 i0 1 + y) ''
          openCubeSet (originCube d 0) := by
      refine ⟨0, hzero, ?_⟩
      show flushSubCentre z (2 : ℤ) 0 i0 1 + 0 = flushSubCentre z (2 : ℤ) 0 i0 1
      exact add_zero _
    have hin := (hsubset hmem).1
    rw [mem_image_add_iff, mem_openCubeSet_originCube_iff] at hin
    have hhi := (hin i0).2
    have hwp : wellPlacedCentre z (2 : ℤ) ((0 : ℤ) + 2) i0 = 0 := by
      show max (-wellPlacedHalfGap (2 : ℤ) ((0 : ℤ) + 2))
        (min (wellPlacedHalfGap (2 : ℤ) ((0 : ℤ) + 2)) (z i0)) = 0
      rw [hgap, hzi]
      norm_num
    have hfs : flushSubCentre z (2 : ℤ) 0 i0 1 i0 = 4 := by
      rw [flushSubCentre_apply_self, hwp]
      norm_num
    have hval : (flushSubCentre z (2 : ℤ) 0 i0 1 - z) i0 = 4 - 1 / 2 := by
      show flushSubCentre z (2 : ℤ) 0 i0 1 i0 - z i0 = 4 - 1 / 2
      rw [hfs, hzi]
    rw [hval] at hhi
    have h3 : (1 / 2 : ℝ) * (3 : ℝ) ^ ((0 : ℤ) + 1) = 3 / 2 := by norm_num
    rw [h3] at hhi
    linarith only [hhi]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
