/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Locality of the weak gradient

The weak gradient is a *local* object: if `u` has weak gradient `Du` on each
member of an open cover of `W`, it has weak gradient `Du` on `W` itself.  This
fact is absent from Mathlib and from the compiled part of CoarseGraining, and
it is the first frontier item of the §4.3 odd-reflection chain: it is what
turns the one-face harmonicity transfer into a statement about the whole
reflected window, and what upgrades a *localized* zero-trace hypothesis (a
hypothesis about `η · v` for cutoffs `η`) into a statement about `v`.

## The argument

Only one ingredient is genuinely missing: a smooth partition of a compactly
supported test function subordinate to the cover.  It is built here from
scratch and *without* any manifold machinery, by a telescoping product:

* `exists_contDiff_eq_one_nhds` upgrades Mathlib's
  `exists_smooth_tsupport_subset` (a bump equal to `1` at one point) to a bump
  identically `1` on a *neighbourhood* of the point, by composing with a
  rescaled `Real.smoothTransition`;
* the compact set `tsupport φ` is covered by finitely many such neighbourhoods,
  so the product `∏ (1 - gᶜ)` of the corresponding bump defects vanishes on
  `tsupport φ`, hence `φ · ∏ (1 - gᶜ) = 0` everywhere;
* `exists_smooth_decomposition_of_open_cover` then telescopes
  `1 - ∏_{c ∈ t} (1 - gᶜ) = ∑ gᶜ ∏_{earlier} (1 - g)` by induction on the
  finite index set, producing finitely many smooth compactly supported pieces
  `ψ j` summing to `φ`, each supported in one member of the cover.

No normalization, no division, and no `SmoothPartitionOfUnity` is needed: the
telescoping identity is exact, and the pieces need not be nonnegative or sum to
one off `tsupport φ`.

The `L²` hypotheses in the locality statements are not decoration.  The weak
derivative predicate `HasWeakPartialDerivOn` is an identity between Bochner
integrals, and splitting the integral of `φ = ∑ ψ j` across the sum requires
each summand to be genuinely integrable; `u, Du ∈ L²(W)` (the `H¹` carrier's
own data) is exactly what makes the Hölder pairing with the smooth compactly
supported pieces integrable.

## Main results

* `exists_contDiff_eq_one_nhds` — a smooth compactly supported bump equal to `1`
  on a neighbourhood of a point and supported in a prescribed neighbourhood.
* `exists_smooth_decomposition_of_open_cover` — the finite smooth decomposition
  of a compactly supported test function subordinate to an open cover.
* `hasWeakPartialDerivOn_iUnion`, `hasWeakGradientOn_iUnion` — locality on a
  union of open sets.
* `hasWeakGradientOn_of_open_cover` — the cover form (the shape consumers use).
* `hasWeakGradientOn_union` — the two-set specialization.

The opposite (easy) direction — restriction of a weak gradient to an open
subset — is CoarseGraining's `HasWeakGradientOn.restrict` and is not repeated
here.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. A smooth bump identically one near a point -/

/-- Mathlib's smooth transition, rescaled to vanish on `(-∞, 1/2]` and to equal
`1` on `[3/4, ∞)`. -/
private def oneNear (t : ℝ) : ℝ :=
  Real.smoothTransition (4 * t - 2)

private theorem contDiff_oneNear : ContDiff ℝ (⊤ : ℕ∞) oneNear := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 4 * t - 2 :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  exact Real.smoothTransition.contDiff.comp h

private theorem oneNear_eq_zero {t : ℝ} (ht : t ≤ 1 / 2) : oneNear t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [ht])

private theorem oneNear_eq_one {t : ℝ} (ht : 3 / 4 ≤ t) : oneNear t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [ht])

private theorem tsupport_zeroFun : tsupport (fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d)) := by
  have hsupp : Function.support (fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d)) := by
    ext z
    simp
  show closure (Function.support fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d))
  rw [hsupp, closure_empty]

private theorem hasCompactSupport_zeroFun :
    HasCompactSupport (fun _ : Vec d => (0 : ℝ)) := by
  show IsCompact (tsupport fun _ : Vec d => (0 : ℝ))
  rw [tsupport_zeroFun]
  exact isCompact_empty

/-- **A smooth bump identically one on a neighbourhood.**

Mathlib's `exists_smooth_tsupport_subset` produces a smooth compactly supported
bump supported in `s` and equal to `1` *at* `x`.  Composing it with the
rescaled smooth transition `oneNear` produces one equal to `1` on a whole open
neighbourhood of `x`, which is what the telescoping decomposition below needs
(a product of defects `1 - g` must vanish *identically* on the covered
compact set, not merely at chosen points). -/
theorem exists_contDiff_eq_one_nhds {s : Set (Vec d)} {x : Vec d} (hs : s ∈ 𝓝 x) :
    ∃ (g : Vec d → ℝ) (W : Set (Vec d)),
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ s ∧
        IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, g y = 1 := by
  obtain ⟨f, hfs, hfc, hf, -, hfx⟩ := exists_smooth_tsupport_subset hs
  have hsupp : Function.support (fun y => oneNear (f y)) ⊆ Function.support f := by
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [h0]; exact oneNear_eq_zero (by norm_num))
  have htsupp : tsupport (fun y => oneNear (f y)) ⊆ tsupport f :=
    closure_mono hsupp
  refine ⟨fun y => oneNear (f y), {y | 3 / 4 < f y}, contDiff_oneNear.comp hf, ?_,
    htsupp.trans hfs, isOpen_lt continuous_const hf.continuous, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hfc isClosed_closure htsupp
  · show (3 : ℝ) / 4 < f x
    rw [hfx]
    norm_num
  · intro y hy
    exact oneNear_eq_one (le_of_lt hy)

/-! ## 2. The finite smooth decomposition subordinate to an open cover -/

/-- The telescoping step.  Given finitely many smooth "local one" bumps whose
defects annihilate `φ`, the test function splits into finitely many smooth
compactly supported pieces, each supported inside one member of the cover.

The identity behind the induction is
`1 - ∏_{c ∈ insert a t} (1 - g c) = g a + (1 - g a) · (1 - ∏_{c ∈ t} (1 - g c))`,
which after multiplication by `φ` reads `φ = φ · g a + φ · (1 - g a)`. -/
private theorem exists_decomposition_aux {ι κ : Type*} {U : ι → Set (Vec d)}
    (G : κ → Vec d → ℝ) (A : κ → ι)
    (hGsmooth : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (G c))
    (hGsupp : ∀ c, tsupport (G c) ⊆ U (A c)) :
    ∀ (t : Finset κ) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ z, φ z * ∏ c ∈ t, (1 - G c z) = 0) →
      ∃ (N : ℕ) (ψ : ℕ → Vec d → ℝ),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) ∧ (∀ j, HasCompactSupport (ψ j)) ∧
          (∀ j, j < N → ∃ α : ι, tsupport (ψ j) ⊆ U α) ∧
            (∀ z, ∑ j ∈ Finset.range N, ψ j z = φ z) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro φ _hφ _hφc hzero
      refine ⟨0, fun _ _ => (0 : ℝ), fun _ => contDiff_const,
        fun _ => hasCompactSupport_zeroFun, fun j hj => absurd hj (by omega), fun z => ?_⟩
      have hz : φ z = 0 := by
        have h := hzero z
        simpa using h
      simp [hz]
  | @insert c s hcs ih =>
      intro φ hφ hφc hzero
      have hprod : ∀ z, (φ z * (1 - G c z)) * ∏ e ∈ s, (1 - G e z) = 0 := by
        intro z
        have h := hzero z
        rw [Finset.prod_insert hcs, ← mul_assoc] at h
        exact h
      obtain ⟨N, ψ, hψs, hψc, hψsub, hψsum⟩ :=
        ih (fun z => φ z * (1 - G c z)) (hφ.mul (contDiff_const.sub (hGsmooth c)))
          (HasCompactSupport.mul_right hφc) hprod
      refine ⟨N + 1,
        fun j => Nat.rec (motive := fun _ => Vec d → ℝ) (fun z => φ z * G c z)
          (fun l _ => ψ l) j,
        fun j => ?_, fun j => ?_, fun j _hj => ?_, fun z => ?_⟩
      · cases j with
        | zero => exact hφ.mul (hGsmooth c)
        | succ l => exact hψs l
      · cases j with
        | zero => exact HasCompactSupport.mul_right hφc
        | succ l => exact hψc l
      · cases j with
        | zero =>
            refine ⟨A c, (closure_mono ?_).trans (hGsupp c)⟩
            intro z hz
            simp only [Function.mem_support] at hz ⊢
            intro hg0
            refine hz ?_
            show φ z * G c z = 0
            rw [hg0, mul_zero]
        | succ l => exact hψsub l (by omega)
      · rw [Finset.sum_range_succ']
        have hsum : (∑ l ∈ Finset.range N,
            Nat.rec (motive := fun _ => Vec d → ℝ) (fun w => φ w * G c w)
              (fun l _ => ψ l) (l + 1) z) = ∑ l ∈ Finset.range N, ψ l z :=
          Finset.sum_congr rfl fun _ _ => rfl
        rw [hsum, hψsum z]
        show φ z * (1 - G c z) + φ z * G c z = φ z
        ring

/-- **The finite smooth decomposition subordinate to an open cover.**

A smooth compactly supported `φ` with `tsupport φ ⊆ ⋃ α, U α` splits as a
finite sum of smooth compactly supported pieces, each supported inside a single
member of the cover.  This is the partition-of-unity input to locality; it is
proved here from Mathlib's bump functions alone. -/
theorem exists_smooth_decomposition_of_open_cover {ι : Type*} {U : ι → Set (Vec d)}
    (hUopen : ∀ α, IsOpen (U α)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ ⋃ α, U α) :
    ∃ (N : ℕ) (ψ : ℕ → Vec d → ℝ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) ∧ (∀ j, HasCompactSupport (ψ j)) ∧
        (∀ j, j < N → ∃ α : ι, tsupport (ψ j) ⊆ U α) ∧
          (∀ z, ∑ j ∈ Finset.range N, ψ j z = φ z) := by
  classical
  have hK : IsCompact (tsupport φ) := hφc
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨α₀, _hα₀⟩ : ∃ α, y₀ ∈ U α := by
      have h := hφU hy₀
      simpa only [Set.mem_iUnion] using h
    have hex : ∀ y : Vec d, ∃ p : (Vec d → ℝ) × ι × Set (Vec d),
        ContDiff ℝ (⊤ : ℕ∞) p.1 ∧ HasCompactSupport p.1 ∧ tsupport p.1 ⊆ U p.2.1 ∧
          IsOpen p.2.2 ∧ (∀ z ∈ p.2.2, p.1 z = 1) ∧ (y ∈ tsupport φ → y ∈ p.2.2) := by
      intro y
      by_cases hy : y ∈ tsupport φ
      · obtain ⟨α, hα⟩ : ∃ α, y ∈ U α := by
          have h := hφU hy
          simpa only [Set.mem_iUnion] using h
        obtain ⟨g, W, hg, hgc, hgU, hWopen, hyW, hgW⟩ :=
          exists_contDiff_eq_one_nhds ((hUopen α).mem_nhds hα)
        exact ⟨(g, α, W), hg, hgc, hgU, hWopen, hgW, fun _ => hyW⟩
      · refine ⟨(fun _ => 0, α₀, (∅ : Set (Vec d))), contDiff_const,
          hasCompactSupport_zeroFun, ?_, isOpen_empty,
          fun z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hy⟩
        show tsupport (fun _ : Vec d => (0 : ℝ)) ⊆ U α₀
        rw [tsupport_zeroFun]
        exact Set.empty_subset _
    choose p hp1 hp2 hp3 hp4 hp5 hp6 using hex
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => (p y).2.2) (fun y => hp4 y)
      (fun y hy => Set.mem_iUnion.2 ⟨y, hp6 y hy⟩)
    refine exists_decomposition_aux (U := U) (fun y => (p y).1) (fun y => (p y).2.1)
      hp1 hp3 t φ hφ hφc ?_
    intro z
    by_cases hz : z ∈ tsupport φ
    · obtain ⟨y, hyt, hzy⟩ : ∃ y ∈ t, z ∈ (p y).2.2 := by
        have h := ht hz
        simpa only [Set.mem_iUnion, exists_prop] using h
      have hfac : (1 : ℝ) - (p y).1 z = 0 := by
        rw [hp5 y z hzy]
        ring
      rw [Finset.prod_eq_zero hyt hfac, mul_zero]
    · have hz0 : φ z = 0 := by
        by_contra h
        exact hz (subset_tsupport φ h)
      rw [hz0, zero_mul]
  · refine ⟨0, fun _ _ => (0 : ℝ), fun _ => contDiff_const,
      fun _ => hasCompactSupport_zeroFun, fun j hj => absurd hj (by omega), fun z => ?_⟩
    have hz : φ z = 0 := by
      by_contra h
      exact hne ⟨z, subset_tsupport φ h⟩
    simp [hz]

/-! ## 3. Locality of the weak gradient -/

private theorem holderTwoTwoOne : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
  ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩

private theorem memL2_restrict_of_contDiff {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    MemLp f 2 (volume.restrict W) :=
  (hf.continuous.memLp_of_hasCompactSupport hfc).restrict W

private theorem memL2_restrict_fderiv {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (i : Fin d) :
    MemLp (fun y => (fderiv ℝ f y) (basisVec i)) 2 (volume.restrict W) := by
  have hcont : Continuous fun y => (fderiv ℝ f y) (basisVec i) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun y => (fderiv ℝ f y) (basisVec i) := by
    simpa only using hfc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcont.memLp_of_hasCompactSupport hsupp).restrict W

private theorem integrable_mul_restrict {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) (hg : MemLp g 2 (volume.restrict W)) :
    Integrable (fun y => f y * g y) (volume.restrict W) := by
  haveI := holderTwoTwoOne
  exact hf.integrable_mul hg

/-- **Locality of the weak partial derivative on an open cover.** -/
theorem hasWeakPartialDerivOn_iUnion {ι : Type*} {U : ι → Set (Vec d)}
    (hUopen : ∀ α, IsOpen (U α)) {i : Fin d} {u gi : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (⋃ α, U α)))
    (hgi : MemLp gi 2 (volume.restrict (⋃ α, U α)))
    (h : ∀ α, HasWeakPartialDerivOn (U α) i u gi) :
    HasWeakPartialDerivOn (⋃ α, U α) i u gi := by
  intro φ hφ hφc hφU
  obtain ⟨N, ψ, hψs, hψc, hψsub, hψsum⟩ :=
    exists_smooth_decomposition_of_open_cover hUopen hφ hφc hφU
  have hWmeas : MeasurableSet (⋃ α, U α) := (isOpen_iUnion hUopen).measurableSet
  have hderiv : ∀ y, (fderiv ℝ φ y) (basisVec i) =
      ∑ j ∈ Finset.range N, (fderiv ℝ (ψ j) y) (basisVec i) := by
    intro y
    have hfun : φ = fun z => ∑ j ∈ Finset.range N, ψ j z := by
      funext z
      exact (hψsum z).symm
    rw [hfun, fderiv_fun_sum (fun j _ => ((hψs j).differentiable (by simp)).differentiableAt)]
    simp
  have hLHS : ∫ y in ⋃ α, U α, u y * (fderiv ℝ φ y) (basisVec i) ∂volume =
      ∑ j ∈ Finset.range N,
        ∫ y in ⋃ α, U α, u y * (fderiv ℝ (ψ j) y) (basisVec i) ∂volume := by
    rw [← integral_finset_sum _ fun j _ =>
      integrable_mul_restrict hu (memL2_restrict_fderiv (hψs j) (hψc j) i)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show u y * (fderiv ℝ φ y) (basisVec i) =
      ∑ j ∈ Finset.range N, u y * (fderiv ℝ (ψ j) y) (basisVec i)
    rw [hderiv y, Finset.mul_sum]
  have hRHS : ∫ y in ⋃ α, U α, gi y * φ y ∂volume =
      ∑ j ∈ Finset.range N, ∫ y in ⋃ α, U α, gi y * ψ j y ∂volume := by
    rw [← integral_finset_sum _ fun j _ =>
      integrable_mul_restrict hgi (memL2_restrict_of_contDiff (hψs j) (hψc j))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show gi y * φ y = ∑ j ∈ Finset.range N, gi y * ψ j y
    rw [← hψsum y, Finset.mul_sum]
  have hpiece : ∀ j ∈ Finset.range N,
      ∫ y in ⋃ α, U α, u y * (fderiv ℝ (ψ j) y) (basisVec i) ∂volume =
        -∫ y in ⋃ α, U α, gi y * ψ j y ∂volume := by
    intro j hj
    obtain ⟨α, hα⟩ := hψsub j (Finset.mem_range.mp hj)
    have hsub : U α ⊆ ⋃ β, U β := Set.subset_iUnion U α
    have hz1 : ∀ y ∈ (⋃ β, U β) \ U α, u y * (fderiv ℝ (ψ j) y) (basisVec i) = 0 := by
      intro y hy
      have hy' : y ∉ tsupport (ψ j) := fun hc => hy.2 (hα hc)
      have hzero : fderiv ℝ (ψ j) y = 0 := by
        by_contra hne
        exact hy' (support_fderiv_subset ℝ (by simpa only [Function.mem_support] using hne))
      rw [hzero]
      simp
    have hz2 : ∀ y ∈ (⋃ β, U β) \ U α, gi y * ψ j y = 0 := by
      intro y hy
      have hy' : y ∉ tsupport (ψ j) := fun hc => hy.2 (hα hc)
      rw [image_eq_zero_of_notMem_tsupport hy', mul_zero]
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero
        (μ := (volume : Measure (Vec d)))
        (f := fun y => u y * (fderiv ℝ (ψ j) y) (basisVec i)) hWmeas hsub hz1,
      setIntegral_eq_of_subset_of_forall_diff_eq_zero
        (μ := (volume : Measure (Vec d))) (f := fun y => gi y * ψ j y) hWmeas hsub hz2]
    exact h α (ψ j) (hψs j) (hψc j) hα
  rw [hLHS, hRHS, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hpiece

/-- **Locality of the weak gradient on an open cover.** -/
theorem hasWeakGradientOn_iUnion {ι : Type*} {U : ι → Set (Vec d)}
    (hUopen : ∀ α, IsOpen (U α)) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (⋃ α, U α)))
    (hDu : ∀ i, MemLp (fun y => Du y i) 2 (volume.restrict (⋃ α, U α)))
    (h : ∀ α, HasWeakGradientOn (U α) u Du) :
    HasWeakGradientOn (⋃ α, U α) u Du :=
  fun i => hasWeakPartialDerivOn_iUnion hUopen hu (hDu i) fun α => h α i

/-- **The cover form of locality.**  If the open sets `U α` cover `W` and each
sits inside `W`, a common weak gradient on every `U α` is the weak gradient on
`W`. -/
theorem hasWeakGradientOn_of_open_cover {ι : Type*} {W : Set (Vec d)} {U : ι → Set (Vec d)}
    (hUopen : ∀ α, IsOpen (U α)) (hUW : ∀ α, U α ⊆ W) (hcover : W ⊆ ⋃ α, U α)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict W))
    (hDu : ∀ i, MemLp (fun y => Du y i) 2 (volume.restrict W))
    (h : ∀ α, HasWeakGradientOn (U α) u Du) :
    HasWeakGradientOn W u Du := by
  have hWeq : W = ⋃ α, U α := Set.Subset.antisymm hcover (Set.iUnion_subset hUW)
  rw [hWeq] at hu hDu ⊢
  exact hasWeakGradientOn_iUnion hUopen hu hDu h

/-- **Locality across two open sets.** -/
theorem hasWeakGradientOn_union {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ∪ V)))
    (hDu : ∀ i, MemLp (fun y => Du y i) 2 (volume.restrict (U ∪ V)))
    (hUw : HasWeakGradientOn U u Du) (hVw : HasWeakGradientOn V u Du) :
    HasWeakGradientOn (U ∪ V) u Du := by
  refine hasWeakGradientOn_of_open_cover (U := fun b : Bool => cond b U V) ?_ ?_ ?_ hu hDu ?_
  · intro b
    cases b
    · exact hV
    · exact hU
  · intro b
    cases b
    · exact Set.subset_union_right
    · exact Set.subset_union_left
  · intro y hy
    rcases hy with hy | hy
    · exact Set.mem_iUnion.2 ⟨true, hy⟩
    · exact Set.mem_iUnion.2 ⟨false, hy⟩
  · intro b
    cases b
    · exact hVw
    · exact hUw

end

end Algsuperdiff.Section4.Provider.ExcessDecay
