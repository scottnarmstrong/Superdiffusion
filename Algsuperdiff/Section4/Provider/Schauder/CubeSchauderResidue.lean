/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderOneStep
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderPoincare
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderFreezingResidue
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWeylRepresentative

/-!
# Cube Schauder: the harmonic competitor and its forcing residue

The interior one step of `CubeSchauderOneStep` consumes two things: a competitor
`v` harmonic on the window, and a bound on the `L̲²` distance `‖u - v‖`.  This
module produces both, from the freezing step and Weyl's lemma, for the
**forced** equation `-Δu = ∇·G` with `G ∈ C^{0,1/2}`.

The chain, on the window `W = (x + □_n) ∩ □_m`:

1. *freezing* (`CubeSchauderFreezing.exists_frozenHarmonicReplacement`, at the
   base point `x` and the constant `c = G(x)`): a corrector `w ∈ H¹₀(W)` with
   `u - w` weakly harmonic and `∫_W |∇w|² ≤ ∫_W |G - G(x)|² ≤ d KG² 3ⁿ |W|` —
   the **freezing gain**, one half-power of the scale;
2. *the coordinate dictionary*
   (`CubeSchauderFreezingResidue.sum_toReal_eLpNorm_grad_le_of_dirichletEnergy_le`):
   `Σᵢ ‖∂ᵢw‖_{L²(W)} ≤ d KG √(3ⁿ|W|)`;
3. *the Dirichlet Poincaré* (`CubeSchauderPoincare`, at the inscribing cube `x
   + □_n`): `‖w‖_{L²(W)} ≤ C_ⁿ Σᵢ ‖∂ᵢw‖_{L²(W)}`, hence after dividing by
   `|W|^{1/2}`,  `‖w‖_{L̲²(W)} ≤ C_P d KG 3ⁿ √(3ⁿ)`;
4. *Weyl* (`ExcessDecay.Schauder.exists_harmonicRepresentative_memLp`): a genuine
   classically harmonic representative `v` of `u - w`, so that `u - v = w` almost
   everywhere on `W`.

The output is exactly the remainder slot of `excessDecay_oneStep_lipschitz`:

```text
  3^{-n} · ‖u - v‖_{L̲²((x+□_{n-2}) ∩ □_m)} ≤ C_res(d) · KG · √(3ⁿ) .
```

The `√(3ⁿ)` is the whole point: the remainder decays at `3^{-1/2}` per triadic
scale, while the one step contracts at `3^{-1}` per scale — the gap the
Campanato iteration needs.

## Main results

* `exists_frozenHarmonicReplacement_truncatedWindow` — steps 1--2.
* `schauderResidueConst` — `√((3⁴)^d) · C_P(d) · d`.
* `exists_harmonicCompetitor_residue` — the whole chain.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`), the
  harmonic-approximation display `e.harmapprox.Sch.onealpha`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open Homogenization
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. Two small dictionary lemmas -/

/-- `‖·‖_{L̲²(W)}` only sees the almost-everywhere class on `W`. -/
theorem normalizedL2On_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : ∀ᵐ y ∂(volume.restrict W), f y = g y) :
    normalizedL2On W f = normalizedL2On W g := by
  have hint : (∫ y in W, f y ^ 2 ∂volume) = ∫ y in W, g y ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  unfold normalizedL2On volumeAverage
  rw [hint]

/-- The oscillation of a `C^{0,1/2}` field on a truncated window. -/
theorem vecNormSq_sub_le_of_holderSeminormBoundOn_truncatedWindow {m n : ℤ} {x : Vec d}
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hG : HolderSeminormBoundOn (truncatedWindow x m n) (1 / 2) KG G)
    {p : Vec d} (hp : p ∈ truncatedWindow x m n) {q : Vec d}
    (hq : q ∈ truncatedWindow x m n) :
    vecNormSq (G p - G q) ≤ (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ n) := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hdiam : ‖p - q‖ ≤ (3 : ℝ) ^ n := norm_sub_le_of_mem_truncatedWindow_pair hp hq
  have hmono : ‖p - q‖ ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hdiam (by norm_num)
  have hbd : ‖G p - G q‖ ≤ KG * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) :=
    (hG p hp q hq).trans (mul_le_mul_of_nonneg_left hmono hKG)
  have hsq : ‖G p - G q‖ ^ 2 ≤ (KG * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hbd 2
  have hexp : (KG * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) ^ 2 = KG ^ 2 * (3 : ℝ) ^ n := by
    rw [mul_pow, ← Real.rpow_natCast (((3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hs.le]
    norm_num
  have hdim := vecNormSq_le_dim_mul_sq_norm (G p - G q)
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hchain : (d : ℝ) * ‖G p - G q‖ ^ 2 ≤ (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ n) := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left hsq hdnn
  linarith only [hdim, hchain]

/-! ## 2. The freezing step on a truncated window -/

/-- **The freezing step on the one-step window, with the gain in coordinate
`L²` form.**

If `u` solves `-Δu = ∇·G` on `□_m` and `[G]_{C^{0,1/2}(□_m)} ≤ KG`, then on the
window `W = (x + □_n) ∩ □_m` there is a corrector `w ∈ H¹₀(W)` making `u - w`
weakly harmonic and obeying

```text
  Σᵢ ‖∂ᵢ w‖_{L²(W)} ≤ d · KG · √(3ⁿ · |W|) .
```
-/
theorem exists_frozenHarmonicReplacement_truncatedWindow [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u G) :
    ∃ w : H10Function (truncatedWindow x m n),
      IsWeaklyHarmonicOn (truncatedWindow x m n)
          (u.restrict (isOpen_truncatedWindow x m n)
            (truncatedWindow_subset_domain x m n) - w.toH1Function) ∧
        ∑ i : Fin d,
            (eLpNorm (fun y => w.toH1Function.grad y i) 2
              (volume.restrict (truncatedWindow x m n))).toReal
          ≤ (d : ℝ) * KG *
              Real.sqrt ((3 : ℝ) ^ n * (volume (truncatedWindow x m n)).toReal) := by
  set W : Set (Vec d) := truncatedWindow x m n with hWdef
  have hWsub : W ⊆ openCubeSet (originCube d m) := truncatedWindow_subset_domain x m n
  have hWopen : IsOpen W := isOpen_truncatedWindow x m n
  have hWdom : IsOpenBoundedConvexDomain W := isOpenBoundedConvexDomain_truncatedWindow x m n
  have hWne : W.Nonempty := truncatedWindow_nonempty n hx
  have hxW : x ∈ W := mem_truncatedWindow_self n hx
  haveI : IsFiniteMeasure (volumeMeasureOn W) := hWdom.isFiniteMeasure_restrict_volume
  have hGW : MemVectorL2 W G := hGL2.mono_measure (Measure.restrict_mono hWsub le_rfl)
  have huW := Algsuperdiff.Section4.Provider.ExcessDecay.isDivFormWeakSolutionOn_restrict
    hWopen hWsub hu
  obtain ⟨w, _, hharm, henergy⟩ :=
    exists_frozenHarmonicReplacement hWdom hWne _ hGW huW (G x)
  refine ⟨w, hharm, ?_⟩
  have hGhol : HolderSeminormBoundOn W (1 / 2) KG G := hG.mono_set hWsub
  have hGc : MemVectorL2 W (fun y => G y - G x) := hGW.sub (memLp_const (G x))
  have hint : IntegrableOn (fun y => vecNormSq (G y - G x)) W volume :=
    integrableOn_vecNormSq_of_memVectorL2 hGc
  have hbd : ∀ y ∈ W, vecNormSq (G y - G x) ≤ (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ n) := fun y hy =>
    vecNormSq_sub_le_of_holderSeminormBoundOn_truncatedWindow hKG hGhol hy hxW
  have hconst : IntegrableOn (fun _ : Vec d => (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ n)) W volume :=
    integrable_const _
  have hmono := setIntegral_mono_on hint hconst (measurableSet_truncatedWindow x m n) hbd
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hmono
  have hE := henergy.trans hmono
  have hstep := sum_toReal_eLpNorm_grad_le_of_dirichletEnergy_le w.toH1Function hE
  refine hstep.trans (le_of_eq ?_)
  exact sqrt_freezing_budget (d : ℝ) KG ((3 : ℝ) ^ n) ((volume W).toReal)
    (Nat.cast_nonneg d) hKG

/-! ## 3. The residue constant and the full chain -/

/-- The residue constant of the forced one step:
`√((3⁴)^d) · C_Poincaré(d) · d`.  The `√((3⁴)^d)` is the volume ratio of the two
truncated windows `U_2 ⊆ U_0`, the `d` the coordinate dictionary's
Cauchy--Schwarz factor. -/
def schauderResidueConst (d : ℕ) : ℝ :=
  Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) * (schauderDirichletPoincareConst d * (d : ℝ))

theorem schauderResidueConst_nonneg (d : ℕ) : 0 ≤ schauderResidueConst d :=
  mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d))

/-- **The harmonic competitor of the forced equation, with its residue priced.**

For `u` solving `-Δu = ∇·G` on `□_m` with `[G]_{C^{0,1/2}(□_m)} ≤ KG`, and for
every base point `x ∈ □_m` and scale `n ≤ m`, there is a function `v` which is

* classically harmonic on the window `W = (x + □_n) ∩ □_m` (Weyl), and
* globally square integrable,

with the one-step remainder slot bounded by the **freezing gain**:

```text
  3^{-n} · ‖u - v‖_{L̲²((x+□_{n-2}) ∩ □_m)} ≤ schauderResidueConst d · KG · √(3ⁿ) .
```
-/
theorem exists_harmonicCompetitor_residue [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (u : H1Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u G) :
    ∃ v : Vec d → ℝ,
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m n) ∧
        MemLp v 2 (volume : Measure (Vec d)) ∧
        (3 : ℝ) ^ (-n) *
            normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - v y)
          ≤ schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n) := by
  set W : Set (Vec d) := truncatedWindow x m n with hWdef
  have hWsub : W ⊆ openCubeSet (originCube d m) := truncatedWindow_subset_domain x m n
  have hWopen : IsOpen W := isOpen_truncatedWindow x m n
  have hWmeas : MeasurableSet W := measurableSet_truncatedWindow x m n
  have hWpos : 0 < (volume W).toReal := volume_toReal_truncatedWindow_pos x hx hnm
  obtain ⟨w, hharm, hgrad⟩ :=
    exists_frozenHarmonicReplacement_truncatedWindow (n := n) hx u hKG hGL2 hG hu
  obtain ⟨v, hvharm, hvmem, hvae⟩ :=
    exists_harmonicRepresentative_memLp hWopen hharm
  refine ⟨v, hvharm, hvmem, ?_⟩
  -- `u - v = w` almost everywhere on the window
  have hae : ∀ᵐ y ∂(volume.restrict W), u.toFun y - v y = w.toH1Function.toFun y := by
    filter_upwards [hvae.restrict, MeasureTheory.self_mem_ae_restrict hWmeas] with y hy hyW
    have hsub : (u.restrict (isOpen_truncatedWindow x m n)
        (truncatedWindow_subset_domain x m n) - w.toH1Function).toFun y
        = u.toFun y - w.toH1Function.toFun y := by
      simp only [H1Function.sub_toFun]
      rfl
    rw [hy, Set.indicator_of_mem hyW, hsub]
    ring
  have hW2sub : truncatedWindow x m (n - 2) ⊆ W := truncatedWindow_mono x m (by omega)
  have hae2 : ∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
      u.toFun y - v y = w.toH1Function.toFun y :=
    ae_restrict_of_ae_restrict_of_subset hW2sub hae
  -- the `L²` legs of the transfer
  have hwW : MemLp w.toH1Function.toFun 2 (volume.restrict W) := by
    have h := w.toH1Function.memL2
    simpa only [volumeMeasureOn] using h
  -- Poincaré at the inscribing cube `x + □_n`
  have hinscribe : ∀ y ∈ W, ∀ j : Fin d,
      x j - (1 / 2 : ℝ) * (3 : ℝ) ^ n < y j ∧ y j < x j + (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    intro y hy j
    have h := mem_image_add_openCubeSet_iff.1 (truncatedWindow_subset_translate x m n hy) j
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have hpoin := eLpNorm_le_schauderDirichletPoincare hWmeas x n hinscribe w
  have hpoin' : (eLpNorm w.toH1Function.toFun 2 (volume.restrict W)).toReal
      ≤ schauderDirichletPoincareConst d * (3 : ℝ) ^ n *
        ((d : ℝ) * KG * Real.sqrt ((3 : ℝ) ^ n * (volume W).toReal)) := by
    refine hpoin.trans (mul_le_mul_of_nonneg_left hgrad ?_)
    exact mul_nonneg (schauderDirichletPoincareConst_nonneg d)
      (zpow_pos (by norm_num) n).le
  -- convert to the normalized seminorm on `W`
  have hsqrtV : Real.sqrt ((3 : ℝ) ^ n * (volume W).toReal)
      = Real.sqrt ((3 : ℝ) ^ n) * Real.sqrt ((volume W).toReal) :=
    Real.sqrt_mul (zpow_pos (by norm_num) n).le _
  have hVne : Real.sqrt ((volume W).toReal) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hWpos)
  have hnormW : normalizedL2On W w.toH1Function.toFun
      ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG *
        ((3 : ℝ) ^ n * Real.sqrt ((3 : ℝ) ^ n)) := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div hwW, div_le_iff₀ (Real.sqrt_pos.2 hWpos)]
    refine hpoin'.trans (le_of_eq ?_)
    rw [hsqrtV]
    ring
  -- transfer to the inner window `U_2`
  have hW2 : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - v y)
      ≤ Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ n * Real.sqrt ((3 : ℝ) ^ n))) := by
    have hcongr2 : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - v y)
        = normalizedL2On (truncatedWindow x m (n - 2)) w.toH1Function.toFun :=
      normalizedL2On_congr_ae hae2
    have htrans := normalizedL2On_truncatedWindow_le (l := n) (k := n - 2) hx
      (by omega : n - 2 - 1 ≤ m) hnm (by omega) (f := w.toH1Function.toFun) hwW
    rw [show n - (n - 2) + 2 = (4 : ℤ) by ring] at htrans
    rw [hcongr2]
    refine htrans.trans (mul_le_mul_of_nonneg_left hnormW (Real.sqrt_nonneg _))
  -- multiply by `3^{-n}`
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hW2 h3n.le
  refine hmul.trans (le_of_eq ?_)
  have hcancel : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  rw [schauderResidueConst]
  calc (3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ n * Real.sqrt ((3 : ℝ) ^ n))))
      = Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ)) * KG *
          Real.sqrt ((3 : ℝ) ^ n) * ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) := by ring
    _ = Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ)) * KG *
          Real.sqrt ((3 : ℝ) ^ n) := by rw [hcancel, mul_one]

end

end Algsuperdiff.Section4.Provider.Schauder
