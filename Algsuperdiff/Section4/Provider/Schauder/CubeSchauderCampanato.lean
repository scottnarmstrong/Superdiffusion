/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Schauder.CubeSchauderResidue

/-!
# Cube Schauder: the Campanato bound of the zero-datum solution

## The rate resolution, made explicit

Per triadic step of size `k` the two rates are

```text
  theta_k = lipschitzContractionConst d · 3^{-k}      (the contraction)
  rho_k   = √(3^{-k})                                  (the freezing gain)
```

`theta_k / rho_k = lipschitzContractionConst d · √(3^{-k}) → 0`, so the gap is
uniform as soon as `k` is large; `schauderStepSize d` is such a `k` (and `≥ 3`,
the one-step machinery's own requirement).  With the `C^{0,1/2}` interior atom
one would instead get `theta_k = C(d)·√(3^{-k}) = C(d)·rho_k` — no gap at any
`k`, the Campanato exponent strictly below `1/2` and the frozen external's
inclusive endpoint `s ≤ 1/2` unreachable.  That is why the composition is routed
through the Lipschitz atom.

At the sharp gap the Campanato bound reads, on the window family
`W_j = (x + □_j) ∩ □_m` of a point `x` of the interior half-cube `□_{m-1}`,

```text
  E(w, W_j) ≤ schauderCampanatoConst d · KG · √(3^j)     for every j ≤ m,
```

`w` the zero-datum `H¹₀(□_m)` solution of `-Δw = ∇·G` and `KG` the `C^{0,1/2}`
seminorm of `G` — the Campanato characterization of `∇w ∈ C^{0,1/2}`, with
exponent **exactly** `1/2`.

## Main results

* `exists_schauderStepSize` / `schauderStepSize` / `schauderStepSize_gap` — the
  step size and the machine-checked rate gap `theta < rho`.
* `excessDecay_oneStep_forced` — the one step for the forced equation.
* `affineExcess_initial_le` — the excess at the top scale.
* `affineExcess_le_campanato_sublattice` — the iterated bound at the scales
  `m - i·k₀`.
* `affineExcess_le_campanato` — the same at **every** scale `j ≤ m`.

## What this module does *not* do

It is the **interior** regime: the base point `x` is restricted to the interior
half-cube `□_{m-1}`, which is what makes the geometry slot `x + □_{j-2} ⊆ □_m`
of the one-step producer available at every scale.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, displays `e.Sch1a.1`--`e.Sch1a.2`.
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

/-! ## 1. Two arithmetic helpers -/

/-- `√(t^i) = (√t)^i`. -/
theorem sqrt_pow_nat {t : ℝ} (ht : 0 ≤ t) (i : ℕ) :
    Real.sqrt (t ^ i) = Real.sqrt t ^ i := by
  induction i with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ht n), ih, pow_succ]

/-- The triadic scale at step `i` of the iteration factorizes. -/
theorem zpow_sub_mul_step (m : ℤ) (k i : ℕ) :
    (3 : ℝ) ^ (m - (i : ℤ) * (k : ℤ)) = (3 : ℝ) ^ m * ((3 : ℝ) ^ (-(k : ℤ))) ^ i := by
  have hne : (3 : ℝ) ≠ 0 := by norm_num
  rw [show m - (i : ℤ) * (k : ℤ) = m + (-(k : ℤ)) * (i : ℤ) by ring, zpow_add₀ hne,
    zpow_mul, zpow_natCast]

/-! ## 2. The step size and the rate gap -/

/-- **The rate gap exists.**  There is a step size `k ≥ 3` at which the
contraction rate `C_contr(d)·3^{-k}` is strictly below the freezing rate
`√(3^{-k})`.

Numerically: any `k ≥ 3` with `3^{k/2} > lipschitzContractionConst d` works, i.e.
any `k ≥ max(3, 2 log₃ C_contr(d) + 1)`. -/
theorem exists_schauderStepSize (d : ℕ) [NeZero d] :
    ∃ k : ℕ, 3 ≤ k ∧
      lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ))
        < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := by
  have hC0 : 0 ≤ lipschitzContractionConst d := lipschitzContractionConst_nonneg d
  set C : ℝ := lipschitzContractionConst d with hCdef
  have hden : (0 : ℝ) < C + 1 := by linarith only [hC0]
  have heps : (0 : ℝ) < (1 / (C + 1)) ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨max n 3, le_max_right n 3, ?_⟩
  set k : ℕ := max n 3 with hkdef
  have hpow : (3 : ℝ) ^ (-(k : ℤ)) = (1 / 3 : ℝ) ^ k := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hmono : (1 / 3 : ℝ) ^ k ≤ (1 / 3 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left n 3)
  have hlt : (3 : ℝ) ^ (-(k : ℤ)) < (1 / (C + 1)) ^ 2 := by
    rw [hpow]
    linarith only [hmono, hn]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hrho : Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) < 1 / (C + 1) := by
    have h := Real.sqrt_lt_sqrt hpos.le hlt
    rwa [Real.sqrt_sq (by positivity)] at h
  have hrhopos : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
      = (3 : ℝ) ^ (-(k : ℤ)) := Real.mul_self_sqrt hpos.le
  have hCr : C * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) < 1 := by
    have h1 : C * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ≤ C * (1 / (C + 1)) :=
      mul_le_mul_of_nonneg_left hrho.le hC0
    have h2 : C * (1 / (C + 1)) < 1 := by
      rw [mul_one_div, div_lt_one hden]
      linarith only []
    linarith only [h1, h2]
  calc C * (3 : ℝ) ^ (-(k : ℤ))
      = (C * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))) * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := by
        rw [mul_assoc, hsq]
    _ < 1 * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := mul_lt_mul_of_pos_right hCr hrhopos
    _ = Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := one_mul _

/-- **The step size of the Campanato iteration**, `k₀(d)`. -/
def schauderStepSize (d : ℕ) [NeZero d] : ℕ := (exists_schauderStepSize d).choose

theorem schauderStepSize_ge_three (d : ℕ) [NeZero d] : 3 ≤ schauderStepSize d :=
  (exists_schauderStepSize d).choose_spec.1

/-- **The rate gap, machine-checked.**  `theta = C_contr(d)·3^{-k₀} < √(3^{-k₀}) = rho`. -/
theorem schauderStepSize_gap (d : ℕ) [NeZero d] :
    lipschitzContractionConst d * (3 : ℝ) ^ (-(schauderStepSize d : ℤ))
      < Real.sqrt ((3 : ℝ) ^ (-(schauderStepSize d : ℤ))) :=
  (exists_schauderStepSize d).choose_spec.2

/-! ## 3. The one step for the forced equation -/

/-- **The interior one step, forced.**

For the solution `u` of `-Δu = ∇·G` on `□_m` with `[G]_{C^{0,1/2}} ≤ KG`, at a
base point `x` and a scale `n` in the interior regime `x + □_{n-2} ⊆ □_m`:

```text
  E(u, W_{n-k}) ≤ C_contr(d)·3^{-k}·E(u, W_n)
                   + C_rem(d,k)·C_res(d)·KG·√(3ⁿ) .
```
-/
theorem excessDecay_oneStep_forced [NeZero d] (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u G) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun
      ≤ lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ))
            * affineExcess (truncatedWindow x m n) u.toFun
        + lipschitzRemainderConst d k *
            (schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n)) := by
  obtain ⟨v, hvharm, hvmem, hres⟩ :=
    exists_harmonicCompetitor_residue (n := n) hx hnm u hKG hGL2 hG hu
  have hWsub : truncatedWindow x m n ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m n
  have huW : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) := by
    have h : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [volumeMeasureOn] using u.memL2
    exact memLp_restrict_of_subset hWsub h
  have hvW : MemLp v 2 (volume.restrict (truncatedWindow x m n)) :=
    hvmem.restrict _
  have hharm2 : HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2)) :=
    fun p hp => hvharm p (Set.image_mono (truncatedWindow_mono x m (by omega)) hp)
  have hstep := excessDecay_oneStep_lipschitz hd hk hx hnm hcube huW hvW hharm2
  have hfinal := mul_le_mul_of_nonneg_left hres (lipschitzRemainderConst_nonneg d k)
  linarith only [hstep, hfinal]

/-! ## 4. The excess at the top scale -/

/-- The constant of the top-scale excess: `9 · √((3²)^d) · C_Poincaré(d) · d`. -/
def schauderInitialConst (d : ℕ) : ℝ :=
  9 * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * (schauderDirichletPoincareConst d * (d : ℝ))

theorem schauderInitialConst_nonneg (d : ℕ) : 0 ≤ schauderInitialConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d))

/-- **The excess of the zero-datum solution at the top scale.**

`E(w, (x+□_m) ∩ □_m) ≤ schauderInitialConst d · KG · √(3^m)`.  The proof is the
freezing identity at the constant `G(0)` (a zero-trace test function does not see
a constant forcing), the sharp energy bound, the coordinate dictionary and the
Dirichlet Poincaré inequality — the same four steps as the one-step residue, run
once at the top scale. -/
theorem affineExcess_initial_le [NeZero d] (hd : d ≠ 0) {m : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (truncatedWindow x m m) u.toFun
      ≤ schauderInitialConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
  have hQdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet _
  haveI : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    hQdom.isFiniteMeasure_restrict_volume
  have hvolQ : (volume (openCubeSet (originCube d m))).toReal = ((3 : ℝ) ^ m) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    rfl
  have hvolQpos : (0 : ℝ) < (volume (openCubeSet (originCube d m))).toReal := by
    rw [hvolQ]
    positivity
  -- the frozen equation and the sharp energy bound
  have hGc : MemVectorL2 (openCubeSet (originCube d m)) (fun y => G y - G 0) :=
    hGL2.sub (memLp_const (G 0))
  have hufroz : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function (fun y => G y - G 0) :=
    isDivFormWeakSolutionOn_sub_const hGL2 (G 0) hu
  have henergy := dirichletEnergy_le_of_isDivFormWeakSolutionOn_one hGc u hufroz
  -- the oscillation bound at the base point `0`
  have h0 : (0 : Vec d) ∈ openCubeSet (originCube d m) :=
    zero_mem_openCubeSet_originCube m
  have hint : IntegrableOn (fun y => vecNormSq (G y - G 0))
      (openCubeSet (originCube d m)) volume :=
    integrableOn_vecNormSq_of_memVectorL2 hGc
  have hbd : ∀ y ∈ openCubeSet (originCube d m),
      vecNormSq (G y - G 0) ≤ (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ m) := by
    intro y hy
    have h := vecNormSq_sub_le_of_holderSeminormBoundOn_openCubeSet
      (Q := originCube d m) hKG hG h0 hy
    have hscale : cubeScaleFactor (originCube d m) = (3 : ℝ) ^ m := rfl
    rwa [hscale] at h
  have hconst : IntegrableOn (fun _ : Vec d => (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ m))
      (openCubeSet (originCube d m)) volume := integrable_const _
  have hmono := setIntegral_mono_on hint hconst (measurableSet_openCubeSet _) hbd
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hmono
  have hE := henergy.trans hmono
  have hsum := sum_toReal_eLpNorm_grad_le_of_dirichletEnergy_le u.toH1Function hE
  have hsum' : ∑ i : Fin d,
      (eLpNorm (fun y => u.toH1Function.grad y i) 2
        (volume.restrict (openCubeSet (originCube d m)))).toReal
      ≤ (d : ℝ) * KG *
        Real.sqrt ((3 : ℝ) ^ m * (volume (openCubeSet (originCube d m))).toReal) := by
    refine hsum.trans (le_of_eq ?_)
    exact sqrt_freezing_budget (d : ℝ) KG ((3 : ℝ) ^ m)
      ((volume (openCubeSet (originCube d m))).toReal) (Nat.cast_nonneg d) hKG
  -- the Dirichlet Poincaré at the inscribing cube `0 + □_m`
  have hinscribe : ∀ y ∈ openCubeSet (originCube d m), ∀ j : Fin d,
      (0 : Vec d) j - (1 / 2 : ℝ) * (3 : ℝ) ^ m < y j ∧
        y j < (0 : Vec d) j + (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    intro y hy j
    have h := mem_openCubeSet_originCube_iff.1 hy j
    exact ⟨by simpa using by linarith only [h.1], by simpa using by linarith only [h.2]⟩
  have hpoin := eLpNorm_le_schauderDirichletPoincare (measurableSet_openCubeSet _) 0 m
    hinscribe u
  have hpoin' : (eLpNorm u.toFun 2 (volume.restrict (openCubeSet (originCube d m)))).toReal
      ≤ schauderDirichletPoincareConst d * (3 : ℝ) ^ m *
        ((d : ℝ) * KG *
          Real.sqrt ((3 : ℝ) ^ m * (volume (openCubeSet (originCube d m))).toReal)) := by
    refine hpoin.trans (mul_le_mul_of_nonneg_left hsum' ?_)
    exact mul_nonneg (schauderDirichletPoincareConst_nonneg d) (zpow_pos (by norm_num) m).le
  have huQ : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.toH1Function.memL2
  have hsqrtV : Real.sqrt ((3 : ℝ) ^ m * (volume (openCubeSet (originCube d m))).toReal)
      = Real.sqrt ((3 : ℝ) ^ m) *
        Real.sqrt ((volume (openCubeSet (originCube d m))).toReal) :=
    Real.sqrt_mul (zpow_pos (by norm_num) m).le _
  have hnormQ : normalizedL2On (openCubeSet (originCube d m)) u.toFun
      ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG *
        ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)) := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div huQ, div_le_iff₀ (Real.sqrt_pos.2 hvolQpos)]
    refine hpoin'.trans (le_of_eq ?_)
    rw [hsqrtV]
    ring
  -- transfer to the truncated window at the top scale
  have hWQ : truncatedWindow x m m ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m m
  have hWpos : (0 : ℝ) < (volume (truncatedWindow x m m)).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hratio : (volume (openCubeSet (originCube d m))).toReal /
      (volume (truncatedWindow x m m)).toReal ≤ ((3 : ℝ) ^ (2 : ℤ)) ^ d := by
    have hlo : ((3 : ℝ) ^ (m - 2)) ^ d ≤ (volume (truncatedWindow x m m)).toReal :=
      (volume_toReal_truncatedWindow_bounds x hx (by omega)).1
    rw [div_le_iff₀ hWpos, hvolQ]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hlo (by positivity))
    rw [← mul_pow]
    congr 1
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hintQ : IntegrableOn (fun y => u.toFun y ^ 2) (openCubeSet (originCube d m)) :=
    (memLp_two_iff_integrable_sq huQ.aestronglyMeasurable).1 huQ
  have htrans : normalizedL2On (truncatedWindow x m m) u.toFun
      ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        normalizedL2On (openCubeSet (originCube d m)) u.toFun := by
    refine (normalizedL2On_le_of_subset hWQ hvolQpos hWpos hintQ).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hratio) (normalizedL2On_nonneg _ _)
  -- the excess against the zero competitor
  have hzero : affineExcessRaw (truncatedWindow x m m) u.toFun
      ≤ normalizedL2On (truncatedWindow x m m) u.toFun := by
    have h := affineExcessRaw_le_normalizedL2On_sub_const (truncatedWindow x m m) u.toFun 0
    have hfun : (fun y => u.toFun y - 0) = u.toFun := by funext y; ring
    rwa [hfun] at h
  obtain ⟨_, hnorm⟩ := rpow_volume_truncatedWindow_bounds hd x hx (by omega : m - 1 ≤ m)
  have hchain : affineExcess (truncatedWindow x m m) u.toFun
      ≤ 9 * (3 : ℝ) ^ (-m) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)))) := by
    have hup : normalizedL2On (truncatedWindow x m m) u.toFun
        ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ) * KG *
            ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))) :=
      htrans.trans (mul_le_mul_of_nonneg_left hnormQ (Real.sqrt_nonneg _))
    have hraw : affineExcessRaw (truncatedWindow x m m) u.toFun
        ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ) * KG *
            ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))) := hzero.trans hup
    have hnn : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))) := by
      have h1 : (0 : ℝ) ≤ schauderDirichletPoincareConst d :=
        schauderDirichletPoincareConst_nonneg d
      have h2 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ m) := Real.sqrt_nonneg _
      have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
      have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg h1 h4) hKG) (mul_nonneg h3.le h2))
    show ((volume (truncatedWindow x m m)).toReal) ^ (-(d : ℝ)⁻¹) *
      affineExcessRaw (truncatedWindow x m m) u.toFun ≤ _
    exact mul_le_mul hnorm hraw (affineExcessRaw_nonneg _ _) (by positivity)
  refine hchain.trans (le_of_eq ?_)
  have hcancel : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ m = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  rw [schauderInitialConst]
  calc 9 * (3 : ℝ) ^ (-m) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))))
      = 9 * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ)) * KG *
          Real.sqrt ((3 : ℝ) ^ m) * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ m) := by ring
    _ = 9 * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ)) * KG *
          Real.sqrt ((3 : ℝ) ^ m) := by rw [hcancel, mul_one]

/-! ## 5. The interior geometry at every scale -/

/-- **The interior regime.**  A base point of the half-cube `□_{m-1}` carries the
one-step producer's geometry slot at *every* scale `n ≤ m`. -/
theorem image_add_subset_of_mem_interior {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m - 1))) (hnm : n ≤ m) :
    (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m) := by
  refine image_add_openCubeSet_subset_of_mem hx ?_
  have h1 : (3 : ℝ) ^ (n - 2) ≤ (3 : ℝ) ^ (m - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hme : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - 1) * 3 := by
    have h := zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) (m - 1)
    have hidx : m - 1 + 1 = m := by ring
    rwa [hidx] at h
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) _
  linarith only [h1, hme, h3]

/-! ## 6. The Campanato bound -/

/-- **The Campanato constant** of the interior regime:
`C_init(d) + C_rem(d,k₀)·C_res(d)/(rho - theta)`, the amplitude of the geometric
sum at the sharp gap. -/
def schauderCampanatoConst (d : ℕ) [NeZero d] : ℝ :=
  schauderInitialConst d
    + lipschitzRemainderConst d (schauderStepSize d) * schauderResidueConst d /
        (Real.sqrt ((3 : ℝ) ^ (-(schauderStepSize d : ℤ)))
          - lipschitzContractionConst d * (3 : ℝ) ^ (-(schauderStepSize d : ℤ)))

/-- **The Campanato bound on the triadic sub-lattice.**

For the zero-datum solution `w` of `-Δw = ∇·G` on `□_m` with
`[G]_{C^{0,1/2}(□_m)} ≤ KG`, at every base point `x` of the interior half-cube
`□_{m-1}` and every step count `i`,

```text
  E(w, (x + □_{m-i·k₀}) ∩ □_m) ≤ schauderCampanatoConst d · KG · √(3^{m-i·k₀}) ,
```

`k₀ = schauderStepSize d`.  This is the `α = 1/2` Campanato bound: the excess
decays exactly like the square root of the scale. -/
theorem affineExcess_le_campanato_sublattice [NeZero d] (hd : d ≠ 0) {m : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m - 1)))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) (i : ℕ) :
    affineExcess (truncatedWindow x m (m - (i : ℤ) * (schauderStepSize d : ℤ))) u.toFun
      ≤ schauderCampanatoConst d * KG *
          Real.sqrt ((3 : ℝ) ^ (m - (i : ℤ) * (schauderStepSize d : ℤ))) := by
  have hgap := schauderStepSize_gap d
  have hk3 : 3 ≤ schauderStepSize d := schauderStepSize_ge_three d
  set k : ℕ := schauderStepSize d with hkdef
  have hxm : x ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega : m - 1 ≤ m) hx
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have h3k : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hrhonn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := Real.sqrt_nonneg _
  have hthetann : (0 : ℝ) ≤ lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) :=
    mul_nonneg (lipschitzContractionConst_nonneg d) h3k.le
  have hFnn : (0 : ℝ) ≤ lipschitzRemainderConst d k *
      (schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) :=
    mul_nonneg (lipschitzRemainderConst_nonneg d k)
      (mul_nonneg (mul_nonneg (schauderResidueConst_nonneg d) hKG) (Real.sqrt_nonneg _))
  -- the scale dictionary
  have hscale : ∀ j : ℕ, Real.sqrt ((3 : ℝ) ^ (m - (j : ℤ) * (k : ℤ)))
      = Real.sqrt ((3 : ℝ) ^ m) * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ^ j := by
    intro j
    rw [zpow_sub_mul_step, Real.sqrt_mul h3m.le, sqrt_pow_nat h3k.le]
  -- the recursion
  have hstep : ∀ j : ℕ,
      affineExcess (truncatedWindow x m (m - ((j + 1 : ℕ) : ℤ) * (k : ℤ))) u.toFun
        ≤ lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) *
            affineExcess (truncatedWindow x m (m - (j : ℤ) * (k : ℤ))) u.toFun
          + lipschitzRemainderConst d k *
              (schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) *
              Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ^ j := by
    intro j
    have hjk : (0 : ℤ) ≤ (j : ℤ) * (k : ℤ) := by positivity
    have hnm : m - (j : ℤ) * (k : ℤ) - 1 ≤ m := by linarith only [hjk]
    have hnle : m - (j : ℤ) * (k : ℤ) ≤ m := by linarith only [hjk]
    have hcube := image_add_subset_of_mem_interior hx hnle
    have hone := excessDecay_oneStep_forced hd hk3 hxm hnm hcube u.toH1Function hKG
      hGL2 hG hu
    have hidx : m - ((j + 1 : ℕ) : ℤ) * (k : ℤ) = m - (j : ℤ) * (k : ℤ) - (k : ℤ) := by
      push_cast
      ring
    rw [hidx]
    refine hone.trans (le_of_eq ?_)
    rw [hscale j]
    ring
  have hE0nn : (0 : ℝ) ≤
      affineExcess (truncatedWindow x m (m - ((0 : ℕ) : ℤ) * (k : ℤ))) u.toFun :=
    affineExcess_nonneg _ _
  have hmain := excess_le_geometric
    (E := fun j : ℕ => affineExcess (truncatedWindow x m (m - (j : ℤ) * (k : ℤ))) u.toFun)
    (theta := lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
    (rho := Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))))
    (F := lipschitzRemainderConst d k *
      (schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)))
    hthetann hgap hFnn hE0nn hstep i
  -- the top-scale excess
  have hinit : affineExcess (truncatedWindow x m (m - ((0 : ℕ) : ℤ) * (k : ℤ))) u.toFun
      ≤ schauderInitialConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
    have hz : m - ((0 : ℕ) : ℤ) * (k : ℤ) = m := by push_cast; ring
    rw [hz]
    exact affineExcess_initial_le hd hxm u hKG hGL2 hG hu
  -- the amplitude
  have hgap0 : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
      - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) := by
    linarith only [hgap]
  have hamp : affineExcess (truncatedWindow x m (m - ((0 : ℕ) : ℤ) * (k : ℤ))) u.toFun
      + lipschitzRemainderConst d k *
          (schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) /
        (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
          - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
      ≤ schauderCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
    have hid : lipschitzRemainderConst d k *
        (schauderResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) /
          (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
            - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
        = lipschitzRemainderConst d k * schauderResidueConst d /
            (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
              - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
          * KG * Real.sqrt ((3 : ℝ) ^ m) := by ring
    rw [hid, schauderCampanatoConst, ← hkdef]
    have hexp : (schauderInitialConst d +
        lipschitzRemainderConst d k * schauderResidueConst d /
          (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
            - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))) * KG *
          Real.sqrt ((3 : ℝ) ^ m)
        = schauderInitialConst d * KG * Real.sqrt ((3 : ℝ) ^ m) +
          lipschitzRemainderConst d k * schauderResidueConst d /
            (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
              - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
            * KG * Real.sqrt ((3 : ℝ) ^ m) := by ring
    rw [hexp]
    have hadd : ∀ a b c : ℝ, a ≤ b → a + c ≤ b + c := fun a b c h => by linarith only [h]
    exact hadd _ _ _ hinit
  have hpow : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ^ i := pow_nonneg hrhonn i
  have hfin := mul_le_mul_of_nonneg_right hamp hpow
  rw [hscale i]
  refine hmain.trans (hfin.trans (le_of_eq ?_))
  ring

/-! ## 7. Every scale -/

/-- The full-range Campanato constant: the sub-lattice constant, times the cost
of interpolating between two consecutive sub-lattice scales. -/
def schauderCampanatoFullConst (d : ℕ) [NeZero d] : ℝ :=
  windowRatioConst d (schauderStepSize d : ℤ) *
    Real.sqrt ((3 : ℝ) ^ (schauderStepSize d : ℤ)) * schauderCampanatoConst d

/-- **The Campanato bound at every scale.**

For the zero-datum solution `w` of `-Δw = ∇·G` on `□_m` with
`[G]_{C^{0,1/2}(□_m)} ≤ KG`, at every base point `x` of the interior half-cube
`□_{m-1}` and **every** scale `j ≤ m`,

```text
  E(w, (x + □_j) ∩ □_m) ≤ schauderCampanatoFullConst d · KG · √(3^j) .
```

This is the Morrey-dual form of `[∇w]_{C^{0,1/2}} ≤ C(d)·KG` on the interior:
the Campanato exponent is exactly `1/2`, and the constant is explicit. -/
theorem affineExcess_le_campanato [NeZero d] (hd : d ≠ 0) {m j : ℤ} (hjm : j ≤ m)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (m - 1)))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (truncatedWindow x m j) u.toFun
      ≤ schauderCampanatoFullConst d * KG * Real.sqrt ((3 : ℝ) ^ j) := by
  have hk3 : 3 ≤ schauderStepSize d := schauderStepSize_ge_three d
  set k : ℕ := schauderStepSize d with hkdef
  have hkpos : 0 < k := by omega
  have hxm : x ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega : m - 1 ≤ m) hx
  -- the sub-lattice index
  set N : ℕ := (m - j).toNat with hNdef
  have hNcast : ((N : ℤ)) = m - j := Int.toNat_of_nonneg (by omega)
  set i : ℕ := N / k with hidef
  have hdiv : k * (N / k) + N % k = N := Nat.div_add_mod N k
  have hmod : N % k < k := Nat.mod_lt N hkpos
  have hle : (i : ℤ) * (k : ℤ) ≤ (N : ℤ) := by
    have h : k * (N / k) ≤ N := Nat.le.intro hdiv
    have h' : ((k * (N / k) : ℕ) : ℤ) ≤ ((N : ℕ) : ℤ) := Int.ofNat_le.2 h
    push_cast at h' ⊢
    rw [hidef]
    push_cast
    linarith only [h']
  have hlt : (N : ℤ) < (i : ℤ) * (k : ℤ) + (k : ℤ) := by
    have h : N < k * (N / k) + k := by omega
    have h' : ((N : ℕ) : ℤ) < ((k * (N / k) + k : ℕ) : ℤ) := Int.ofNat_lt.2 h
    push_cast at h' ⊢
    rw [hidef]
    push_cast
    linarith only [h']
  set n : ℤ := m - (i : ℤ) * (k : ℤ) with hndef
  have hjn : j ≤ n := by
    rw [hndef]
    linarith only [hle, hNcast]
  have hnj : n - j ≤ (k : ℤ) := by
    rw [hndef]
    linarith only [hlt, hNcast]
  have hnm : n ≤ m := by
    have hjk : (0 : ℤ) ≤ (i : ℤ) * (k : ℤ) := by positivity
    rw [hndef]
    linarith only [hjk]
  -- the sub-lattice bound at scale `n`
  have hsub := affineExcess_le_campanato_sublattice hd hx u hKG hGL2 hG hu i
  rw [← hkdef, ← hndef] at hsub
  -- quasi-monotonicity from `n` down to `j`
  have hun : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) := by
    have h : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [volumeMeasureOn] using u.toH1Function.memL2
    exact memLp_restrict_of_subset (truncatedWindow_subset_domain x m n) h
  have hmono := affineExcess_truncatedWindow_le (l := n) (k := j) x hxm
    (by omega : j - 1 ≤ m) (by omega : n - 1 ≤ m) hjn hun
  -- the two interpolation costs
  have hratio : windowRatioConst d (n - j) ≤ windowRatioConst d (k : ℤ) := by
    have hbase : ((3 : ℝ) ^ (n - j + 2)) ^ d ≤ ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d :=
      pow_le_pow_left₀ (by positivity)
        (zpow_le_zpow_right₀ (by norm_num) (by linarith only [hnj])) d
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hsqrt : Real.sqrt ((3 : ℝ) ^ n)
      ≤ Real.sqrt ((3 : ℝ) ^ (k : ℤ)) * Real.sqrt ((3 : ℝ) ^ j) := by
    have hstep : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ ((k : ℤ) + j) :=
      zpow_le_zpow_right₀ (by norm_num) (by linarith only [hnj])
    calc Real.sqrt ((3 : ℝ) ^ n) ≤ Real.sqrt ((3 : ℝ) ^ ((k : ℤ) + j)) :=
          Real.sqrt_le_sqrt hstep
      _ = Real.sqrt ((3 : ℝ) ^ (k : ℤ)) * Real.sqrt ((3 : ℝ) ^ j) := by
          rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
            Real.sqrt_mul (zpow_pos (by norm_num) _).le]
  -- assemble
  have hCnn : (0 : ℝ) ≤ schauderCampanatoConst d * KG := by
    have h1 : (0 : ℝ) ≤ schauderInitialConst d := schauderInitialConst_nonneg d
    have hgap := schauderStepSize_gap d
    rw [← hkdef] at hgap
    have hgap0 : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
        - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) := by linarith only [hgap]
    have h2 : (0 : ℝ) ≤ lipschitzRemainderConst d k * schauderResidueConst d /
        (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
          - lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ))) :=
      div_nonneg (mul_nonneg (lipschitzRemainderConst_nonneg d k)
        (schauderResidueConst_nonneg d)) hgap0.le
    have h3 : (0 : ℝ) ≤ schauderCampanatoConst d := by
      rw [schauderCampanatoConst, ← hkdef]
      linarith only [h1, h2]
    exact mul_nonneg h3 hKG
  have hstep1 : affineExcess (truncatedWindow x m j) u.toFun
      ≤ windowRatioConst d (k : ℤ) *
        (schauderCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ n)) := by
    refine hmono.trans ?_
    have hrhs : (0 : ℝ) ≤ affineExcess (truncatedWindow x m n) u.toFun :=
      affineExcess_nonneg _ _
    have h1 : windowRatioConst d (n - j) * affineExcess (truncatedWindow x m n) u.toFun
        ≤ windowRatioConst d (k : ℤ) * affineExcess (truncatedWindow x m n) u.toFun :=
      mul_le_mul_of_nonneg_right hratio hrhs
    have h2 : windowRatioConst d (k : ℤ) * affineExcess (truncatedWindow x m n) u.toFun
        ≤ windowRatioConst d (k : ℤ) *
          (schauderCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left hsub (windowRatioConst_nonneg d (k : ℤ))
    linarith only [h1, h2]
  refine hstep1.trans ?_
  have h3 : schauderCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ n)
      ≤ schauderCampanatoConst d * KG *
        (Real.sqrt ((3 : ℝ) ^ (k : ℤ)) * Real.sqrt ((3 : ℝ) ^ j)) :=
    mul_le_mul_of_nonneg_left hsqrt hCnn
  have h4 := mul_le_mul_of_nonneg_left h3 (windowRatioConst_nonneg d (k : ℤ))
  refine h4.trans (le_of_eq ?_)
  rw [schauderCampanatoFullConst, ← hkdef]
  ring

end

end Algsuperdiff.Section4.Provider.Schauder
