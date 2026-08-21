/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccGradient

/-!
# `t.regularity` Step 7d, part one: `e.cg.Poincare.with.rhs.grad.applied`

## The target

```text
  3^{-m'}‖∇u‖_{B^{-1}_{2,2}(z'+□_{m'-1})} 1_{𝒢(m',z;·,·)}
    ≤ C σ̄_{m'}^{-1/2} ν^{1/2}‖∇u‖_{L̲²(z'+□_{m'-1})}
        + C σ̄_{m'}^{-1} 3^{sm'}[𝐠]_{H̲^s(z'+□_{m'-1})}
    ≤ C 3^{(1/2)(d+γ)(m-m')} ( σ̄_m^{-1/2} ν^{1/2}‖∇u‖_{L̲²(□_m)}
        + σ̄_m^{-1} 3^{sm}[𝐠]_{H̲^s(□_m)} ) .
```

Two independent inequalities, proved here as two independent theorems on the S
the display names (/ discipline), plus the `C₁`-largeness accounting that
absorbs the transport exponent.

## The scalar carriers

* `besov` — `3^{-m'}‖∇u‖_{B^{-1}_{2,2}(z'+□_{m'-1})}·1_{𝒢}`, the left-hand
  side.
* `lamInv` — `λ_{1/4,2}^{-1}(z+□_{m'};𝐚_{L,m'})·1_{𝒢}`, the coarse-graining
  lemma's ellipticity weight at the lattice centre.
* `shomMpInv` / `shomMinv` — `σ̄_{m'}^{-1}` and `σ̄_m^{-1}`.
* `gradLoc` / `gradM` — `ν^{1/2}‖∇u‖_{L̲²}` on `z'+□_{m'-1}` and on `□_m`: for
  `𝐚_L = ν I + 𝐤` with `𝐤` antisymmetric this is the symmetric coefficient
  energy.
* `dataLoc` / `dataM` — `3^{sm'}[𝐠]_{H̲^s(z'+□_{m'-1})}` and
  `3^{sm}[𝐠]_{H̲^s(□_m)}`.
* `Kg`, `Kd`, `Ks` — the three transport factors of the second inequality: the
  `L̲²` volume ratio, the `H̲^s` window restriction, and the `σ̄` comparison.

## The conditional inputs, and nothing else

* **`hcg`** — `l.coarse.graining.RHS` applied on `z'+□_{m'-1}` at the good scale
  `m'`, in the ellipticity-weighted form the display quotes:
  `besov ≤ C(√lamInv·gradLoc) + C(lamInv·dataLoc)`.
* **`hlambda`** — `e.lambda.stability.applied`, the lower leg at `k' = m'`:
  `λ_{1/4,2}^{-1}(z+□_{m'};𝐚_{L,m'})1_{𝒢} ≤ C σ̄_{m'}^{-1}`.  This is the first
  conjunct of the printed display, in exactly the rendering discipline the
  Step-7c `hlambda` uses for the second conjunct (lattice centre, indicator absorbed,
  one scalar inequality `weight ≤ C · σ̄-power`), so that a single future
  Step-7b theorem discharges both.

The three transport ingredients `hgrad`, `hdata`, `hshom` are *not* conditional
inputs of this module: they are the caller's own geometry/`σ̄` facts, and each
is supplied unconditionally elsewhere in the development
(`normalizedL2On_le_of_subset` for `Kg`, the window restriction for `Kd`, and
`sigmaBar_le_rpow_mul_sigmaBar_of_inductionState` for `Ks`).

## The `C₁`-largeness accounting (the transport exponent)

The transport exponent `(1/2)(d+γ)(m-m')` is absorbed into
`3^{(1/4)(1-α)(m-n)}` by the third and fourth `C₁`-largeness conditions.  The
`C₁` floor already carries the exact clause: `stepOneC1`'s second maximand is
`2d+2`, and `two_mul_dim_add_gamma_le_stepOneC1` reads it as `2(d+γ) ≤ C₁` for
`γ ≤ 1` — the pin whose docstring names *this* transport.  So

```text
  (1/2)(d+γ)(m-m') ≤ (1/2)(d+γ)·3 + 1/4 + (1/4)(1-α)(m-n)
```

with NO new largeness demand: `half_dim_add_gamma_mul_inv_le_quarter` needs
exactly `2d+2 ≤ C₁` and `γ ≤ 1`.  Nothing was enlarged.

## References

* ABK26, `e.cg.Poincare.with.rhs.grad.applied`.
* ABK26, graining.; `e.lambda.stability.applied`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 1. The transport exponent and the `C₁` absorption -/

/-- `(1/2)(d+γ)·C₁⁻¹ ≤ 1/4`'s pin (4).  This is the ONLY place the `C₁`-largeness
of the coarse-graining transport is used's floor `C₁ ≥ 2d+2` already covers it
whenever `γ ≤ 1` — the exact reading of `two_mul_dim_add_gamma_le_stepOneC1`. -/
theorem half_dim_add_gamma_mul_inv_le_quarter (d : ℕ) {C1 gamma : ℝ}
    (hgamma1 : gamma ≤ 1) (hC1 : 2 * (d : ℝ) + 2 ≤ C1) :
    1 / 2 * ((d : ℝ) + gamma) * C1⁻¹ ≤ 1 / 4 := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1, hd]
  rw [mul_inv_le_iff₀ hC1pos]
  linarith only [hC1, hd, hgamma1]

/-- **The transport exponent, bounded by the budget** (first clause).

At the gap `m - m' ≤ |𝓑_z| + G`, the budget `|𝓑_z| ≤ δ((m-n)+1)`, the parameter
choice `δ ≤ C₁⁻¹(1-α)`'s floor `C₁ ≥ 2d+2` with `γ ≤ 1`:

```text
  (1/2)(d+γ)(m - m')  ≤  (1/2)(d+γ)·G  +  1/4  +  (1/4)(1-α)(m-n) .
```

The shape is that of `stepSevenVolumeExponent_le_of_gap` with `d/2` replaced by
`(1/2)(d+γ)` and the lower gap by the upper one. -/
theorem stepSevenTransportExponent_le_of_gap (d : ℕ) {C1 alpha delta gamma : ℝ}
    {B : ℕ} {n m m' : ℤ} {G : ℤ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hgap : m - m' ≤ (B : ℤ) + G)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1)) :
    1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ)) ≤
      1 / 2 * ((d : ℝ) + gamma) * (G : ℝ) + 1 / 4 +
        1 / 4 * stepSixExponent alpha n m := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd2 : (0 : ℝ) ≤ 1 / 2 * ((d : ℝ) + gamma) := by linarith only [hd, hgamma0]
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1, hd]
  have hA0 : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha1]
  have hA1 : (1 : ℝ) - alpha ≤ 1 := by linarith only [halpha0]
  -- the window length, as a real
  have hT : ((m - n).toNat : ℝ) = (m : ℝ) - (n : ℝ) := by
    have h : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have hT0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [this]
  -- the selection gap, as a real
  have hgapR : (m : ℝ) - (m' : ℝ) ≤ (B : ℝ) + (G : ℝ) := by
    have h : ((m - m' : ℤ) : ℝ) ≤ (((B : ℤ) + G : ℤ) : ℝ) := by exact_mod_cast hgap
    push_cast at h
    linarith only [h]
  -- the budget, transported through `δ ≤ C₁⁻¹(1-α)`
  have hTp : (0 : ℝ) ≤ ((m : ℝ) - (n : ℝ)) + 1 := by linarith only [hT0]
  have hb1 : (B : ℝ) ≤ delta * (((m : ℝ) - (n : ℝ)) + 1) := by
    rw [hT] at hbudget; exact hbudget
  have hb2 : delta * (((m : ℝ) - (n : ℝ)) + 1) ≤
      C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1) :=
    mul_le_mul_of_nonneg_right hdelta hTp
  have hb3 : 1 / 2 * ((d : ℝ) + gamma) * (B : ℝ) ≤
      1 / 2 * ((d : ℝ) + gamma) * (C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) :=
    mul_le_mul_of_nonneg_left (le_trans hb1 hb2) hd2
  -- `(1/2)(d+γ)·C₁⁻¹ ≤ 1/4`
  have hq := half_dim_add_gamma_mul_inv_le_quarter d hgamma1 hC1
  have hAT : (0 : ℝ) ≤ (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1) := mul_nonneg hA0 hTp
  have hb4 : 1 / 2 * ((d : ℝ) + gamma) *
      (C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) ≤
      1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) := by
    have h := mul_le_mul_of_nonneg_right hq hAT
    calc 1 / 2 * ((d : ℝ) + gamma) *
          (C1⁻¹ * (1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1))
        = (1 / 2 * ((d : ℝ) + gamma) * C1⁻¹) *
            ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) := by ring
      _ ≤ 1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) := h
  -- the `+1` of the budget costs `(1/4)(1-α) ≤ 1/4`
  have hb5 : 1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) ≤
      1 / 4 + 1 / 4 * ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by
    have h : (1 : ℝ) / 4 * (1 - alpha) ≤ 1 / 4 := by linarith only [hA1]
    have hexp : 1 / 4 * ((1 - alpha) * (((m : ℝ) - (n : ℝ)) + 1)) =
        1 / 4 * ((1 - alpha) * ((m : ℝ) - (n : ℝ))) + 1 / 4 * (1 - alpha) := by ring
    linarith only [h, hexp.ge, hexp.le]
  -- assemble
  have hgapmul : 1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ)) ≤
      1 / 2 * ((d : ℝ) + gamma) * ((B : ℝ) + (G : ℝ)) :=
    mul_le_mul_of_nonneg_left hgapR hd2
  have hexpand : 1 / 2 * ((d : ℝ) + gamma) * ((B : ℝ) + (G : ℝ)) =
      1 / 2 * ((d : ℝ) + gamma) * (B : ℝ) + 1 / 2 * ((d : ℝ) + gamma) * (G : ℝ) := by
    ring
  rw [stepSixExponent]
  linarith only [hgapmul, hexpand.ge, hexpand.le, hb3, hb4, hb5]

/-- **The transport factor itself**'s sharp gap `m - m' ≤ |𝓑_z| + 3`:
`3^{(1/2)(d+γ)(m-m')} ≤ 3^{(3/2)(d+γ) + 1/4} · 3^{(1/4)(1-α)(m-n)}`. -/
theorem three_rpow_stepSevenTransport_le (d : ℕ) {C1 alpha delta gamma : ℝ} {B : ℕ}
    {n m m' : ℤ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hgap : m - m' ≤ (B : ℤ) + 3)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1)) :
    Real.rpow (3 : ℝ) (1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ))) ≤
      Real.rpow (3 : ℝ) (3 / 2 * ((d : ℝ) + gamma) + 1 / 4) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
  have h := stepSevenTransportExponent_le_of_gap d (G := 3) hgamma0 hgamma1 hC1
    halpha0 halpha1 hnm hdelta hgap hbudget
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcast : (((3 : ℤ) : ℝ)) = (3 : ℝ) := by norm_num
  rw [hcast] at h
  have hred : 1 / 2 * ((d : ℝ) + gamma) * (3 : ℝ) = 3 / 2 * ((d : ℝ) + gamma) := by
    ring
  rw [hred] at h
  calc Real.rpow (3 : ℝ) (1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ)))
      ≤ Real.rpow (3 : ℝ) ((3 / 2 * ((d : ℝ) + gamma) + 1 / 4) +
          1 / 4 * stepSixExponent alpha n m) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [h])
    _ = _ := Real.rpow_add h3 _ _

/-- **The transport factor with the `C₁` floor discharged.**  `stepOneC1` meets
`2d+2` unconditionally (`two_mul_dim_le_stepOneC1`, the pin whose docstring names
this transport), and `stepOneDelta` is `C₁⁻¹(1-α)` definitionally, so at the
development's own parameters the transport factor needs only `γ ≤ 1`, the
window regime and the budget. -/
theorem three_rpow_stepSevenTransport_le_stepOneC1 (d : ℕ)
    {Cedos Cann Citer alpha delta gamma : ℝ} {k B : ℕ} {n m m' : ℤ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) (hnm : n ≤ m)
    (hdelta : delta ≤ stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha)
    (hgap : m - m' ≤ (B : ℤ) + 3)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1)) :
    Real.rpow (3 : ℝ) (1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ))) ≤
      Real.rpow (3 : ℝ) (3 / 2 * ((d : ℝ) + gamma) + 1 / 4) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
  three_rpow_stepSevenTransport_le d hgamma0 hgamma1
    (two_mul_dim_le_stepOneC1 d Cedos Cann Citer k) halpha0 halpha1 hnm
    (by rw [stepOneDelta] at hdelta; exact hdelta) hgap hbudget

/-! ## 2. The first inequality: the coarse-graining Poincaré after `hlambda` -/

/-- **`e.cg.Poincare.with.rhs.grad.applied`, first inequality**, on abstract reals.

`l.coarse.graining.RHS` produces the Besov left-hand side against the weight
`λ^{-1}` (square root on the gradient leg, full power on the data leg);
`e.lambda.stability.applied` replaces `λ^{-1}` by `C σ̄_{m'}^{-1}`.  The two
legs are then carried by the single constant `Ccg(√Clam + Clam)`. -/
theorem cgPoincareShom_compose {Ccg Clam lamInv shomInv besov gradLoc dataLoc : ℝ}
    (hCcg : 0 ≤ Ccg) (hClam : 0 ≤ Clam) (hshomInv : 0 ≤ shomInv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hcg : besov ≤ Ccg * (Real.sqrt lamInv * gradLoc) + Ccg * (lamInv * dataLoc))
    (hlambda : lamInv ≤ Clam * shomInv) :
    besov ≤ (Ccg * (Real.sqrt Clam + Clam)) * (Real.sqrt shomInv * gradLoc) +
      (Ccg * (Real.sqrt Clam + Clam)) * (shomInv * dataLoc) := by
  have hL : (0 : ℝ) ≤ Real.sqrt Clam := Real.sqrt_nonneg _
  have hS : (0 : ℝ) ≤ Real.sqrt shomInv := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt lamInv ≤ Real.sqrt Clam * Real.sqrt shomInv := by
    calc Real.sqrt lamInv ≤ Real.sqrt (Clam * shomInv) := Real.sqrt_le_sqrt hlambda
      _ = Real.sqrt Clam * Real.sqrt shomInv := Real.sqrt_mul hClam shomInv
  have h1 : Ccg * (Real.sqrt lamInv * gradLoc) ≤
      Ccg * (Real.sqrt Clam * (Real.sqrt shomInv * gradLoc)) := by
    have hstep : Real.sqrt lamInv * gradLoc ≤
        Real.sqrt Clam * (Real.sqrt shomInv * gradLoc) := by
      have h := mul_le_mul_of_nonneg_right hsqrt hgradLoc
      calc Real.sqrt lamInv * gradLoc
          ≤ Real.sqrt Clam * Real.sqrt shomInv * gradLoc := h
        _ = Real.sqrt Clam * (Real.sqrt shomInv * gradLoc) := by ring
    exact mul_le_mul_of_nonneg_left hstep hCcg
  have h2 : Ccg * (lamInv * dataLoc) ≤ Ccg * (Clam * (shomInv * dataLoc)) := by
    have hstep : lamInv * dataLoc ≤ Clam * (shomInv * dataLoc) := by
      have h := mul_le_mul_of_nonneg_right hlambda hdataLoc
      calc lamInv * dataLoc ≤ Clam * shomInv * dataLoc := h
        _ = Clam * (shomInv * dataLoc) := by ring
    exact mul_le_mul_of_nonneg_left hstep hCcg
  have p1 : 0 ≤ Ccg * Clam * (Real.sqrt shomInv * gradLoc) :=
    mul_nonneg (mul_nonneg hCcg hClam) (mul_nonneg hS hgradLoc)
  have p2 : 0 ≤ Ccg * Real.sqrt Clam * (shomInv * dataLoc) :=
    mul_nonneg (mul_nonneg hCcg hL) (mul_nonneg hshomInv hdataLoc)
  have hkey : Ccg * (Real.sqrt Clam * (Real.sqrt shomInv * gradLoc)) +
      Ccg * (Clam * (shomInv * dataLoc)) +
      (Ccg * Clam * (Real.sqrt shomInv * gradLoc) +
        Ccg * Real.sqrt Clam * (shomInv * dataLoc)) =
      (Ccg * (Real.sqrt Clam + Clam)) * (Real.sqrt shomInv * gradLoc) +
        (Ccg * (Real.sqrt Clam + Clam)) * (shomInv * dataLoc) := by
    ring
  linarith only [hcg, h1, h2, p1, p2, hkey.ge, hkey.le]

/-! ## 3. The second inequality: the transport to `□_m` -/

/-- **`e.cg.Poincare.with.rhs.grad.applied`, second inequality**, on abstract
reals: the three transports

```text
  gradLoc ≤ Kg · gradM ,   dataLoc ≤ Kd · dataM ,   σ̄_{m'}^{-1} ≤ Ks · σ̄_m^{-1}
```

(the `L̲²` volume ratio, the `H̲^s` window restriction, and the `σ̄`
comparison) carry the weighted bracket from `z'+□_{m'-1}` to `□_m` at the two
factors `√Ks·Kg` and `Ks·Kd`. -/
theorem cgPoincareTransport_compose {Kg Kd Ks gradLoc dataLoc gradM dataM
    shomMpInv shomMinv : ℝ}
    (hKs : 0 ≤ Ks) (hshomMinv : 0 ≤ shomMinv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hgrad : gradLoc ≤ Kg * gradM) (hdata : dataLoc ≤ Kd * dataM)
    (hshom : shomMpInv ≤ Ks * shomMinv) :
    Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc ≤
      (Real.sqrt Ks * Kg) * (Real.sqrt shomMinv * gradM) +
        (Ks * Kd) * (shomMinv * dataM) := by
  have hKsS : (0 : ℝ) ≤ Real.sqrt Ks := Real.sqrt_nonneg _
  have hSm : (0 : ℝ) ≤ Real.sqrt shomMinv := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt shomMpInv ≤ Real.sqrt Ks * Real.sqrt shomMinv := by
    calc Real.sqrt shomMpInv ≤ Real.sqrt (Ks * shomMinv) := Real.sqrt_le_sqrt hshom
      _ = Real.sqrt Ks * Real.sqrt shomMinv := Real.sqrt_mul hKs shomMinv
  have h1 : Real.sqrt shomMpInv * gradLoc ≤
      (Real.sqrt Ks * Real.sqrt shomMinv) * (Kg * gradM) :=
    mul_le_mul hsqrt hgrad hgradLoc (mul_nonneg hKsS hSm)
  have h2 : shomMpInv * dataLoc ≤ (Ks * shomMinv) * (Kd * dataM) :=
    mul_le_mul hshom hdata hdataLoc (mul_nonneg hKs hshomMinv)
  have hkey1 : (Real.sqrt Ks * Real.sqrt shomMinv) * (Kg * gradM) =
      (Real.sqrt Ks * Kg) * (Real.sqrt shomMinv * gradM) := by ring
  have hkey2 : (Ks * shomMinv) * (Kd * dataM) = (Ks * Kd) * (shomMinv * dataM) := by
    ring
  linarith only [h1, h2, hkey1.ge, hkey1.le, hkey2.ge, hkey2.le]

/-! ## 4. The display -/

/-- **`e.cg.Poincare.with.rhs.grad.applied`, as printed.**

The two inequalities composed, at a single transport factor `Ktr` dominating
both legs' factors:

```text
  besov ≤ Ccg(√Clam + Clam) · Ktr · ( √σ̄_m^{-1}·gradM + σ̄_m^{-1}·dataM ) .
```

`hcg` and `hlambda` are the only conditional
inputs; `hgrad`, `hdata`, `hshom`, `hKgb`, `hKdb` are the caller's own
transport data. -/
theorem stepSevenCgPoincareApplied {Ccg Clam Kg Kd Ks Ktr lamInv shomMpInv shomMinv
    besov gradLoc dataLoc gradM dataM : ℝ}
    (hCcg : 0 ≤ Ccg) (hClam : 0 ≤ Clam) (hKs : 0 ≤ Ks)
    (hshomMpInv : 0 ≤ shomMpInv) (hshomMinv : 0 ≤ shomMinv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hgradM : 0 ≤ gradM) (hdataM : 0 ≤ dataM)
    (hcg : besov ≤ Ccg * (Real.sqrt lamInv * gradLoc) + Ccg * (lamInv * dataLoc))
    (hlambda : lamInv ≤ Clam * shomMpInv)
    (hgrad : gradLoc ≤ Kg * gradM) (hdata : dataLoc ≤ Kd * dataM)
    (hshom : shomMpInv ≤ Ks * shomMinv)
    (hKgb : Real.sqrt Ks * Kg ≤ Ktr) (hKdb : Ks * Kd ≤ Ktr) :
    besov ≤ (Ccg * (Real.sqrt Clam + Clam)) * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by
  have hCout : (0 : ℝ) ≤ Ccg * (Real.sqrt Clam + Clam) :=
    mul_nonneg hCcg (add_nonneg (Real.sqrt_nonneg _) hClam)
  have hA := cgPoincareShom_compose hCcg hClam hshomMpInv hgradLoc hdataLoc hcg hlambda
  have hB := cgPoincareTransport_compose hKs hshomMinv hgradLoc hdataLoc hgrad hdata hshom
  -- the bracket at `m'` is dominated by `Ktr` times the bracket at `m`
  have hg : (0 : ℝ) ≤ Real.sqrt shomMinv * gradM :=
    mul_nonneg (Real.sqrt_nonneg _) hgradM
  have hdd : (0 : ℝ) ≤ shomMinv * dataM := mul_nonneg hshomMinv hdataM
  have hC1 : (Real.sqrt Ks * Kg) * (Real.sqrt shomMinv * gradM) ≤
      Ktr * (Real.sqrt shomMinv * gradM) := mul_le_mul_of_nonneg_right hKgb hg
  have hC2 : (Ks * Kd) * (shomMinv * dataM) ≤ Ktr * (shomMinv * dataM) :=
    mul_le_mul_of_nonneg_right hKdb hdd
  have hbr : Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc ≤
      Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by
    have hexp : Ktr * (Real.sqrt shomMinv * gradM) + Ktr * (shomMinv * dataM) =
        Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by ring
    linarith only [hB, hC1, hC2, hexp.ge, hexp.le]
  have hfin : (Ccg * (Real.sqrt Clam + Clam)) *
      (Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc) ≤
      (Ccg * (Real.sqrt Clam + Clam)) *
        (Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM)) :=
    mul_le_mul_of_nonneg_left hbr hCout
  have hexp2 : (Ccg * (Real.sqrt Clam + Clam)) *
      (Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc) =
      (Ccg * (Real.sqrt Clam + Clam)) * (Real.sqrt shomMpInv * gradLoc) +
        (Ccg * (Real.sqrt Clam + Clam)) * (shomMpInv * dataLoc) := by ring
  have hexp3 : (Ccg * (Real.sqrt Clam + Clam)) *
      (Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM)) =
      (Ccg * (Real.sqrt Clam + Clam)) * Ktr *
        (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by ring
  linarith only [hA, hfin, hexp2.ge, hexp2.le, hexp3.ge, hexp3.le]

/-- **`e.cg.Poincare.with.rhs.grad.applied`, with the transport exponent
absorbed** (the display's first clause).  At `Ktr = 3^{(1/2)(d+γ)(m-m')}`, the
sharp gap and the Step-3 budget, the
display holds with `3^{(1/4)(1-α)(m-n)}` in place of the transport factor, at
the explicit constant `3^{(3/2)(d+γ)+1/4}`. -/
theorem stepSevenCgPoincareApplied_absorbed (d : ℕ)
    {C1 alpha delta gamma : ℝ} {B : ℕ} {n m m' : ℤ}
    {Ccg Clam Kg Kd Ks lamInv shomMpInv shomMinv besov gradLoc dataLoc gradM dataM : ℝ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hgap : m - m' ≤ (B : ℤ) + 3)
    (hbudget : (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1))
    (hCcg : 0 ≤ Ccg) (hClam : 0 ≤ Clam) (hKs : 0 ≤ Ks)
    (hshomMpInv : 0 ≤ shomMpInv) (hshomMinv : 0 ≤ shomMinv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hgradM : 0 ≤ gradM) (hdataM : 0 ≤ dataM)
    (hcg : besov ≤ Ccg * (Real.sqrt lamInv * gradLoc) + Ccg * (lamInv * dataLoc))
    (hlambda : lamInv ≤ Clam * shomMpInv)
    (hgrad : gradLoc ≤ Kg * gradM) (hdata : dataLoc ≤ Kd * dataM)
    (hshom : shomMpInv ≤ Ks * shomMinv)
    (hKgb : Real.sqrt Ks * Kg ≤
      Real.rpow (3 : ℝ) (1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ))))
    (hKdb : Ks * Kd ≤
      Real.rpow (3 : ℝ) (1 / 2 * ((d : ℝ) + gamma) * ((m : ℝ) - (m' : ℝ)))) :
    besov ≤ (Ccg * (Real.sqrt Clam + Clam)) *
      (Real.rpow (3 : ℝ) (3 / 2 * ((d : ℝ) + gamma) + 1 / 4) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m)) *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by
  have habs := three_rpow_stepSevenTransport_le d hgamma0 hgamma1 hC1 halpha0 halpha1
    hnm hdelta hgap hbudget
  exact stepSevenCgPoincareApplied hCcg hClam hKs hshomMpInv hshomMinv hgradLoc
    hdataLoc hgradM hdataM hcg hlambda hgrad hdata hshom (le_trans hKgb habs)
    (le_trans hKdb habs)

end

end Algsuperdiff.Section4.Provider.Regularity
