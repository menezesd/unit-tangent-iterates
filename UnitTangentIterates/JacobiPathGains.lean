import Mathlib
import UnitTangentIterates.JacobiEstimates
import UnitTangentIterates.MarkedTopology

/-!
# The inverse Jacobi estimates for the path functionals

The lemma *Inverse Jacobi estimates* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* is stated for the functionals of a whole path,

```
  W(𝔅Γ) ≤ W(Γ),
  S₀(𝔅Γ) ≤ C₀ W(Γ),
  S₁(𝔅Γ) ≤ C₁ (W(Γ) + S₀(Γ)),
  S₂(𝔅Γ) ≤ C₂ (W(Γ) + S₀(Γ) + S₁(Γ)),
```

with `W(Γ) = ∫₀¹‖η_t‖_{L¹} dt` and `S_j(Γ) = ∫₀¹‖∂ₛ^j η_t‖_{L^∞} dt`
(`MarkedTopology.W`, `MarkedTopology.S`).

`UnitTangentIterates.JacobiEstimates` proves the corresponding statements for a
*single slice* — the `L¹` contraction of the periodic inverse `ℛ_ℓ` of `1 + ∂ₓ`,
its `L¹ → L^∞` gain, and the first- and second-order gains from the
differentiated transport identity.  This file integrates those slice estimates
in `t`, which is all that separates them from the displayed inequalities.

Following the convention of this project, the integrability of the slice
functionals is carried as a hypothesis rather than re-derived; the content is
the inequality.

Main results: `W_nonexpansive_path`, `S0_gain_path`, `S1_gain_path`,
`S2_gain_path` — the four displayed inequalities of the lemma.
-/

noncomputable section

open MeasureTheory MarkedTopology

namespace JacobiPathGains

/-- A uniform slice bound bounds the sup norm. -/
theorem supNorm_le {f : ℝ → ℝ} {c : ℝ} (h : ∀ u, |f u| ≤ c) : supNorm f ≤ c :=
  ciSup_le h

/-- **`eq:Wnonexp` for the path functional.**  Integrating the slicewise
`L¹` contraction `JacobiEstimates.W_nonexpansive` in `t` gives
`W(𝔅Γ) ≤ W(Γ)`: the selected inverse does not increase `W`. -/
theorem W_nonexpansive_path {etaR etaF : ℝ → ℝ → ℝ} {l P : ℝ}
    (hR : IntervalIntegrable (fun t => ∫ x in (0:ℝ)..l, |etaR t x|) volume 0 1)
    (hF : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..P, |etaF t s|) volume 0 1)
    (hslice : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (∫ x in (0:ℝ)..l, |etaR t x|) ≤ ∫ s in (0:ℝ)..P, |etaF t s|) :
    W etaR l ≤ W etaF P :=
  intervalIntegral.integral_mono_on (by norm_num) hR hF hslice

/-- **`eq:S0gain` for the path functionals.**  Integrating the slicewise
`L¹ → L^∞` gain `JacobiEstimates.S0_gain` in `t` gives `S₀(𝔅Γ) ≤ C₀ W(Γ)`. -/
theorem S0_gain_path {etaR etaF : ℝ → ℝ → ℝ} {P C : ℝ} (hC : 0 ≤ C)
    (hR : IntervalIntegrable (fun t => supNorm (etaR t)) volume 0 1)
    (hF : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..P, |etaF t s|) volume 0 1)
    (hslice : ∀ t x, |etaR t x| ≤ C * ∫ s in (0:ℝ)..P, |etaF t s|) :
    S 0 etaR ≤ C * W etaF P := by
  rw [S_zero, W]
  have hmono : ∀ t ∈ Set.Icc (0:ℝ) 1,
      supNorm (etaR t) ≤ C * ∫ s in (0:ℝ)..P, |etaF t s| :=
    fun t _ => supNorm_le (hslice t)
  refine le_trans (intervalIntegral.integral_mono_on (by norm_num) hR
    (hF.const_mul C) hmono) ?_
  rw [intervalIntegral.integral_const_mul]

/-- **A slice bound for the `j`-th derivative gives a bound on `S_j`.**  This is
the only step separating the slicewise estimates of `JacobiEstimates` from the
path functionals of the paper. -/
theorem S_le_of_slice {eta : ℝ → ℝ → ℝ} {j : ℕ} {b : ℝ → ℝ}
    (hS : IntervalIntegrable (fun t => supNorm (iteratedDeriv j (eta t))) volume 0 1)
    (hb : IntervalIntegrable b volume 0 1)
    (hslice : ∀ t x, |iteratedDeriv j (eta t) x| ≤ b t) :
    S j eta ≤ ∫ t in (0:ℝ)..1, b t :=
  intervalIntegral.integral_mono_on (by norm_num) hS hb
    fun t _ => supNorm_le (hslice t)

/-- **`eq:S1gain` for the path functionals.**  The differentiated transport
identity gives, slicewise, `‖η_{R,x}‖_∞ ≤ c₀⁻¹‖η_F‖_∞ + C‖η_F‖_{L¹}`
(`JacobiEstimates.S1_gain` combined with the `S₀` gain for the `η_R` term);
integrating in `t` gives `S₁(𝔅Γ) ≤ c₀⁻¹ S₀(Γ) + C W(Γ)`, which is the paper's
`S₁(𝔅Γ) ≤ C₁(W(Γ) + S₀(Γ))`. -/
theorem S1_gain_path {etaR etaF : ℝ → ℝ → ℝ} {P C c0 : ℝ}
    (hRx : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (etaR t))) volume 0 1)
    (hFsup : IntervalIntegrable (fun t => supNorm (etaF t)) volume 0 1)
    (hFint : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..P, |etaF t s|) volume 0 1)
    (hslice : ∀ t x, |iteratedDeriv 1 (etaR t) x| ≤ c0⁻¹ * supNorm (etaF t)
      + C * ∫ s in (0:ℝ)..P, |etaF t s|) :
    S 1 etaR ≤ c0⁻¹ * S 0 etaF + C * W etaF P := by
  have hb : IntervalIntegrable
      (fun t => c0⁻¹ * supNorm (etaF t) + C * ∫ s in (0:ℝ)..P, |etaF t s|)
      volume 0 1 := (hFsup.const_mul _).add (hFint.const_mul _)
  refine le_trans (S_le_of_slice hRx hb hslice) ?_
  rw [intervalIntegral.integral_add (hFsup.const_mul _) (hFint.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    S_zero, W]

/-- **`eq:S2gain` for the path functionals.**  Same integration applied to the
second-order slice bound of `JacobiEstimates.S2_gain`. -/
theorem S2_gain_path {etaR etaF : ℝ → ℝ → ℝ} {P C c0 c1 : ℝ}
    (hRxx : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (etaR t))) volume 0 1)
    (hF0 : IntervalIntegrable (fun t => supNorm (etaF t)) volume 0 1)
    (hF1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (etaF t))) volume 0 1)
    (hFint : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..P, |etaF t s|) volume 0 1)
    (hslice : ∀ t x, |iteratedDeriv 2 (etaR t) x| ≤
      c0 * supNorm (etaF t) + c1 * supNorm (iteratedDeriv 1 (etaF t))
        + C * ∫ s in (0:ℝ)..P, |etaF t s|) :
    S 2 etaR ≤ c0 * S 0 etaF + c1 * S 1 etaF + C * W etaF P := by
  have hb : IntervalIntegrable
      (fun t => c0 * supNorm (etaF t) + c1 * supNorm (iteratedDeriv 1 (etaF t))
        + C * ∫ s in (0:ℝ)..P, |etaF t s|) volume 0 1 :=
    ((hF0.const_mul _).add (hF1.const_mul _)).add (hFint.const_mul _)
  refine le_trans (S_le_of_slice hRxx hb hslice) ?_
  rw [intervalIntegral.integral_add ((hF0.const_mul _).add (hF1.const_mul _))
      (hFint.const_mul _),
    intervalIntegral.integral_add (hF0.const_mul _) (hF1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, S_zero, W, S]

end JacobiPathGains
