import Mathlib
import UnitTangentIterates.TwoCapPairs
import UnitTangentIterates.CellAsymptotics
import UnitTangentIterates.ExpDecay

/-!
# The asymptotics of the rear half-perimeter

The proposition *Exact two-cap pairs* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* ends with the two asymptotic clauses

`P(H) = H - Δ + O(e^{-βH})`,   `P'(H) = 1 + O(e^{-βH})`,

for the rear half-perimeter `P(H) = ∫₀^H c_H`, `c_H = √(1 - Y_H²)`.  The
ingredients are already available: the perimeter defect
`H - P(H) = ∫₀^H Φ(Y_H)` with `Φ(z) = 1 - √(1 - z²)`
(`UnitTangentIterates/TwoCapPairs.lean`), the comparison of a centred cell integral
with the whole-line integral (`UnitTangentIterates/CellAsymptotics.lean`), the
absorption of a polynomial factor into a slightly smaller exponent
(`UnitTangentIterates/ExpDecay.lean`) and the Leibniz rule for the centred cell
integral (`UnitTangentIterates/LeibnizRule.lean`).

This file assembles them.

Main results:

* `perimeter_defect_centred` : the defect over the centred cell,
  `H - P(H) = ∫_{-H/2}^{H/2} Φ(Y_H)`, by periodicity;
* `abs_defect_sub_delta_le` : `|(H - P(H)) - Δ| ≤ εH + (2C/α)e^{-αH/2}`, where
  `Δ = ∫_ℝ Φ(y)` and `ε` bounds `Φ(Y_H) - Φ(y)` on the cell;
* `abs_defect_sub_delta_le_exp` : with `ε = C₁e^{-βH}` and any `β' < β` with
  `2β' ≤ α`, this is `H - P(H) = Δ + O(e^{-β'H})`;
* `hasDerivAt_perimeter` : from the Leibniz rule for the centred cell integral
  and exponentially small endpoint and interior terms,
  `P'(H) = 1 + O(e^{-βH})`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace PerimeterAsymptotics

/-- The defect integrand `Φ(z) = 1 - √(1 - z²)`. -/
def Phi (z : ℝ) : ℝ := 1 - Real.sqrt (1 - z ^ 2)

/-! ### The defect over the centred cell -/

/-- **The perimeter defect over the centred cell.**  If the defect integrand is
`H`-periodic, then `H - P(H) = ∫_{-H/2}^{H/2} Φ(Y_H)`. -/
theorem perimeter_defect_centred {Y : ℝ → ℝ} {H : ℝ}
    (hc : IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H)
    (hper : Function.Periodic (fun s => Phi (Y s)) H) :
    H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))
      = ∫ s in (-(H/2))..(H/2), Phi (Y s) := by
  rw [TwoCapPairs.perimeter_defect hc]
  have h := hper.intervalIntegral_add_eq 0 (-(H/2))
  simp only [Phi] at h ⊢
  rw [zero_add, show -(H/2) + H = H/2 by ring] at h
  exact h

/-! ### The value: `H - P(H) = Δ + O(e^{-βH})` -/

variable {Y y : ℝ → ℝ} {H C alpha eps : ℝ}

/-- **The defect is close to its whole-line limit.**  With
`Δ = ∫_ℝ Φ(y)` the defect of the isolated hairpin, `C, α` the exponential
localization of `Φ(y)`, and `ε` a bound for `Φ(Y_H) - Φ(y)` on the centred
cell,
`|(H - P(H)) - Δ| ≤ εH + (2C/α)e^{-αH/2}`. -/
theorem abs_defect_sub_delta_le (ha : 0 < alpha) (hH : 0 ≤ H)
    (hc : IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H)
    (hper : Function.Periodic (fun s => Phi (Y s)) H)
    (hgi : Integrable (fun s => Phi (y s)))
    (hGi : IntervalIntegrable (fun s => Phi (Y s)) volume (-(H/2)) (H/2))
    (hbd : ∀ s, |Phi (y s)| ≤ C * Real.exp (-alpha * |s|))
    (happrox : ∀ s ∈ Icc (-(H/2)) (H/2), |Phi (Y s) - Phi (y s)| ≤ eps) :
    |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))) - ∫ s : ℝ, Phi (y s)|
      ≤ eps * H + 2 * C * Real.exp (-alpha * (H/2)) / alpha := by
  rw [perimeter_defect_centred hc hper]
  exact CellAsymptotics.abs_cell_sub_line_le ha hH hgi hGi hbd happrox

/-- **`H - P(H) = Δ + O(e^{-β'H})`.**  If the cell error is `εₕ = C₁e^{-βH}`,
then for any `0 < β' < β` with `2β' ≤ α` the defect differs from its
whole-line limit `Δ` by at most a constant multiple of `e^{-β'H}`. -/
theorem abs_defect_sub_delta_le_exp {C1 beta beta' : ℝ} (ha : 0 < alpha) (hH : 0 ≤ H)
    (hC1 : 0 ≤ C1) (hbeta : beta' < beta) (halpha : 2 * beta' ≤ alpha)
    (hc : IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H)
    (hper : Function.Periodic (fun s => Phi (Y s)) H)
    (hgi : Integrable (fun s => Phi (y s)))
    (hGi : IntervalIntegrable (fun s => Phi (Y s)) volume (-(H/2)) (H/2))
    (hC : 0 ≤ C)
    (hbd : ∀ s, |Phi (y s)| ≤ C * Real.exp (-alpha * |s|))
    (happrox : ∀ s ∈ Icc (-(H/2)) (H/2),
      |Phi (Y s) - Phi (y s)| ≤ C1 * Real.exp (-beta * H)) :
    |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))) - ∫ s : ℝ, Phi (y s)|
      ≤ (C1 / ((beta - beta') * Real.exp 1) + 2 * C / alpha) * Real.exp (-beta' * H) := by
  have hmain := abs_defect_sub_delta_le ha hH hc hper hgi hGi hbd happrox
  -- the polynomial factor is absorbed into a slightly smaller exponent
  have h1 : C1 * Real.exp (-beta * H) * H
      ≤ C1 / ((beta - beta') * Real.exp 1) * Real.exp (-beta' * H) := by
    have h := ExpDecay.linear_exp_decay (b := beta) (b' := beta') (x := H) hbeta
    have : H * Real.exp (-(beta * H)) ≤
        1 / ((beta - beta') * Real.exp 1) * Real.exp (-(beta' * H)) := h
    have hrw1 : Real.exp (-beta * H) = Real.exp (-(beta * H)) := by ring_nf
    have hrw2 : Real.exp (-beta' * H) = Real.exp (-(beta' * H)) := by ring_nf
    rw [hrw1, hrw2]
    calc C1 * Real.exp (-(beta * H)) * H = C1 * (H * Real.exp (-(beta * H))) := by ring
      _ ≤ C1 * (1 / ((beta - beta') * Real.exp 1) * Real.exp (-(beta' * H))) :=
          mul_le_mul_of_nonneg_left this hC1
      _ = C1 / ((beta - beta') * Real.exp 1) * Real.exp (-(beta' * H)) := by ring
  -- the tail term has an exponent at least `β'`
  have h2 : 2 * C * Real.exp (-alpha * (H/2)) / alpha
      ≤ 2 * C / alpha * Real.exp (-beta' * H) := by
    have hexp : Real.exp (-alpha * (H/2)) ≤ Real.exp (-beta' * H) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hCa : 0 ≤ 2 * C / alpha := by positivity
    calc 2 * C * Real.exp (-alpha * (H/2)) / alpha
        = 2 * C / alpha * Real.exp (-alpha * (H/2)) := by ring
      _ ≤ 2 * C / alpha * Real.exp (-beta' * H) := mul_le_mul_of_nonneg_left hexp hCa
  calc |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))) - ∫ s : ℝ, Phi (y s)|
      ≤ C1 * Real.exp (-beta * H) * H + 2 * C * Real.exp (-alpha * (H/2)) / alpha := hmain
    _ ≤ C1 / ((beta - beta') * Real.exp 1) * Real.exp (-beta' * H)
          + 2 * C / alpha * Real.exp (-beta' * H) := by linarith
    _ = (C1 / ((beta - beta') * Real.exp 1) + 2 * C / alpha) * Real.exp (-beta' * H) := by ring

/-! ### The derivative: `P'(H) = 1 + O(e^{-βH})` -/

/-- **`P'(H) = 1 + O(e^{-βH})`.**  Suppose the perimeter defect is the centred
cell integral of `g`, that the Leibniz rule of `UnitTangentIterates/LeibnizRule.lean`
computes the derivative of that integral at `H₀`, and that both endpoint terms
and the interior term are small.  Then `P` is differentiable at `H₀` with
`|P'(H₀) - 1| ≤ C_e + C_i`. -/
theorem hasDerivAt_perimeter {P : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ} {H0 Ce Ci : ℝ}
    (hid : ∀ H, H - P H = ∫ s in (-(H/2))..(H/2), g H s)
    (hderiv : HasDerivAt (fun H => ∫ s in (-(H/2))..(H/2), g H s)
      (g H0 (H0/2) / 2 + g H0 (-(H0/2)) / 2 + ∫ s in (-(H0/2))..(H0/2), gH s) H0)
    (hend1 : |g H0 (H0/2)| ≤ Ce) (hend2 : |g H0 (-(H0/2))| ≤ Ce)
    (hint : |∫ s in (-(H0/2))..(H0/2), gH s| ≤ Ci) :
    ∃ p : ℝ, HasDerivAt P p H0 ∧ |p - 1| ≤ Ce + Ci := by
  set D : ℝ := g H0 (H0/2) / 2 + g H0 (-(H0/2)) / 2 + ∫ s in (-(H0/2))..(H0/2), gH s with hD
  have hPeq : P = fun H => H - ∫ s in (-(H/2))..(H/2), g H s := by
    funext H
    have := hid H
    linarith
  refine ⟨1 - D, ?_, ?_⟩
  · rw [hPeq]
    exact (hasDerivAt_id H0).sub hderiv
  · have h1 : |g H0 (H0/2) / 2 + g H0 (-(H0/2)) / 2| ≤ Ce := by
      have := abs_add_le (g H0 (H0/2) / 2) (g H0 (-(H0/2)) / 2)
      rw [abs_div, abs_div] at this
      simp only [abs_two] at this
      linarith
    have h2 : |D| ≤ Ce + Ci := by
      rw [hD]
      exact le_trans (abs_add_le _ _) (by linarith)
    calc |(1 - D) - 1| = |D| := by rw [show (1 - D) - 1 = -D by ring, abs_neg]
      _ ≤ Ce + Ci := h2

/-- The exponential form of the derivative clause: if the endpoint and interior
terms are `O(e^{-βH})`, then `|P'(H) - 1| ≤ (C_e + C_i)e^{-βH}`. -/
theorem hasDerivAt_perimeter_exp {P : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ}
    {H0 Ce Ci beta : ℝ}
    (hid : ∀ H, H - P H = ∫ s in (-(H/2))..(H/2), g H s)
    (hderiv : HasDerivAt (fun H => ∫ s in (-(H/2))..(H/2), g H s)
      (g H0 (H0/2) / 2 + g H0 (-(H0/2)) / 2 + ∫ s in (-(H0/2))..(H0/2), gH s) H0)
    (hend1 : |g H0 (H0/2)| ≤ Ce * Real.exp (-beta * H0))
    (hend2 : |g H0 (-(H0/2))| ≤ Ce * Real.exp (-beta * H0))
    (hint : |∫ s in (-(H0/2))..(H0/2), gH s| ≤ Ci * Real.exp (-beta * H0)) :
    ∃ p : ℝ, HasDerivAt P p H0 ∧ |p - 1| ≤ (Ce + Ci) * Real.exp (-beta * H0) := by
  obtain ⟨p, hp, hbound⟩ := hasDerivAt_perimeter hid hderiv hend1 hend2 hint
  exact ⟨p, hp, by linarith [hbound]⟩

end PerimeterAsymptotics
