import Mathlib
import UnitTangentIterates.PerimeterAsymptoticsProduced

/-!
# The derivative clause of the two-cap asymptotics, with its endpoint terms produced

The second asymptotic clause of the proposition *Exact two-cap pairs* of
*A Noncircular Oval with Convex Unit-Tangent Iterates* is

```
  P'(H) = 1 + O(e^{-βH}).
```

`PerimeterAsymptotics.hasDerivAt_perimeter_exp` derives it from the Leibniz
rule for the centred cell integral together with the smallness of the two
endpoint terms `Φ(Y_H(±H/2))` and of the interior term `∫ ∂_H Φ(Y_H)`.  This
file produces the two **endpoint** terms for the periodization
`Y_H(s) = ∑_{m∈ℤ} y(s - mH)` of an exponentially localized nonnegative pulse:
at the edge of the cell every translate is at distance at least `H/2` from its
centre, so `Y_H(±H/2) ≤ 5Ce^{-(α/2)H}` and hence
`|Φ(Y_H(±H/2))| ≤ 25C²e^{-αH}` (the last step also using that the periodized
profile stays below `1`).

Main results:

* `periodization_edge_le` : `Y_H(s) ≤ 5Ce^{-(α/2)H}` for `|s| = H/2`;
* `abs_Phi_edge_le` : `|Φ(Y_H(s))| ≤ 25C²e^{-αH}` there;
* `hasDerivAt_perimeter_of_pulse` : `|P'(H) - 1| ≤ (25C² + C_i)e^{-αH}`, only
  the interior term of the Leibniz rule remaining as a hypothesis.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterDerivativeProduced

open PerimeterAsymptotics PerimeterAsymptoticsProduced

variable {y : ℝ → ℝ} {C alpha H : ℝ}

/-- **The periodized profile at the edge of the cell.**  Every translate is at
distance at least `H/2` from the centre of its pulse, so
`Y_H(s) ≤ 5Ce^{-(α/2)H}` when `|s| = H/2`. -/
theorem periodization_edge_le (halpha : 0 < alpha) (hH : 0 < H)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    {s : ℝ} (hs : |s| = H / 2) :
    (∑' m : ℤ, y (s - m * H)) ≤ 5 * C * Real.exp (-(alpha / 2) * H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have habs : |s| ≤ H / 2 := le_of_eq hs
  have herr := Periodization.periodization_error_le (z := y) (C := C) (a := alpha) (H := H)
    (s := s) halpha hy0 hyb hH hq habs
  have h1 : (∑' m : ℤ, y (s - m * H)) - y s ≤ 4 * C * Real.exp (-(alpha / 2) * H) :=
    le_trans (le_abs_self _) herr
  have h2 : y s ≤ C * Real.exp (-(alpha / 2) * H) := by
    have := hyb s
    rw [hs] at this
    calc y s ≤ C * Real.exp (-alpha * (H / 2)) := this
      _ = C * Real.exp (-(alpha / 2) * H) := by ring_nf
  linarith

/-- **The endpoint term of the Leibniz rule is exponentially small.** -/
theorem abs_Phi_edge_le (halpha : 0 < alpha) (hH : 0 < H)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    {s : ℝ} (hs : |s| = H / 2) (hY1 : (∑' m : ℤ, y (s - m * H)) ≤ 1) :
    |Phi (∑' m : ℤ, y (s - m * H))| ≤ 25 * C ^ 2 * Real.exp (-alpha * H) := by
  have hY0 : 0 ≤ ∑' m : ℤ, y (s - m * H) := tsum_nonneg fun _ => hy0 _
  have hedge := periodization_edge_le halpha hH hq hy0 hyb hs
  have hone : |∑' m : ℤ, y (s - m * H)| ≤ 1 := by
    rw [abs_of_nonneg hY0]; exact hY1
  have hsq : |Phi (∑' m : ℤ, y (s - m * H))| ≤ (∑' m : ℤ, y (s - m * H)) ^ 2 :=
    abs_Phi_le_sq hone
  have hbd : (∑' m : ℤ, y (s - m * H)) ^ 2 ≤ (5 * C * Real.exp (-(alpha / 2) * H)) ^ 2 := by
    nlinarith
  have hrw : (5 * C * Real.exp (-(alpha / 2) * H)) ^ 2 = 25 * C ^ 2 * Real.exp (-alpha * H) := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    ring_nf
  linarith [hsq, hbd, hrw.le, hrw.ge]

/-- **`P'(H) = 1 + O(e^{-αH})`, with the endpoint terms produced.**  If the
perimeter defect is the centred cell integral of `Φ(Y_H)`, the Leibniz rule
computes its derivative at `H₀` and the interior term is `O(e^{-αH₀})`, then
`P` is differentiable at `H₀` with `|P'(H₀) - 1| ≤ (25C² + C_i)e^{-αH₀}`. -/
theorem hasDerivAt_perimeter_of_pulse {P : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ}
    {H0 Ci : ℝ} (halpha : 0 < alpha) (hH : 0 < H0)
    (hq : Real.exp (-alpha * H0) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H0)) ≤ 1)
    (hg : ∀ H' s, g H' s = Phi (∑' m : ℤ, y (s - m * H')))
    (hid : ∀ H', H' - P H' = ∫ s in (-(H'/2))..(H'/2), g H' s)
    (hderiv : HasDerivAt (fun H' => ∫ s in (-(H'/2))..(H'/2), g H' s)
      (g H0 (H0/2) / 2 + g H0 (-(H0/2)) / 2 + ∫ s in (-(H0/2))..(H0/2), gH s) H0)
    (hint : |∫ s in (-(H0/2))..(H0/2), gH s| ≤ Ci * Real.exp (-alpha * H0)) :
    ∃ p : ℝ, HasDerivAt P p H0 ∧ |p - 1| ≤ (25 * C ^ 2 + Ci) * Real.exp (-alpha * H0) := by
  have habs1 : |H0 / 2| = H0 / 2 := abs_of_nonneg (by linarith)
  have habs2 : |(-(H0 / 2) : ℝ)| = H0 / 2 := by
    rw [abs_neg]; exact habs1
  have hend1 : |g H0 (H0/2)| ≤ 25 * C ^ 2 * Real.exp (-alpha * H0) := by
    rw [hg]
    exact abs_Phi_edge_le halpha hH hq hy0 hyb habs1 (hYa _)
  have hend2 : |g H0 (-(H0/2))| ≤ 25 * C ^ 2 * Real.exp (-alpha * H0) := by
    rw [hg]
    exact abs_Phi_edge_le halpha hH hq hy0 hyb habs2 (hYa _)
  exact PerimeterAsymptotics.hasDerivAt_perimeter_exp hid hderiv hend1 hend2 hint

end PerimeterDerivativeProduced
