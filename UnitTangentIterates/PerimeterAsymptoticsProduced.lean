import Mathlib
import UnitTangentIterates.PerimeterAsymptotics
import UnitTangentIterates.Periodization
import UnitTangentIterates.MatchingEstimates

/-!
# The perimeter defect with the cell approximation produced

`UnitTangentIterates/PerimeterAsymptotics.lean` derives the asymptotics

```
  H - P(H) = Δ + O(e^{-β'H}),      Δ = ∫_ℝ Φ(y),   Φ(z) = 1 - √(1 - z²),
```

of the rear half-perimeter of *A Noncircular Oval with Convex Unit-Tangent
Iterates* from an *assumed* approximation of the periodized profile by the
isolated one,

```
  |Φ(Y_H(s)) - Φ(y(s))| ≤ C₁ e^{-βH}      on the centred cell.
```

This file produces that hypothesis for the periodization
`Y_H(s) = ∑_{m∈ℤ} y(s - mH)` of an exponentially localized nonnegative pulse
`y`, and restates the defect asymptotics with it discharged.  The two
ingredients are

* `MatchingEstimates.abs_sqrt_one_sub_sq_sub_le`, the Lipschitz estimate for
  `z ↦ √(1 - z²)` on `|z| ≤ a < 1`, giving
  `|Φ(Y) - Φ(y)| ≤ (a/√(1-a²))|Y - y|`, and
* `Periodization.periodization_error_le`, the periodization error
  `|Y_H(s) - y(s)| ≤ 4C e^{-(α/2)H}` on the centred cell.

Main results:

* `abs_Phi_sub_le` : `Φ` is Lipschitz with constant `a/√(1-a²)` on `[-a, a]`;
* `abs_Phi_le_sq` : `|Φ(z)| ≤ z²`, whence `Φ(y)` inherits the exponential
  localization of `y`;
* `abs_Phi_periodization_error_le` : the produced cell approximation, with
  `C₁ = (a/√(1-a²))·4C` and `β = α/2`;
* `abs_defect_sub_delta_le_pulse` : `H - P(H) = Δ + O(e^{-β'H})` for every
  `0 < β' < α/2`, no approximation hypothesis being assumed.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace PerimeterAsymptoticsProduced

open PerimeterAsymptotics

/-! ### Elementary properties of the defect integrand -/

/-- **`Φ` is Lipschitz on `[-a, a]`** with constant `a/√(1-a²)`. -/
theorem abs_Phi_sub_le {a z w : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hz : |z| ≤ a) (hw : |w| ≤ a) :
    |Phi z - Phi w| ≤ a / Real.sqrt (1 - a ^ 2) * |z - w| := by
  have h := MatchingEstimates.abs_sqrt_one_sub_sq_sub_le ha0 ha1 hw hz
  have hrw : Phi z - Phi w = Real.sqrt (1 - w ^ 2) - Real.sqrt (1 - z ^ 2) := by
    simp only [Phi]; ring
  rw [hrw, abs_sub_comm z w] at *
  exact h

/-- **`|Φ(z)| ≤ z²`** for `|z| ≤ 1`. -/
theorem abs_Phi_le_sq {z : ℝ} (hz : |z| ≤ 1) : |Phi z| ≤ z ^ 2 := by
  have hz2 : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, abs_le.mp hz]
  have hnn : (0:ℝ) ≤ 1 - z ^ 2 := by linarith
  have hs0 : 0 ≤ Real.sqrt (1 - z ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hnn
  have hs1 : Real.sqrt (1 - z ^ 2) ≤ 1 := by nlinarith
  have h1 : 0 ≤ Phi z := by simp only [Phi]; linarith
  rw [abs_of_nonneg h1]
  simp only [Phi]
  nlinarith

/-- The exponential localization of `Φ(y)` inherited from that of `y`. -/
theorem abs_Phi_comp_le {y : ℝ → ℝ} {C alpha : ℝ} (halpha : 0 < alpha)
    (hy0 : ∀ s, 0 ≤ y s) (hy1 : ∀ s, y s ≤ 1)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) (s : ℝ) :
    |Phi (y s)| ≤ C ^ 2 * Real.exp (-alpha * |s|) := by
  have habs : |y s| ≤ 1 := by rw [abs_of_nonneg (hy0 s)]; exact hy1 s
  have h1 : |Phi (y s)| ≤ (y s) ^ 2 := abs_Phi_le_sq habs
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have h2 : (y s) ^ 2 ≤ (C * Real.exp (-alpha * |s|)) ^ 2 := by
    have := hyb s
    nlinarith [hy0 s]
  have h3 : (C * Real.exp (-alpha * |s|)) ^ 2
      = C ^ 2 * Real.exp (-(2 * alpha) * |s|) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  have h4 : Real.exp (-(2 * alpha) * |s|) ≤ Real.exp (-alpha * |s|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg s]
  calc |Phi (y s)| ≤ (y s) ^ 2 := h1
    _ ≤ (C * Real.exp (-alpha * |s|)) ^ 2 := h2
    _ = C ^ 2 * Real.exp (-(2 * alpha) * |s|) := h3
    _ ≤ C ^ 2 * Real.exp (-alpha * |s|) := by
        have : (0:ℝ) ≤ C ^ 2 := sq_nonneg C
        exact mul_le_mul_of_nonneg_left h4 this

/-! ### The produced cell approximation -/

variable {y : ℝ → ℝ} {C a alpha H : ℝ}

/-- **The cell approximation of the periodized profile by the isolated one.**
For a nonnegative pulse `y` with `y(s) ≤ C e^{-α|s|}` whose periodization stays
below `a < 1`,
`|Φ(Y_H(s)) - Φ(y(s))| ≤ (a/√(1-a²))·4C·e^{-(α/2)H}` on the centred cell. -/
theorem abs_Phi_periodization_error_le (halpha : 0 < alpha) (hH : 0 < H)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ a)
    {s : ℝ} (hs : s ∈ Icc (-(H / 2)) (H / 2)) :
    |Phi (∑' m : ℤ, y (s - m * H)) - Phi (y s)|
      ≤ a / Real.sqrt (1 - a ^ 2) * (4 * C) * Real.exp (-(alpha / 2) * H) := by
  obtain ⟨hs1, hs2⟩ := hs
  have habs : |s| ≤ H / 2 := abs_le.mpr ⟨hs1, hs2⟩
  have hsum : Summable (fun m : ℤ => y (s - m * H)) :=
    Periodization.summable_periodization halpha hy0 hyb hH habs
  have hY0 : 0 ≤ ∑' m : ℤ, y (s - m * H) := tsum_nonneg fun _ => hy0 _
  have hYle : |∑' m : ℤ, y (s - m * H)| ≤ a := by
    rw [abs_of_nonneg hY0]; exact hYa s
  have hy0le : y s ≤ ∑' m : ℤ, y (s - m * H) := by
    have h := hsum.le_tsum (0 : ℤ) (fun i _ => hy0 _)
    simpa using h
  have hyle : |y s| ≤ a := by
    rw [abs_of_nonneg (hy0 s)]
    exact le_trans hy0le (hYa s)
  have hlip := abs_Phi_sub_le ha0 ha1 hYle hyle
  have herr := Periodization.periodization_error_le (z := y) (C := C) (a := alpha) (H := H)
    (s := s) halpha hy0 hyb hH hq habs
  have hcoef : 0 ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  calc |Phi (∑' m : ℤ, y (s - m * H)) - Phi (y s)|
      ≤ a / Real.sqrt (1 - a ^ 2) * |(∑' m : ℤ, y (s - m * H)) - y s| := hlip
    _ ≤ a / Real.sqrt (1 - a ^ 2) * (4 * C * Real.exp (-(alpha / 2) * H)) :=
        mul_le_mul_of_nonneg_left herr hcoef
    _ = a / Real.sqrt (1 - a ^ 2) * (4 * C) * Real.exp (-(alpha / 2) * H) := by ring

/-! ### The defect asymptotics with the approximation produced -/

/-- **`H - P(H) = Δ + O(e^{-β'H})`, with the cell approximation produced.**
For a nonnegative pulse `y` with `y(s) ≤ C e^{-α|s|}` and `y ≤ 1`, whose
periodization `Y_H` stays below `a < 1`, the rear half-perimeter
`P(H) = ∫₀^H √(1 - Y_H²)` satisfies

`|(H - P(H)) - Δ| ≤ (C₁/((α/2 - β')e) + 2C²/α) e^{-β'H}`,
`C₁ = (a/√(1-a²))·4C`,   `Δ = ∫_ℝ Φ(y)`,

for every `β' < α/2`; no approximation of `Y_H` by `y` is assumed. -/
theorem abs_defect_sub_delta_le_pulse {Y : ℝ → ℝ} {beta' : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H) (hb : beta' < alpha / 2)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hy1 : ∀ s, y s ≤ 1)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hY : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (hc : IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H)
    (hper : Function.Periodic (fun s => Phi (Y s)) H)
    (hgi : Integrable (fun s => Phi (y s)))
    (hGi : IntervalIntegrable (fun s => Phi (Y s)) volume (-(H / 2)) (H / 2)) :
    |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))) - ∫ s : ℝ, Phi (y s)|
      ≤ (a / Real.sqrt (1 - a ^ 2) * (4 * C) / ((alpha / 2 - beta') * Real.exp 1)
          + 2 * C ^ 2 / alpha) * Real.exp (-beta' * H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hC1 : 0 ≤ a / Real.sqrt (1 - a ^ 2) * (4 * C) := by positivity
  have happrox : ∀ s ∈ Icc (-(H / 2)) (H / 2),
      |Phi (Y s) - Phi (y s)|
        ≤ a / Real.sqrt (1 - a ^ 2) * (4 * C) * Real.exp (-(alpha / 2) * H) := by
    intro s hs
    rw [hY s]
    exact abs_Phi_periodization_error_le halpha hH hq hy0 hyb ha0 ha1 hYa hs
  exact PerimeterAsymptotics.abs_defect_sub_delta_le_exp
    (C1 := a / Real.sqrt (1 - a ^ 2) * (4 * C)) (beta := alpha / 2) (beta' := beta')
    (C := C ^ 2) halpha hH.le hC1 hb (by linarith) hc hper hgi hGi (sq_nonneg C)
    (abs_Phi_comp_le halpha hy0 hy1 hyb) happrox

end PerimeterAsymptoticsProduced
