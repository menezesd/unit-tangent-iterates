import Mathlib
import UnitTangentIterates.PerimeterLeibnizProduced

/-!
# The value clause of the two-cap asymptotics, from the pulse alone

`UnitTangentIterates/PerimeterAsymptoticsProduced.lean` proves

```
  |(H - P(H)) - Δ| ≤ (C₁/((α/2 - β')e) + 2C²/α) e^{-β'H} ,    Δ = ∫_ℝ Φ(y),
```

with the approximation of the periodized profile by the isolated one produced,
but with the integrability of `Φ(y)`, the interval integrability of the two
integrands and the periodicity of `Φ(Y_H)` still assumed.  All four are
consequences of the exponential localization of the pulse, and this file
derives them, so that the value clause holds with **no hypothesis beyond the
pulse**.

Main results:

* `periodic_Phi_periodization` : `Φ(Y_H)` is `H`-periodic;
* `integrable_Phi_comp` : `Φ(y)` is integrable;
* `abs_defect_sub_delta_le_pulse_full` : the value clause with every
  hypothesis discharged.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterValueProduced

open PerimeterAsymptotics PerimeterAsymptoticsProduced PerimeterLeibnizProduced

variable {y : ℝ → ℝ} {C a alpha H : ℝ}

/-- The defect integrand of the periodized profile is `H`-periodic. -/
theorem periodic_Phi_periodization (H : ℝ) :
    Function.Periodic (fun u => Phi (∑' m : ℤ, y (u - m * H))) H := by
  intro u
  simp only
  have h := FrontPeriodizationIntegral.periodic_tsum_translates y H u
  simp only at h
  rw [h]

/-- The defect integrand of the isolated pulse is integrable. -/
theorem integrable_Phi_comp (halpha : 0 < alpha) (hy : Continuous y)
    (hy0 : ∀ x, 0 ≤ y x) (hy1 : ∀ x, y x ≤ 1)
    (hyb : ∀ x, y x ≤ C * Real.exp (-alpha * |x|)) :
    Integrable (fun s => Phi (y s)) := by
  have hPhi : Continuous Phi := by
    unfold Phi
    fun_prop
  exact FrontPeriodizationIntegral.integrable_of_exp_bound' (C := C ^ 2) halpha (hPhi.comp hy)
    (abs_Phi_comp_le halpha hy0 hy1 hyb)

/-- **The value clause `H - P(H) = Δ + O(e^{-β'H})`, from the pulse alone.**
For a nonnegative pulse `y` with `y ≤ Ce^{-α|·|}` whose periodization
`Y_H` stays below `a < 1`, the rear half-perimeter `P(H) = ∫₀^H √(1 - Y_H²)`
satisfies, for every `β' < α/2`,

`|(H - P(H)) - Δ| ≤ ((a/√(1-a²))·4C/((α/2-β')e) + 2C²/α)e^{-β'H}`,
`Δ = ∫_ℝ Φ(y)`,

no integrability, periodicity or approximation hypothesis being assumed. -/
theorem abs_defect_sub_delta_le_pulse_full {beta' : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H) (hb : beta' < alpha / 2)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy : Continuous y) (hy0 : ∀ x, 0 ≤ y x)
    (hyb : ∀ x, y x ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ a) :
    |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)))
        - ∫ s : ℝ, Phi (y s)|
      ≤ (a / Real.sqrt (1 - a ^ 2) * (4 * C) / ((alpha / 2 - beta') * Real.exp 1)
          + 2 * C ^ 2 / alpha) * Real.exp (-beta' * H) := by
  have hyb' : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|) := fun x => by
    rw [abs_of_nonneg (hy0 x)]; exact hyb x
  -- the pulse is dominated by its periodization, hence below `1`
  have hy1 : ∀ x, y x ≤ 1 := by
    intro x
    have hsum : Summable (fun m : ℤ => y (x - m * H)) :=
      PeriodizationDeriv.summable_periodization_of_le (z := y) (C := C) (a := alpha)
        (H₀ := H) (H := H) (s := x) halpha hyb' hH le_rfl
    have hle : y x ≤ ∑' m : ℤ, y (x - m * H) := by
      have h := hsum.le_tsum (0 : ℤ) (fun i _ => hy0 _)
      simpa using h
    exact le_trans (le_trans hle (hYa x)) ha1.le
  -- continuity of the two integrands
  have hYcont : Continuous (fun u => ∑' m : ℤ, y (u - m * H)) :=
    FrontPeriodizationIntegral.continuous_tsum_translates (C := C) halpha hH hy hyb'
  have hPhi : Continuous Phi := by
    unfold Phi
    fun_prop
  have hc : IntervalIntegrable
      (fun s => Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)) volume 0 H := by
    have : Continuous (fun s => Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)) := by
      fun_prop
    exact this.intervalIntegrable _ _
  have hGi : IntervalIntegrable (fun s => Phi (∑' m : ℤ, y (s - m * H))) volume
      (-(H / 2)) (H / 2) := (hPhi.comp hYcont).intervalIntegrable _ _
  exact abs_defect_sub_delta_le_pulse (y := y) (Y := fun u => ∑' m : ℤ, y (u - m * H))
    (C := C) (a := a) (alpha := alpha) (H := H) (beta' := beta')
    halpha hH hb hq hy0 hy1 hyb ha0 ha1 hYa (fun _ => rfl) hc
    (periodic_Phi_periodization H) (integrable_Phi_comp halpha hy hy0 hy1 hyb) hGi

end PerimeterValueProduced
