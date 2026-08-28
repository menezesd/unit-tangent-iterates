import UnitTangentIterates.ConstantSpeedFrame

/-!
# Unit-speed reparametrization of the path family

The rear-family constructor of `GaugeRearFamilyFromFront` asks for a front
family in **arclength**: `F' = e^{iΘ}` with `Θ' = K`.  What
`IsConstantSpeedNormalPath` supplies (§74) is the normalized parameter:
`X' = P·e^{iθ}` with `θ' = P·κ`.

`unitSpeed_of_frame` performs the change: with `F t s = X t (s/P t)`,

```
  F' = e^{iθ(s/P)} ,     (θ ∘ (·/P))' = κ(s/P) ,     |κ(s/P)| ≤ κ̂ .
```

The speed divides out of both the curve and the angle, and the curvature ceiling
is unchanged — which is the point: the ceiling is a property of the geometry,
not of the parametrization, and it is the quantity everything downstream
(§§55, 69, 71, 74) depends on.

This is the first step of §72's threading.  What follows it is the steering
angle `δ` — determined by the ODE `δ' = K − sin δ` — and the rear arclength.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MarkedSpace PathMetric

namespace NormalPathC2Increment

/-- The reparametrized family, stated directly: given the frame data of a
constant-speed path with positive speed, the arclength family
`F t s = X t (s/P t)` has unit speed and curvature `K t s = κ t (s/P t)`,
bounded by the same ceiling. -/
theorem unitSpeed_of_frame {khat : ℝ} {X : ℝ → ℝ → ℂ}
    {P : ℝ → ℝ} {theta kappa : ℝ → ℝ → ℝ}
    (hPpos : ∀ t, 0 < P t)
    (hX : ∀ t u, HasDerivAt (X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hth : ∀ t u, HasDerivAt (theta t) (P t * kappa t u) u)
    (hk : ∀ t u, |kappa t u| ≤ khat) :
    (∀ t s, HasDerivAt (fun r => X t (r / P t))
      (Complex.exp (Complex.I * ((theta t (s / P t)) : ℂ))) s) ∧
    (∀ t s, HasDerivAt (fun r => theta t (r / P t)) (kappa t (s / P t)) s) ∧
    (∀ t s, |kappa t (s / P t)| ≤ khat) := by
  refine ⟨fun t s => ?_, fun t s => ?_, fun t s => hk t _⟩
  · have hinner : HasDerivAt (fun r : ℝ => r / P t) (1 / P t) s := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (P t)
    have h := (hX t (s / P t)).scomp s hinner
    have hne : (P t : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero).mpr (hPpos t).ne'
    convert h using 1
    simp [smul_eq_mul]
    field_simp
  · have hinner : HasDerivAt (fun r : ℝ => r / P t) (1 / P t) s := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (P t)
    have hne : P t ≠ 0 := (hPpos t).ne'
    have h := (hth t (s / P t)).comp s hinner
    convert h using 1
    field_simp

end NormalPathC2Increment
