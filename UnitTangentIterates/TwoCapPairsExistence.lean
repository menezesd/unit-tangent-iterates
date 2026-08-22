import Mathlib
import UnitTangentIterates.TwoCapPairsAssembly
import UnitTangentIterates.SteeringExistence

/-!
# Exact two-cap pairs: the rear exists

`TwoCapPairsAssembly.lean` assembles the proposition *Exact two-cap pairs* of
*A Noncircular Oval with Convex Unit-Tangent Iterates* from a periodic steering
solution `δ` supplied as a hypothesis.  With the existence theorem of
`SteeringExistence.lean` that hypothesis can now be discharged: for an
`H`-periodic front curvature with `0 ≤ K ≤ κ̂ < 1` and total turning `π` over a
period, the steering solution exists, and the whole two-cap pair with it.

`exact_two_cap_pair` states the resulting package: the front is unit speed,
centrally symmetric, closes after two periods and has perimeter `2H`; the rear
`R = F − e^{iΨ}` has velocity `cos δ · e^{iΨ}` with `cos δ ≥ √(1 − κ̂²) > 0`,
satisfies `𝒯R = F`, is centrally symmetric, closes after two periods, and has
perimeter `2∫₀^H cos δ = 2P(H)`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace TwoCapPairsExistence

open TwoCapPairsAssembly RearTrack

/-- **Exact two-cap pairs.**  For a continuous `H`-periodic front curvature
with `0 ≤ K ≤ κ̂ < 1` and total turning `π` over a period, there is a periodic
steering angle in the closed strip, and the front/rear pair it defines has all
the properties of the paper's proposition. -/
theorem exact_two_cap_pair {kappa : ℝ → ℝ} {H kap theta0 : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Function.Periodic kappa H)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkk : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π) :
    ∃ delta : ℝ → ℝ,
      -- the steering angle
      Function.Periodic delta H ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt delta (kappa s - Real.sin (delta s)) s) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      -- the front
      (∀ s, ‖deriv (front kappa theta0 H) s‖ = 1) ∧
      (∀ s, front kappa theta0 H (s + H) = -front kappa theta0 H s) ∧
      Function.Periodic (front kappa theta0 H) (2 * H) ∧
      (∫ s in (0:ℝ)..(2 * H), ‖deriv (front kappa theta0 H) s‖) = 2 * H ∧
      -- the rear
      (∀ s, HasDerivAt (rear kappa delta theta0 H)
        ((Real.cos (delta s) : ℂ)
          * Complex.exp (Complex.I
              * (rearAngle (frontAngle kappa theta0) delta s : ℂ))) s) ∧
      (∀ s, rear kappa delta theta0 H s
          + (deriv (rear kappa delta theta0 H) s) / ‖deriv (rear kappa delta theta0 H) s‖
        = front kappa theta0 H s) ∧
      (∀ s, rear kappa delta theta0 H (s + H) = -rear kappa delta theta0 H s) ∧
      Function.Periodic (rear kappa delta theta0 H) (2 * H) ∧
      (∫ s in (0:ℝ)..(2 * H), ‖deriv (rear kappa delta theta0 H) s‖)
        = 2 * ∫ s in (0:ℝ)..H, Real.cos (delta s) := by
  obtain ⟨delta, hdper, hrange, hcos, hode⟩ :=
    SteeringExistence.exists_periodic_steering hH hk hper hkap0 hkap1.le hk0 hkk
  have hspos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcospos : ∀ s, 0 < Real.cos (delta s) := fun s => lt_of_lt_of_le hspos (hcos s)
  have hdcont : Continuous delta := Differentiable.continuous fun s => (hode s).differentiableAt
  exact ⟨delta, hdper, hrange, hode, hcos,
    fun s => front_unit_speed (theta0 := theta0) (H := H) hk s,
    fun s => front_add_halfPeriod (theta0 := theta0) hk hper htotal s,
    front_periodic (theta0 := theta0) hk hper htotal,
    front_perimeter (theta0 := theta0) (H := H) hk,
    fun s => rear_hasDerivAt (theta0 := theta0) (H := H) hk (hode s),
    fun s => unitTangentMap_rear_eq_front (theta0 := theta0) (H := H) hk (hode s) (hcospos s),
    fun s => rear_add_halfPeriod (theta0 := theta0) hk hper htotal hdper s,
    rear_periodic (theta0 := theta0) hk hper htotal hdper,
    rear_perimeter (theta0 := theta0) hk hdcont hdper hode (fun s => (hcospos s).le)⟩

end TwoCapPairsExistence
