import Mathlib
import UnitTangentIterates.Bicycle

/-!
# From the tangent-angle steering equation back to arclength

The paper writes the steering equation in two parametrizations: in front
arclength `s`,

`δ_s = K − sin δ`,

and — for a strictly convex front, using the front tangent angle `φ = Θ` as
parameter and the radius of curvature `q = 1/K` — in the tangent-angle form

`δ_φ = 1 − q sin δ`.

`UnitTangentIterates/Bicycle.lean` derives the second from the first
(`Bicycle.steering_deriv_angle`).  The existence and smooth-dependence results
of the project (`SteeringExistence.lean`,
`SteeringSmoothDependence.lean`) are proved in the tangent-angle form, whereas
the inverse Jacobi estimates and the path metric
(`SelectedInversePathGeometry.lean`) need the arclength form.  This file
supplies the converse passage:

* `hasDerivAt_steering_of_angle` — if `D` solves `D' = 1 − q sin D` in the
  tangent angle and `Θ_s = K` with `q(Θ) K = 1`, then `δ = D ∘ Θ` solves
  `δ_s = K − sin δ`;
* `periodic_comp_of_turning` — a `2π`-periodic `D` composed with a tangent
  angle that increases by `2π` over one front period gives a `P`-periodic `δ`,
  as the closed-curve hypotheses of the path metric require;
* `mem_strip_comp` — membership of the selected strip is preserved.
-/

noncomputable section

namespace SteeringArclength

/-- **The steering equation in arclength, from its tangent-angle form.**  If
the front tangent angle satisfies `Θ_s = K` with radius of curvature
`q(Θ) = 1/K`, and `D` solves `D' = 1 − q sin D` in the tangent angle, then
`δ = D ∘ Θ` solves the arclength steering equation `δ_s = K − sin δ`. -/
theorem hasDerivAt_steering_of_angle {D Theta K q : ℝ → ℝ} {s : ℝ}
    (hTheta : HasDerivAt Theta (K s) s)
    (hD : HasDerivAt D (1 - q (Theta s) * Real.sin (D (Theta s))) (Theta s))
    (hq : q (Theta s) * K s = 1) :
    HasDerivAt (fun σ => D (Theta σ)) (K s - Real.sin (D (Theta s))) s := by
  have h := hD.comp s hTheta
  refine h.congr_deriv ?_
  have hqK : q (Theta s) * K s * Real.sin (D (Theta s)) = Real.sin (D (Theta s)) := by
    rw [hq, one_mul]
  nlinarith [hqK]

/-- A `2π`-periodic function of the tangent angle becomes a `P`-periodic
function of arclength, for a front whose tangent angle turns by `2π` over one
period. -/
theorem periodic_comp_of_turning {D Theta : ℝ → ℝ} {P : ℝ}
    (hD : Function.Periodic D (2 * Real.pi))
    (hTheta : ∀ s, Theta (s + P) = Theta s + 2 * Real.pi) :
    Function.Periodic (fun σ => D (Theta σ)) P := fun s => by
  simp only [hTheta s, hD (Theta s)]

/-- Membership of the selected strip is preserved by the change of
parametrization. -/
theorem mem_strip_comp {D Theta : ℝ → ℝ} {kap : ℝ}
    (hD : ∀ phi, D phi ∈ Set.Icc (0:ℝ) (Real.arcsin kap)) (s : ℝ) :
    D (Theta s) ∈ Set.Icc (0:ℝ) (Real.arcsin kap) := hD (Theta s)

/-- The passage is inverse to the one of `Bicycle.steering_deriv_angle`:
feeding the arclength equation just obtained back into that lemma returns the
coefficient `1 - q sin D` one started from, with `q = 1/K`. -/
example {D Theta K q : ℝ → ℝ} {s : ℝ}
    (hTheta : HasDerivAt Theta (K s) s) (hK : K s ≠ 0)
    (hD : HasDerivAt D (1 - q (Theta s) * Real.sin (D (Theta s))) (Theta s))
    (hq : q (Theta s) * K s = 1) :
    1 - q (Theta s) * Real.sin (D (Theta s))
      = 1 - (1 / K s) * Real.sin (D (Theta s)) :=
  Bicycle.steering_deriv_angle hTheta hK hD (hasDerivAt_steering_of_angle hTheta hD hq)

end SteeringArclength
