import Mathlib
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.SteeringExistence
import UnitTangentIterates.SelectedInversePathGeometry

/-!
# The selected steering data of a path of fronts

`UnitTangentIterates/SelectedInversePathGeometry.lean` produces the normal path of
selected rears from data attached to each front of a path: a steering angle
`δ`, periodic with the front period, taking values in the selected strip
`0 ≤ δ ≤ arcsin κ̂` and solving `δ_s = K − sin δ`, together with an inverse `sf`
of the rear arclength `x(s) = ∫₀ˢ cos δ`.  This file shows that **such data
always exists and the steering angle is unique**, for every path of fronts
whose curvatures satisfy the tube bounds `0 ≤ K ≤ κ̂ < 1`:

* `exists_selected_steering_family` — the steering angles and the changes of
  variable of a whole path of fronts, with uniqueness of the steering angle at
  each time;
* `exists_steering_and_normalPath` — the combined statement: for a normal path
  of fronts with curvatures in the tube and periods in `[P₀, P₁]`, there is a
  selected steering family, and for *any* rear family moving over it with a
  normal velocity solving the inverse Jacobi ODE the rears form a normal path
  of cost the uniform constant times the cost of the front path.

Together with `SelectedInversePathGeometry.exists_normalPath_of_geometry` this
says that the geometric hypotheses of the Jacobi bridge concerning the *front*
are never restrictive: only the hypotheses describing the motion of the rear
family (the paper's lemma *Smooth dependence of the selected rear*) remain.
-/

noncomputable section

open Set RearTrack ArclengthInverse

namespace SelectedSteeringFamily

/-- **The selected steering data of a path of fronts.**  For a family of front
curvatures `K t`, continuous, periodic with period `P t` and pinched by
`0 ≤ K ≤ κ̂ < 1`, there are a steering angle `δ t` and a change of variable
`sf t` such that, at every time, `δ t` is periodic with the front period, takes
values in the selected strip, solves the steering equation, is the *only*
periodic solution in the closed strip `|δ| ≤ π/2`, and `sf t` inverts the rear
arclength.  These are exactly the hypotheses `hdper`, `hstrip0`, `hstrip1`,
`hsteer`, `hsfinv` of
`SelectedInversePathGeometry.exists_normalPath_of_geometry`. -/
theorem exists_selected_steering_family {kh : ℝ} {P : ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hP : ∀ t, 0 < P t)
    (hKc : ∀ t, Continuous (K t)) (hKper : ∀ t, Function.Periodic (K t) (P t))
    (hK0 : ∀ t s, 0 ≤ K t s) (hKk : ∀ t s, K t s ≤ kh) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (delta t) (P t)) ∧
      (∀ t s, 0 ≤ delta t s) ∧ (∀ t s, delta t s ≤ Real.arcsin kh) ∧
      (∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s) ∧
      (∀ t x, rearArclength (delta t) (sf t x) = x) ∧
      (∀ t e, Function.Periodic e (P t) → (∀ s, e s ∈ Icc 0 (Real.arcsin kh)) →
        (∀ s, HasDerivAt e (K t s - Real.sin (e s)) s) → e = delta t) := by
  -- the steering angle at each time
  have hex : ∀ t, ∃ d : ℝ → ℝ, Function.Periodic d (P t) ∧
      (∀ s, d s ∈ Icc 0 (Real.arcsin kh)) ∧
      (∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (d s)) ∧
      (∀ s, HasDerivAt d (K t s - Real.sin (d s)) s) := fun t =>
    SteeringExistence.exists_periodic_steering (hP t) (hKc t) (hKper t) hkh0 hkh1.le
      (hK0 t) (hKk t)
  choose delta hper hrange _hcos hode using hex
  -- the change of variable at each time
  have hdc : ∀ t, Continuous (delta t) := fun t =>
    Differentiable.continuous fun s => (hode t s).differentiableAt
  have hinv : ∀ t, ∃ g : ℝ → ℝ, ∀ x, rearArclength (delta t) (g x) = x := fun t =>
    exists_inverse_rearArclength hkh0 hkh1 (hdc t) (fun s => (hrange t s).1)
      (fun s => (hrange t s).2)
  choose sf hsf using hinv
  -- the closed strip `|δ| ≤ π/2` containing the selected strip
  have hstrip : ∀ (e : ℝ → ℝ), (∀ s, e s ∈ Icc 0 (Real.arcsin kh)) →
      ∀ s, e s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro e he s
    exact ⟨by linarith [(he s).1, Real.pi_pos],
      le_trans (he s).2 (Real.arcsin_le_pi_div_two kh)⟩
  refine ⟨delta, sf, hper, fun t s => (hrange t s).1, fun t s => (hrange t s).2, hode,
    hsf, ?_⟩
  intro t e hpere hrangee hodee
  exact Shadowing.steering_unique (hP t) hodee (hode t) hpere (hper t)
    (hstrip e hrangee) (hstrip (delta t) (hrange t))

/-- **The selected steering family and the normal path of rears, combined.**
For a normal path of fronts whose curvatures satisfy the tube bounds
`0 ≤ K ≤ κ̂ < 1` and whose periods lie in `[P₀, P₁]`, there is a selected
steering family `δ` with its change of variable `sf`; and whenever a rear
family moves over it with a normal velocity solving the inverse Jacobi ODE, the
rears form a normal path whose cost is the uniform constant of
`SelectedInversePathGeometry` times the cost of the front path. -/
theorem exists_steering_and_normalPath {p q p' q' : MarkedSpace.Data}
    (Γ : PathMetric.NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {K etaF etaFs : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hKc : ∀ t, Continuous (K t)) (hKper : ∀ t, Function.Periodic (K t) (P t))
    (hK0 : ∀ t s, 0 ≤ K t s) (hKk : ∀ t s, K t s ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u)) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (delta t) (P t)) ∧
      (∀ t s, delta t s ∈ Icc 0 (Real.arcsin kh)) ∧
      (∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s) ∧
      (∀ t x, rearArclength (delta t) (sf t x) = x) ∧
      ∀ (etaR : ℝ → ℝ → ℝ) (XR nuR : ℝ → ℝ → ℂ),
        (∀ t x, HasDerivAt (etaR t)
          (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x) →
        (∀ t, Function.Periodic (etaR t) (rearArclength (delta t) (P t))) →
        (∀ u, XR 0 u = p'.1 u) → (∀ u, XR Γ.T u = q'.1 u) →
        (∀ t u, HasDerivAt (fun r => XR r u)
          ((etaR t (rearArclength (delta t) (P t) * u) : ℂ) * nuR t u) t) →
        (∀ u, Continuous fun t =>
          (etaR t (rearArclength (delta t) (P t) * u) : ℂ) * nuR t u) →
        (∀ t u, ‖nuR t u‖ = 1) →
        ∃ Δ : PathMetric.NormalPath p' q', Δ.T = Γ.T ∧
          PathMetric.NormalPath.cost Δ = PathMetricJacobi.jacobiConst
            (SelectedInversePathGeometry.uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
            (SelectedInversePathGeometry.uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2)))
            (SelectedInversePathGeometry.uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
            (SelectedInversePathGeometry.uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh)
            * PathMetric.NormalPath.cost Γ := by
  have hP : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨delta, sf, hper, hs0, hs1, hode, hsf, -⟩ :=
    exists_selected_steering_family hkh0 hkh1 hP hKc hKper hK0 hKk
  have hK : ∀ t s, |K t s| ≤ kh := fun t s => abs_le.mpr
    ⟨by linarith [hK0 t s, hKk t s], hKk t s⟩
  refine ⟨delta, sf, hper, fun t s => ⟨hs0 t s, hs1 t s⟩, hode, hsf, ?_⟩
  intro etaR XR nuR hetaR hetaRper hstart hfinish hderiv hcont hnu
  exact SelectedInversePathGeometry.exists_normalPath_of_geometry Γ hP0 hkh0 hkh1 hPl hPu
    hode hs0 hs1 hper hK hetaFd hetaFsc hetaFper hsf hetaR hetaRper hlink hstart hfinish
    hderiv hcont hnu

end SelectedSteeringFamily
