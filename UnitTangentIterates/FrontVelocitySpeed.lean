import Mathlib
import UnitTangentIterates.RearOwnPathDistSlices
import UnitTangentIterates.PathMetricSpeed

/-!
# The front normal velocity of a slow path is small

The constants of the path-distance bound for the selected rears
(`RearOwnPathDistFrontOnly.lean` and the files built on it) are not driven by
the *cost* of the normal path but by a sup bound `E_F` for the **front normal
velocity** along it,

`∀ t s, |η_F(t, s)| ≤ E_F`,

which the assembled statements produce by a compactness argument over the time
window; the constant therefore depends on the path, and a Lipschitz bound
uniform over the tube cannot be read off from them.

`PathMetricSpeed.exists_unitTime_bounded_speed` removes that obstruction on the
side of the path: every normal path may be run, at an arbitrarily small extra
cost, with its normal speed bounded by `3/2` times its cost.  This file
transports that bound to the front side.  If the moving curve of the path is
the family of fronts read in the normalized parameter — the geometric
identification of `RearOwnPathDistSlices.lean` — then the normal speed of the
path *is* the front normal velocity, so a bound for the one is a bound for the
other:

* `frontNormalVelocity_le_of_link` : from the identification and a bound on the
  cost density;
* `frontNormalVelocity_le_of_slices` : with the identification produced from the
  geometry of the slices;
* `exists_slow_front_path` : the two statements combined — every normal path of
  fronts is, up to an arbitrarily small extra cost, a path of duration one along
  which the front normal velocity is everywhere at most `3/2` times the cost.

Together with `PathMetricSpeed.pathDist_le_mul_of_maps_slow_paths` this makes
the sup bound `E_F` of those constants a function of the pseudodistance of the
two curves alone, rather than of the chosen path.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearFamilyFrame

namespace FrontVelocitySpeed

open SelectedInverseJacobiODE RearOwnPathDistSlices RearOwnHigherRegularity

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **A bound for the cost density of the path bounds the front normal
velocity.**  Every arclength `s` is the normalized parameter `s / P t` read in
the current period, at which the normal speed of the path is the front normal
velocity. -/
theorem frontNormalVelocity_le_of_link {p q : Data} (Γ : NormalPath p q) {M : ℝ}
    (hPpos : ∀ t, 0 < P t)
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    (hm : ∀ t, Γ.m t ≤ M) (t s : ℝ) :
    |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ M := by
  have hP : P t ≠ 0 := (hPpos t).ne'
  have hs : P t * (s / P t) = s := by field_simp
  have h := hlink t (s / P t)
  rw [hs] at h
  rw [← h]
  exact le_trans (Γ.abs_eta_le t (s / P t)) (hm t)

/-- **The same bound, with the identification produced from the geometry of the
slices.**  If the moving marked curve of the path is the family of fronts read
in the normalized parameter, with the standard unit normal, then a bound for the
cost density of the path is a bound for the front normal velocity. -/
theorem frontNormalVelocity_le_of_slices {p q : Data} (Γ : NormalPath p q) {M : ℝ}
    (hFdiff : Differentiable ℝ (uncurry F))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hPdiff : Differentiable ℝ P) (hPpos : ∀ t, 0 < P t)
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (hm : ∀ t, Γ.m t ≤ M) (t s : ℝ) :
    |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ M :=
  frontNormalVelocity_le_of_link (δ := δ) Γ hPpos
    (fun t u => eta_eq_frontNormalVelocity (δ := δ) Γ hFdiff hF hPdiff hX hnu t u) hm t s

/-- **Every normal path of fronts can be run with a small front normal
velocity.**  At an arbitrarily small extra cost the path may be taken of
duration one, with the front normal velocity of *its own* family of fronts
bounded by `3/2` times its cost.

The family of fronts of the reparametrized path is the family of fronts of the
original one, read at the changed time; the statement is therefore about the
composed family `F ∘ ψ`, which is what the identification of the slices produces
for the new path. -/
theorem exists_slow_front_path {p q : Data} (Γ : NormalPath p q) {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ : NormalPath p q, Δ.T = 1 ∧ cost Δ = cost Γ + ε ∧
      ∀ (G : ℝ → ℝ → ℂ) (Ξ : ℝ → ℝ → ℝ) (Q : ℝ → ℝ),
        Differentiable ℝ (uncurry G) →
        (∀ t s, HasDerivAt (G t) (Complex.exp (Complex.I * (Ξ t s : ℂ))) s) →
        Differentiable ℝ Q → (∀ t, 0 < Q t) →
        (∀ t u, Δ.X t u = G t (Q t * u)) →
        (∀ t u, Δ.nu t u = Complex.I * Complex.exp (Complex.I * (Ξ t (Q t * u) : ℂ))) →
        ∀ t s, |frontNormalVelocityAt (partialTime G) Ξ δ t s| ≤ (3 / 2) * (cost Γ + ε) := by
  obtain ⟨Δ, hT, hcost, hm⟩ := exists_unitTime_bounded_speed Γ hε
  exact ⟨Δ, hT, hcost, fun G Ξ Q hGdiff hG hQdiff hQpos hX hnu t s =>
    frontNormalVelocity_le_of_slices (δ := δ) Δ hGdiff hG hQdiff hQpos hX hnu hm t s⟩

end FrontVelocitySpeed
