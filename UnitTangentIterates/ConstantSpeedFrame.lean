import UnitTangentIterates.NormalPathC2Increment

/-!
# What the scheme's path hypothesis supplies

The geometric scheme's `hmap` is quantified over paths satisfying
`IsConstantSpeedNormalPath P0 P1 khat`.  That is not a bare path: it carries

* the speed `P` and its derivative, with `P ≤ P₁`;
* the tangent angle `theta`, with `X' = P·e^{iθ}` and `θ' = P·κ`;
* the curvature `kappa`, with the **ceiling** `|κ| ≤ κ̂`;
* the time derivatives `etas = ∂ₜθ` and `kt = ∂ₜκ`, each bounded by a fixed
  multiple of the path's own cost density `Γ.m`.

`exists_frame_of_constantSpeed` unpacks all of it;
`exists_curvature_le_of_constantSpeed` extracts the ceiling alone.

This matters for the threading of §72 because those are precisely the data
`GaugeRearFamilyFromFront`'s constructor consumes — the front family with its
angle and curvature, the regularity in time, and the bounds by the cost density.
So `hmap` is an unpack-and-feed, not a construction: the hypothesis carries what
the constructor needs.

It also explains why the curvature ceiling appears in `hmap`'s hypothesis at
all.  It is the same ceiling that §55 uses for the floor-free chord bound and
§69 for the rear's — the single quantity that replaced the unavailable floor
throughout §§47–69.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MarkedSpace PathMetric

namespace NormalPathC2Increment

/-- **What `IsConstantSpeedNormalPath` supplies.**  The hypothesis of the
scheme's `hmap` is not a bare path: it carries the tangent angle, the curvature,
their time derivatives, and bounds on all of them by the path's own cost
density.  These are exactly the data the rear-family constructor of
`GaugeRearFamilyFromFront` consumes, so the threading of §72 is unpacking and
feeding rather than construction. -/
theorem exists_frame_of_constantSpeed {P0 P1 khat : ℝ} {p q : Data}
    {Γ : NormalPath p q} (h : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    ∃ (P Pd : ℝ → ℝ) (theta kappa etas kt : ℝ → ℝ → ℝ),
      (∀ t, 0 ≤ P t) ∧ (∀ t, P t ≤ P1) ∧ (∀ t u, |kappa t u| ≤ khat) ∧
      (∀ t u, HasDerivAt (Γ.X t)
        ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u) ∧
      (∀ t u, HasDerivAt (theta t) (P t * kappa t u) u) ∧
      (∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t) ∧
      (∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t) ∧
      (∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t) ∧
      (∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * Γ.m t) := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hP0, hP1, hk, hX, hth, hPd, hPdc,
    hPdb, hthT, hthTc, hetas, hkT, hktc, hkt⟩ := h
  exact ⟨P, Pd, theta, kappa, etas, kt, hP0, hP1, hk, hX, hth, hthT, hetas,
    hkT, hkt⟩

/-- In particular the curvature ceiling, which is what the floor-free chord
bound (§55) and the rear-family constructor both ask for. -/
theorem exists_curvature_le_of_constantSpeed {P0 P1 khat : ℝ} {p q : Data}
    {Γ : NormalPath p q} (h : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    ∃ kappa : ℝ → ℝ → ℝ, ∀ t u, |kappa t u| ≤ khat := by
  obtain ⟨-, -, -, kappa, -, -, -, -, hk, -⟩ := exists_frame_of_constantSpeed h
  exact ⟨kappa, hk⟩

end NormalPathC2Increment
