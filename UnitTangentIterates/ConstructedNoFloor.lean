import UnitTangentIterates.ConstructedConfiguredSequence
import UnitTangentIterates.CurvatureFloorObstruction

/-!
# The construction admits no positive curvature floor

`CurvatureFloorObstruction` proved abstractly that a positive curvature floor
`kmin > 0` is incompatible with total turning `π` on separations that grow
without bound.  This file connects that obstruction to the sequence the
construction actually produces.

`MarkedSpace.unit_tangent_iterates_main_theorem` takes `hkminpos : 0 < kmin`
together with `hkmin : ∀ n s, kmin ≤ kappas n s` and
`htotal : ∀ n, ∫₀^{Hₙ} κₙ = π`.  The configured model sequence of
`exists_configuredModelSequence_of_eps` satisfies `htotal` and grows linearly,
so **those hypotheses cannot be met simultaneously**: the main theorem, as
stated, is not instantiable from the construction.

This is not a gap in the construction — it is a defect in the way the closing
theorem is parameterized.  The repair is the floor-free route already present in
`CurvatureFloorFreeFamily`, where the tube is taken with `kmin = 0` and the
curvature is only required nonnegative.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real

/-- **The sequence the construction produces admits no positive curvature
floor.**  Its total turning is `π` on every period and its separations grow
linearly, and those two force the infimum of the curvature to zero. -/
theorem no_positive_floor_of_eps {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ) (Delta : ℝ),
      0 < Delta ∧ (∀ n, 0 < Hs n) ∧
      (∀ n, Continuous (kappas n)) ∧
      (∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) ∧
      (∀ n : ℕ, Hs 0 + n * Delta ≤ Hs n) ∧
      ¬ ∃ kmin : ℝ, 0 < kmin ∧ ∀ n s, kmin ≤ kappas n s := by
  obtain ⟨kappas, Hs, deltaStep, kd, kstar, cst, beta, hdelta, hstep, ⟨model⟩,
    hsum⟩ := exists_configuredModelSequence_of_eps heps heps10
  have hHpos : ∀ n, 0 < Hs n := model.separation_pos
  have hcont : ∀ n, Continuous (kappas n) := model.curvature_continuous
  have htotal := model.total_turning
  have hgrow : ∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have := hstep n
        push_cast
        nlinarith [ih, this, hdelta]
  refine ⟨kappas, Hs, deltaStep, hdelta, hHpos, hcont, htotal, hgrow, ?_⟩
  · rintro ⟨kmin, hkmin0, hkmin⟩
    exact CurvatureFloorObstruction.not_forall_of_curvature_floor_of_linear_growth
      hkmin0 hHpos hcont hkmin htotal (by linarith : (0:ℝ) < 2 * deltaStep)
      (by intro n; have := hgrow n; nlinarith [this])
