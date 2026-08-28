import UnitTangentIterates.ChordFloorFree
import UnitTangentIterates.ModelChordNear

/-!
# The model's chord-arc bound, without a curvature floor

Feeding `ConvexChordArc.chord_bound_floor_free` (§55) into the two-cap model.

* `chord_front_of_le_halfPeriod` — the tangent turns by exactly `π` over a half
  period (`frontAngle_add_halfPeriod`), so on any sub-arc of length at most `H`
  the turning is at most `π` and the floor-free bound applies:

  ```
    min((y−x)/2, π/(12·kap)) ≤ ‖front y − front x‖ .
  ```

* `chord_front_cyclic` — extended across the period by `front_periodic`.  Two
  points of the closed curve are joined by an arc of length at most `H` on one
  side or the other, so with
  `cyc(x,y) = min(y−x, 2H−(y−x))`,

  ```
    min(cyc(x,y)/2, π/(12·kap)) ≤ ‖front y − front x‖ .
  ```

Both constants are uniform in the separation `H`: the first depends on nothing,
the second only on the curvature ceiling.  That is what the tube's `chord` field
needs, and what a curvature floor was previously being used to supply.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Function


namespace TwoCapPairsAssembly

/-- **The floor-free chord bound for the model front, within a half period.**
The tangent turns by exactly `π` over a half period, so on any sub-arc of length
at most `H` the turning is at most `π` and `chord_bound_floor_free` applies. -/
theorem chord_front_of_le_halfPeriod {kappa : ℝ → ℝ} {theta0 H kap : ℝ}
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap) (hkap0 : 0 < kap)
    {x y : ℝ} (hxy : x ≤ y) (hle : y ≤ x + H) :
    min ((y - x) / 2) (π / (12 * kap))
      ≤ ‖front kappa theta0 H y - front kappa theta0 H x‖ := by
  have hX : ∀ s, HasDerivAt (front kappa theta0 H)
      (Complex.exp ((frontAngle kappa theta0 s : ℂ) * Complex.I)) s := by
    intro s
    have h := front_hasDerivAt (kappa := kappa) (theta0 := theta0) (H := H) hk s
    have he : Complex.exp (Complex.I * (frontAngle kappa theta0 s : ℂ))
        = Complex.exp ((frontAngle kappa theta0 s : ℂ) * Complex.I) := by
      rw [mul_comm]
    rwa [he] at h
  have hth : ∀ s, HasDerivAt (frontAngle kappa theta0) (kappa s) s := fun s =>
    CurvatureInterpolation.hasDerivAt_tangentAngle (θ₀ := theta0) hk s
  have hmono := ConvexChordArc.theta_monotone hth hk0
  have hturn : frontAngle kappa theta0 y - frontAngle kappa theta0 x ≤ π := by
    have h1 : frontAngle kappa theta0 y ≤ frontAngle kappa theta0 (x + H) :=
      hmono hle
    have h2 : frontAngle kappa theta0 (x + H)
        = frontAngle kappa theta0 x + π :=
      frontAngle_add_halfPeriod (kappa := kappa) (theta0 := theta0) (H := H)
        hk hper htotal x
    linarith [h1, h2.le, h2.ge]
  exact ConvexChordArc.chord_bound_floor_free hX hth hk0 hkap hkap0 hxy hturn

/-- **The cyclic floor-free chord bound for the model front.**  Extending
`chord_front_of_le_halfPeriod` across the period by `front_periodic`: the two
points are joined by an arc of length at most `H` on one side or the other. -/
theorem chord_front_cyclic {kappa : ℝ → ℝ} {theta0 H kap : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap) (hkap0 : 0 < kap)
    {x y : ℝ} (hxy : x ≤ y) (hlt : y - x ≤ 2 * H) :
    min (min (y - x) (2 * H - (y - x)) / 2) (π / (12 * kap))
      ≤ ‖front kappa theta0 H y - front kappa theta0 H x‖ := by
  have hfp : Function.Periodic (front kappa theta0 H) (2 * H) :=
    front_periodic (kappa := kappa) (theta0 := theta0) (H := H) hk hper htotal
  rcases le_or_gt (y - x) H with hc | hc
  · have hmin : min (y - x) (2 * H - (y - x)) = y - x := by
      apply min_eq_left; linarith
    rw [hmin]
    exact chord_front_of_le_halfPeriod hk hper htotal hk0 hkap hkap0 hxy
      (by linarith)
  · have hmin : min (y - x) (2 * H - (y - x)) = 2 * H - (y - x) := by
      apply min_eq_right; linarith
    rw [hmin]
    have hshift : front kappa theta0 H (y - 2 * H) = front kappa theta0 H y := by
      have := hfp (y - 2 * H)
      simpa using this.symm
    have hxy' : y - 2 * H ≤ x := by linarith
    have hle' : x ≤ (y - 2 * H) + H := by linarith
    have h := chord_front_of_le_halfPeriod (theta0 := theta0) hk hper htotal
      hk0 hkap hkap0 hxy' hle'
    have heq : x - (y - 2 * H) = 2 * H - (y - x) := by ring
    rw [heq] at h
    calc min ((2 * H - (y - x)) / 2) (π / (12 * kap))
        ≤ ‖front kappa theta0 H x - front kappa theta0 H (y - 2 * H)‖ := h
      _ = ‖front kappa theta0 H y - front kappa theta0 H x‖ := by
          rw [hshift, norm_sub_rev]

end TwoCapPairsAssembly
