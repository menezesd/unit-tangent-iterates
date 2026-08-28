import UnitTangentIterates.RearTrack
import UnitTangentIterates.HairpinPulseBarrier
import UnitTangentIterates.HairpinLowerComparisonInterior

/-!
# Rear convexity from the pulse barrier

§67 reduced tube invariance to two properties of the selected inverse: that it
preserves convexity, and that it preserves the chord bound.  This file settles
the first.

The steering angle of the selected rear is `δ = arcsin Y`, and its curvature is
`tan δ`.  `RearTrack.rear_curvature_nonneg` gives `0 ≤ tan δ` from
`0 ≤ δ ≤ arcsin κ̂` with `κ̂ < 1`.  §18's barrier supplies exactly that:
`0 ≤ Y ≤ 1/√(1+m²) < 1` uniformly, from the profile's lower barrier `f ≥ m`.

* `rear_curvature_nonneg_of_pulse` — the general form, from `0 ≤ Y ≤ b < 1`;
* `rear_curvature_nonneg_of_barrier` — with the barrier constant already
  substituted.

So the convexity half of tube invariance is not an extra hypothesis: it follows
from the same barrier that gives `sup y ≤ b < 1`, which is the fact that has
been doing the work since §18.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real


namespace RearTrack

/-- **Rear convexity from the pulse barrier.**  The steering angle of the
selected rear is `δ = arcsin Y`, and §18's barrier gives `0 ≤ Y ≤ b < 1`
uniformly.  Hence `0 ≤ δ ≤ arcsin b` and the rear curvature `tan δ` is
nonnegative — the convexity that the floor-free tube asks for. -/
theorem rear_curvature_nonneg_of_pulse {Y : ℝ → ℝ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hY0 : ∀ s, 0 ≤ Y s) (hYb : ∀ s, Y s ≤ b) (s : ℝ) :
    0 ≤ Real.tan (Real.arcsin (Y s)) := by
  refine rear_curvature_nonneg (δ := fun r => Real.arcsin (Y r)) hb1 hb0 ?_ ?_
  · exact Real.arcsin_nonneg.mpr (hY0 s)
  · exact Real.arcsin_le_arcsin (hYb s)

/-- The same, with the barrier constant of `HairpinRelative.pulseField_le_of_barrier`
already in place: for a profile bounded below by `m > 0`, the pulse never
reaches one, so the rear is convex. -/
theorem rear_curvature_nonneg_of_barrier {f theta x : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m) (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π) (s : ℝ) :
    0 ≤ Real.tan (Real.arcsin
      (HairpinRelative.pulseField f (theta (x s)))) := by
  refine rear_curvature_nonneg_of_pulse (b := 1 / Real.sqrt (1 + m ^ 2))
    (by positivity) (HairpinRelative.one_div_sqrt_one_add_sq_lt_one hm)
    (fun r => HairpinRelative.pulseField_nonneg_interior hfpos (hmem (x r)))
    (fun r => HairpinRelative.pulseField_le_of_barrier hm
      (hlow _ (hmem (x r))) (hmem (x r))) s

end RearTrack
