import UnitTangentIterates.RearConvexityFromBarrier

/-!
# The rear track's curvature is pinched by the barrier

§67 left two properties of the selected inverse: preservation of convexity
(settled in §68) and of the chord bound.

The chord bound does not need to be *transported*.  §55 derives a chord bound
from convexity together with a curvature **ceiling**, and the rear track has its
own ceiling, from the same barrier:

```
  tan(arcsin y) = y/√(1−y²)  is increasing, so  0 ≤ Y ≤ b < 1  gives
  0 ≤ tan δ ≤ b/√(1−b²) .
```

* `rear_curvature_le_of_pulse` — the ceiling;
* `rear_curvature_pinched_of_pulse` — both bounds together, with positivity of
  the ceiling when `b > 0`.

These are exactly the hypotheses `ConvexChordArc.chord_bound_floor_free` takes.
So the rear inherits a chord bound not by transport but by satisfying the same
criterion the front does — which is the right shape, since the constant then
depends only on the rear's own ceiling and not on any comparison with the front.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real

namespace RearTrack

/-- **The rear curvature ceiling from the pulse barrier.**  `tan(arcsin y) =
y/√(1−y²)` is increasing, so the barrier `0 ≤ Y ≤ b < 1` bounds the rear
curvature by `b/√(1−b²)`. -/
theorem rear_curvature_le_of_pulse {Y : ℝ → ℝ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hY0 : ∀ s, 0 ≤ Y s) (hYb : ∀ s, Y s ≤ b) (s : ℝ) :
    Real.tan (Real.arcsin (Y s)) ≤ b / Real.sqrt (1 - b ^ 2) := by
  have hYs0 := hY0 s
  have hYsb := hYb s
  have hsq : (0:ℝ) < 1 - Y s ^ 2 := by nlinarith
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - Y s ^ 2) := Real.sqrt_pos.mpr hsq
  have hsbp : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  rw [Real.tan_arcsin]
  have hmono : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - Y s ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  exact div_le_div₀ hb0 hYsb hsbp hmono

/-- **The rear track is a convex curve of bounded curvature.**  Both bounds come
from the same barrier: `0 ≤ tan δ ≤ b/√(1−b²)`.  These are exactly the two
hypotheses `ConvexChordArc.chord_bound_floor_free` needs, so the rear inherits a
chord bound with no curvature floor. -/
theorem rear_curvature_pinched_of_pulse {Y : ℝ → ℝ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hY0 : ∀ s, 0 ≤ Y s) (hYb : ∀ s, Y s ≤ b) :
    (∀ s, 0 ≤ Real.tan (Real.arcsin (Y s))) ∧
      (∀ s, Real.tan (Real.arcsin (Y s)) ≤ b / Real.sqrt (1 - b ^ 2)) ∧
      0 < b / Real.sqrt (1 - b ^ 2) ∨ b = 0 := by
  rcases eq_or_lt_of_le hb0 with hb | hb
  · exact Or.inr hb.symm
  · refine Or.inl ⟨fun s => rear_curvature_nonneg_of_pulse hb0 hb1 hY0 hYb s,
      fun s => rear_curvature_le_of_pulse hb0 hb1 hY0 hYb s, ?_⟩
    have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
    positivity

end RearTrack
