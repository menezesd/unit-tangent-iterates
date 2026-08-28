import UnitTangentIterates.MarkedSpace

/-!
# Floor-free tube membership

§66 reduced `hmem` to tube invariance of the selected inverse.  The existing
membership criteria (`PinchedCurveSelInv.isTubeMember_of_isPinchedCurve`,
`SelInvPathTubeC2.isTubeMember_of_slice`) all require `0 < kminP`, and produce a
chord constant `chordConstSpeed … (perim · kminP) …` that degenerates with it —
so they cannot be used on the floor-free route, for the reason §47 established.

This file records what the floor-free tube actually asks.  With `kmin = 0` the
curvature field is exactly convexity:

```
  0 · ‖V‖³ ≤ Im(conj V · A)   ⟺   0 ≤ Im(conj V · A) .
```

`isTubeMember_zero_of_convex_and_chord` therefore builds membership from: the
two derivative relations, closedness, constant speed, speed at least `c`,
**convexity**, and a chord bound.  `convex_of_isTubeMember_zero` is the converse
reading of the curvature field.

Both of the substantive inputs are available without a floor — convexity is what
the construction supplies (`0 ≤ κ`), and the chord bound is §§55–57.  So tube
invariance of the selected inverse reduces to: the inverse preserves convexity
and the chord bound, together with the four structural fields.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Function

namespace MarkedSpace

/-- **Floor-free tube membership.**  With `kmin = 0` the curvature field of
`IsTubeMember` is exactly convexity, `0 ≤ Im(conj V · A)`.  So a closed
constant-speed `C²` curve of speed at least `c` belongs to the floor-free tube
as soon as it is convex and satisfies a chord bound — the two things §§55–57
supply for the two-cap model without any curvature floor. -/
theorem isTubeMember_zero_of_convex_and_chord {p : Data} {c delta : ℝ}
    (hd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hper : Periodic (⇑p.1) 1)
    (hconst : ∀ u v, ‖p.2.1 u‖ = ‖p.2.1 v‖)
    (hspeed : ∀ u, c ≤ ‖p.2.1 u‖)
    (hconvex : ∀ u, 0 ≤ ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im)
    (hchord : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      delta * cyc u v ≤ ‖p.1 u - p.1 v‖) :
    IsTubeMember c 0 delta p where
  hasDerivAt_curve := hd
  hasDerivAt_vel := hd2
  periodic := hper
  speed_const := hconst
  speed_lb := hspeed
  curv_lb := fun u => by simpa using hconvex u
  chord := hchord

/-- Conversely, membership of the floor-free tube gives back convexity. -/
theorem convex_of_isTubeMember_zero {p : Data} {c delta : ℝ}
    (hp : IsTubeMember c 0 delta p) :
    ∀ u, 0 ≤ ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im := by
  intro u
  have := hp.curv_lb u
  simpa using this

end MarkedSpace
