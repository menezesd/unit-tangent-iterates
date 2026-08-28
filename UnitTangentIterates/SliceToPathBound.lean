import UnitTangentIterates.PathMetric

/-!
# From slicewise Jacobi estimates to the path bound

§65 reduced the scheme's `hmap` to the per-path Jacobi bound
`pathDist (B p) (B q) ≤ K · cost Γ`.  This file supplies the passage from the
*slicewise* estimates — which is what `JacobiEstimates` and `JacobiPathGains`
prove — to that bound.

`cost_le_of_slice_domination` : if the pullback path's cost density satisfies

```
  Δ.m t ≤ C · ∫₀¹ |Γ.eta t u| du       for every t,
```

then `cost Δ ≤ C · cost Γ`.

Note what does **not** appear: any factor of the perimeter.  The normal
parameter of a `NormalPath` is normalized to `[0,1]`, and the structure's own
field `le_m_L1` already bounds `∫₀¹|η| ` by the cost density.  The earlier
worry (§62) that converting `W` back to `cost` would cost a factor `2Hₙ` was
about the unnormalized functional; in the normalized parameter the conversion is
free.

`pathDist_le_of_slice_domination` is the same conclusion for the pseudodistance,
which is the form §65 consumes.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MeasureTheory MarkedSpace

namespace PathMetric

open NormalPath

/-- **Slice domination gives a cost bound.**  If the pullback path's cost
density is dominated slicewise by `C` times the `L¹` norm of the original's
normal field, its total cost is at most `C` times the original's.  No factor of
the perimeter appears: the normal parameter is normalized to `[0,1]`, and
`NormalPath.le_m_L1` already bounds that `L¹` norm by the cost density. -/
theorem cost_le_of_slice_domination {p q p' q' : Data} {C : ℝ}
    (hC : 0 ≤ C) (Γ : NormalPath p q) (Δ : NormalPath p' q')
    (hT : Δ.T = Γ.T) (hT0 : 0 ≤ Γ.T)
    (hmi : IntervalIntegrable Δ.m volume 0 Δ.T)
    (hgi : IntervalIntegrable (fun t => C * Γ.m t) volume 0 Γ.T)
    (hm : ∀ t, Δ.m t ≤ C * ∫ u in (0:ℝ)..1, |Γ.eta t u|) :
    cost Δ ≤ C * cost Γ := by
  have hstep : ∀ t, Δ.m t ≤ C * Γ.m t := fun t =>
    le_trans (hm t) (mul_le_mul_of_nonneg_left (Γ.le_m_L1 t) hC)
  rw [cost, cost, hT]
  refine le_trans (intervalIntegral.integral_mono_on hT0 (by rwa [hT] at hmi) hgi
    (fun t _ => hstep t)) ?_
  rw [intervalIntegral.integral_const_mul]

/-- Hence the path pseudodistance of the images is controlled. -/
theorem pathDist_le_of_slice_domination {p q p' q' : Data} {C : ℝ}
    (hC : 0 ≤ C) (Γ : NormalPath p q) (Δ : NormalPath p' q')
    (hT : Δ.T = Γ.T) (hT0 : 0 ≤ Γ.T)
    (hmi : IntervalIntegrable Δ.m volume 0 Δ.T)
    (hgi : IntervalIntegrable (fun t => C * Γ.m t) volume 0 Γ.T)
    (hm : ∀ t, Δ.m t ≤ C * ∫ u in (0:ℝ)..1, |Γ.eta t u|) :
    pathDist p' q' ≤ C * cost Γ :=
  le_trans (pathDist_le_cost Δ)
    (cost_le_of_slice_domination hC Γ Δ hT hT0 hmi hgi hm)

end PathMetric
