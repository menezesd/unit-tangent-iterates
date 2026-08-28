import UnitTangentIterates.VariableMarkedTube
import UnitTangentIterates.ChordArc

/-!
# Local stability of the variable marked tube

A triangular row need not retain products of all preceding gauge-flow
distortions.  Uniform marked `C2` closeness to the fixed row model directly
gives uniform speed and chord constants.  Nonnegative oriented curvature is
kept explicit because a zero curvature floor is a closed, not open,
condition.
-/

noncomputable section

open Set Function

namespace VariableMarkedTubeLocalStability

open MarkedSpace VariableMarkedTube

/-- Acceleration evaluation is dominated by the marked `C2` distance. -/
theorem dist_acc_apply_le (p q : Data) (u : ℝ) :
    ‖p.2.2 u - q.2.2 u‖ ≤ dist p q := by
  have h1 : dist (p.2.2 u) (q.2.2 u) ≤ dist p.2.2 q.2.2 :=
    BoundedContinuousFunction.dist_coe_le_dist u
  have h2 : dist p.2.2 q.2.2 ≤ dist p.2 q.2 := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have h3 : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  rw [← dist_eq_norm]
  exact h1.trans (h2.trans h3)

/-- One fixed marked ball around an ordinary tube member lies in a uniform
variable-speed tube, provided the endpoint orientation is nonnegative.

The resulting speed constants are explicit: `c0 - r` and
`perim base + r`.  The remaining scalar inequalities are precisely the
near-diagonal acceleration budget and far-diagonal chord margin used by
`ChordArc.chord_arc_stable_of_acc_bound`. -/
theorem variableTube_of_dist_le
    {base p : Data} {c0 d0 r A0 rho dlt : ℝ}
    (hbase : IsTubeMember c0 0 d0 base)
    (hcurve : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hperiodic : Periodic (⇑p.1) 1)
    (hdist : dist base p ≤ r)
    (hbase_acc : ∀ u, ‖base.2.2 u‖ ≤ A0)
    (hcurv : ∀ u, 0 ≤ ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im)
    (hr : 0 ≤ r) (hc : 0 < c0 - r) (hA0 : 0 ≤ A0)
    (hrho : 0 < rho) (hrhohalf : rho ≤ 1 / 2)
    (hArho : (A0 + r) * rho ≤ (c0 - r) / 2)
    (hdlt0 : 0 ≤ dlt) (hdltc : dlt ≤ (c0 - r) / 2)
    (hmargin : 2 * r ≤ (d0 - dlt) * rho) :
    IsVariableTubeMember (c0 - r) (perim base + r) 0 dlt p := by
  have hspeed : ∀ u, c0 - r ≤ ‖p.2.1 u‖ := by
    intro u
    have hvR := (MarkedSpace.dist_vel_apply_le base p u).trans hdist
    have htri : ‖base.2.1 u‖ ≤
        ‖base.2.1 u - p.2.1 u‖ + ‖p.2.1 u‖ := by
      calc
        ‖base.2.1 u‖ = ‖(base.2.1 u - p.2.1 u) + p.2.1 u‖ := by ring
        _ ≤ ‖base.2.1 u - p.2.1 u‖ + ‖p.2.1 u‖ := norm_add_le _ _
    linarith [hbase.speed_lb u]
  have hspeedUpper : ∀ u, ‖p.2.1 u‖ ≤ perim base + r := by
    intro u
    have hvR : ‖p.2.1 u - base.2.1 u‖ ≤ r := by
      exact (MarkedSpace.dist_vel_apply_le p base u).trans
        (by simpa [dist_comm] using hdist)
    calc
      ‖p.2.1 u‖ = ‖(p.2.1 u - base.2.1 u) + base.2.1 u‖ := by ring
      _ ≤ ‖p.2.1 u - base.2.1 u‖ + ‖base.2.1 u‖ := norm_add_le _ _
      _ ≤ r + perim base := add_le_add hvR (norm_vel_eq_perim hbase u).le
      _ = perim base + r := add_comm _ _
  have hacc : ∀ u, ‖p.2.2 u‖ ≤ A0 + r := by
    intro u
    have haR : ‖p.2.2 u - base.2.2 u‖ ≤ r := by
      exact (dist_acc_apply_le p base u).trans
        (by simpa [dist_comm] using hdist)
    calc
      ‖p.2.2 u‖ = ‖(p.2.2 u - base.2.2 u) + base.2.2 u‖ := by ring
      _ ≤ ‖p.2.2 u - base.2.2 u‖ + ‖base.2.2 u‖ := norm_add_le _ _
      _ ≤ r + A0 := add_le_add haR (hbase_acc u)
      _ = A0 + r := add_comm _ _
  have hclose : ∀ u, ‖p.1 u - base.1 u‖ ≤ r := by
    intro u
    exact (MarkedSpace.dist_apply_le p base u).trans
      (by simpa [dist_comm] using hdist)
  have hchord := ChordArc.chord_arc_stable_of_acc_bound
    hcurve hvel (MarkedSpace.periodic_of_hasDerivAt hcurve hperiodic)
    hperiodic hspeed hacc hbase.chord hclose (add_nonneg hA0 hr)
    hrho hrhohalf hArho hdlt0 hdltc hmargin
  exact
    { hasDerivAt_curve := hcurve
      hasDerivAt_vel := hvel
      periodic := hperiodic
      speed_lb := hspeed
      speed_ub := hspeedUpper
      curv_lb := fun u => by simpa using hcurv u
      chord := hchord }

/-- Family form used by a triangular row.  A single radius and scalar budget
give constants independent of the depth index. -/
theorem family_variableTube_of_dist_le
    {ι : Type*} {base : Data} {p : ι → Data}
    {c0 d0 r A0 rho dlt : ℝ}
    (hbase : IsTubeMember c0 0 d0 base)
    (hcurve : ∀ i u, HasDerivAt (⇑(p i).1) ((p i).2.1 u) u)
    (hvel : ∀ i u, HasDerivAt (⇑(p i).2.1) ((p i).2.2 u) u)
    (hperiodic : ∀ i, Periodic (⇑(p i).1) 1)
    (hdist : ∀ i, dist base (p i) ≤ r)
    (hbase_acc : ∀ u, ‖base.2.2 u‖ ≤ A0)
    (hcurv : ∀ i u, 0 ≤
      ((starRingEnd ℂ) ((p i).2.1 u) * (p i).2.2 u).im)
    (hr : 0 ≤ r) (hc : 0 < c0 - r) (hA0 : 0 ≤ A0)
    (hrho : 0 < rho) (hrhohalf : rho ≤ 1 / 2)
    (hArho : (A0 + r) * rho ≤ (c0 - r) / 2)
    (hdlt0 : 0 ≤ dlt) (hdltc : dlt ≤ (c0 - r) / 2)
    (hmargin : 2 * r ≤ (d0 - dlt) * rho) :
    ∀ i, IsVariableTubeMember (c0 - r) (perim base + r) 0 dlt (p i) := by
  intro i
  exact variableTube_of_dist_le hbase (hcurve i) (hvel i) (hperiodic i)
    (hdist i) hbase_acc (hcurv i) hr hc hA0 hrho hrhohalf hArho
    hdlt0 hdltc hmargin

end VariableMarkedTubeLocalStability
