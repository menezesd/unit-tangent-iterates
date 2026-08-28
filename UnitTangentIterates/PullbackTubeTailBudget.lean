import UnitTangentIterates.ChordArc
import UnitTangentIterates.TubePullbackLimit
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.TubeArclengthAngle

/-!
# Diagonal pullback membership from a summable radius margin

This is the quantitative replacement for a raw closed-tube preservation
callback.  The model carries strict speed and chord margins.  A diagonal
pullback is known to have the closed structural fields and to remain within
the weighted remaining-tail radius in marked distance.  The speed margin and
`ChordArc.chord_arc_stable_of_acc_bound` then put it in the target tube.
-/

noncomputable section

open Set Function MarkedSpace PathMetric

namespace PullbackTubeTailBudget

/-- The marked remaining-tail radius in row `n`. -/
def radius (C K : ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ShadowingTails.tail (fun k => C * (K ^ k * d (n + k))) 0

/-- Quantitative data sufficient to recover the exact diagonal tube
membership used by the local pullback theorem.  `weak_mem` contains only the
closed differential, periodic, constant-speed, and nonnegative-curvature
facts; its zero speed/chord constants carry no hidden positive margin.
-/
structure Budget
    (B : Data → Data) (Q : ℕ → Data) (C K : ℝ) (d : ℕ → ℝ)
    (c d0 dlt : ℝ) (A0 rho : ℕ → ℝ) : Prop where
  c_pos : 0 < c
  radius_nonneg : ∀ n, 0 ≤ radius C K d n
  model_mem : ∀ n, IsTubeMember (c + radius C K d n) 0 d0 (Q n)
  weak_mem : ∀ n k, IsTubeMember 0 0 0
    (TubePullbackLimit.pullback B Q n k)
  marked_tail : ∀ n k, dist (Q n) (TubePullbackLimit.pullback B Q n k) ≤
    radius C K d n
  model_acc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n
  acc_nonneg : ∀ n, 0 ≤ A0 n
  rho_pos : ∀ n, 0 < rho n
  rho_half : ∀ n, rho n ≤ 1 / 2
  acc_radius : ∀ n, (A0 n + radius C K d n) * rho n ≤ c / 2
  chord_nonneg : 0 ≤ dlt
  chord_speed : dlt ≤ c / 2
  chord_margin : ∀ n,
    2 * radius C K d n ≤ (d0 - dlt) * rho n

private theorem dist_acc_apply_le (p q : Data) (u : ℝ) :
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

/-- A tail budget yields exactly the diagonal membership family, with no
claim that `B` preserves every member of a fixed ambient tube. -/
theorem Budget.pullback_mem
    {B : Data → Data} {Q : ℕ → Data} {C K c d0 dlt : ℝ}
    {d : ℕ → ℝ} {A0 rho : ℕ → ℝ}
    (R : Budget B Q C K d c d0 dlt A0 rho) :
    ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k) := by
  intro n k
  let Z := TubePullbackLimit.pullback B Q n k
  let r := radius C K d n
  have hQ := R.model_mem n
  have hZ := R.weak_mem n k
  have hdist : dist (Q n) Z ≤ r := R.marked_tail n k
  have hspeed : ∀ u, c ≤ ‖Z.2.1 u‖ := by
    intro u
    have hv := MarkedSpace.dist_vel_apply_le (Q n) Z u
    have hvR : ‖(Q n).2.1 u - Z.2.1 u‖ ≤ r := hv.trans hdist
    have htri : ‖(Q n).2.1 u‖ ≤
        ‖(Q n).2.1 u - Z.2.1 u‖ + ‖Z.2.1 u‖ := by
      calc
        ‖(Q n).2.1 u‖ = ‖((Q n).2.1 u - Z.2.1 u) + Z.2.1 u‖ := by ring
        _ ≤ ‖(Q n).2.1 u - Z.2.1 u‖ + ‖Z.2.1 u‖ := norm_add_le _ _
    have hQspeed := hQ.speed_lb u
    dsimp [r] at hvR hQspeed ⊢
    linarith
  have hacc : ∀ u, ‖Z.2.2 u‖ ≤ A0 n + r := by
    intro u
    have ha := dist_acc_apply_le Z (Q n) u
    have haR : ‖Z.2.2 u - (Q n).2.2 u‖ ≤ r := by
      exact ha.trans (dist_comm Z (Q n) ▸ hdist)
    calc
      ‖Z.2.2 u‖ = ‖(Z.2.2 u - (Q n).2.2 u) + (Q n).2.2 u‖ := by ring
      _ ≤ ‖Z.2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := norm_add_le _ _
      _ ≤ r + A0 n := add_le_add haR (R.model_acc n u)
      _ = A0 n + r := add_comm _ _
  have hclose : ∀ u, ‖Z.1 u - (Q n).1 u‖ ≤ r := by
    intro u
    exact (MarkedSpace.dist_apply_le Z (Q n) u).trans
      (by simpa [dist_comm] using hdist)
  have hchord := ChordArc.chord_arc_stable_of_acc_bound
    hZ.hasDerivAt_curve hZ.hasDerivAt_vel (MarkedSpace.periodic_vel hZ)
    hZ.periodic hspeed hacc hQ.chord hclose
    (add_nonneg (R.acc_nonneg n) (R.radius_nonneg n))
    (R.rho_pos n) (R.rho_half n) (R.acc_radius n)
    R.chord_nonneg R.chord_speed (R.chord_margin n)
  exact
    { hasDerivAt_curve := hZ.hasDerivAt_curve
      hasDerivAt_vel := hZ.hasDerivAt_vel
      periodic := hZ.periodic
      speed_const := hZ.speed_const
      speed_lb := hspeed
      curv_lb := hZ.curv_lb
      chord := hchord }

end PullbackTubeTailBudget
