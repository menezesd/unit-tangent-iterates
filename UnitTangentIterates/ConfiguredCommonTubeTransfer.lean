import UnitTangentIterates.ConfiguredGaugeEndpointDefect
import UnitTangentIterates.InductiveLocalPullbackTube

/-!
# Common-tube transfer for retained physical terminals

The inductive tube budget is stated for canonical pullbacks, but its local
argument only uses closeness to the strict model, the structural marked-curve
facts, and nonnegative curvature.  This sibling theorem exposes that argument
for the ordinary physical terminal bases retained by the enriched gauge
construction.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredCommonTubeTransfer

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

/-- Any retained physical terminal within the reserved model radius belongs
to the same fixed tube as a canonical pullback.  The local tube constants in
`TerminalPhysicalFacts` are used only for the closed, constant-speed `C²`
structure; the desired speed and chord constants come from the configured
inductive budget, and convexity is supplied by the corrected physical edge.
-/
theorem mem_of_terminalPhysical_and_dist
    {B : Data → Data} {Q : ℕ → Data} {C K c d0 dlt : ℝ}
    {d : ℕ → ℝ} {A0 rho : ℕ → ℝ}
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      B Q C K d c d0 dlt A0 rho)
    (n : ℕ) {M Z : Data}
    (hmodel : IsTubeMember
      (c + PullbackTubeTailBudget.radius C K d n) 0 d0 M)
    (hmodel_acc : ∀ u, ‖M.2.2 u‖ ≤ A0 n)
    (P : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts Z)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (Z.2.1 u) * Z.2.2 u).im)
    (hdist : dist M Z ≤ PullbackTubeTailBudget.radius C K d n) :
    IsTubeMember c 0 dlt Z := by
  let r := PullbackTubeTailBudget.radius C K d n
  have hQ := hmodel
  have hZ := P.tube
  have hspeed : ∀ u, c ≤ ‖Z.2.1 u‖ := by
    intro u
    have hv := MarkedSpace.dist_vel_apply_le M Z u
    have hvR : ‖M.2.1 u - Z.2.1 u‖ ≤ r := hv.trans hdist
    have htri : ‖M.2.1 u‖ ≤
        ‖M.2.1 u - Z.2.1 u‖ + ‖Z.2.1 u‖ := by
      calc
        ‖M.2.1 u‖ = ‖(M.2.1 u - Z.2.1 u) + Z.2.1 u‖ := by ring
        _ ≤ ‖M.2.1 u - Z.2.1 u‖ + ‖Z.2.1 u‖ := norm_add_le _ _
    have hQspeed := hQ.speed_lb u
    dsimp [r] at hvR hQspeed ⊢
    linarith
  have hacc : ∀ u, ‖Z.2.2 u‖ ≤ A0 n + r := by
    intro u
    have ha := dist_acc_apply_le Z M u
    have haR : ‖Z.2.2 u - M.2.2 u‖ ≤ r := by
      exact ha.trans (dist_comm Z M ▸ hdist)
    calc
      ‖Z.2.2 u‖ = ‖(Z.2.2 u - M.2.2 u) + M.2.2 u‖ := by ring
      _ ≤ ‖Z.2.2 u - M.2.2 u‖ + ‖M.2.2 u‖ := norm_add_le _ _
      _ ≤ r + A0 n := add_le_add haR (hmodel_acc u)
      _ = A0 n + r := add_comm _ _
  have hclose : ∀ u, ‖Z.1 u - M.1 u‖ ≤ r := by
    intro u
    exact (MarkedSpace.dist_apply_le Z M u).trans
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
      curv_lb := by
        intro u
        simpa using hcurv u
      chord := hchord }

end ConfiguredCommonTubeTransfer
