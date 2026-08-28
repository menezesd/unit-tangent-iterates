import UnitTangentIterates.VariableSpeedApproximatePullback

/-! # Approximate pullbacks from closed-tube invariance

This adapter removes the pointwise pullback-membership callback from the
approximate variable-speed limit theorem.  Membership of every finite
pullback is instead derived from the paper-facing closed-tube residual.
-/

noncomputable section

open Function Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace PaperFaithfulApproximatePullback

/-- Approximate variable-speed transport in the closed nonnegative-curvature
tube.  The residual's model-membership and one-step preservation fields imply
the complete pullback-membership family internally. -/
theorem exists_markedLimit_of_approx_variableSpeed_transport_closedTube
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c dlt : ℝ}
    (hK : 0 ≤ K)
    (hweighted : ∀ n, Summable fun k => K ^ k * d (n + k))
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma →
      ∀ eps : ℝ, 0 < eps → ∃ Delta : NormalPath (B p) (B q),
        cost Delta ≤ K * cost Gamma + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eps : ℝ, 0 < eps →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ d n + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Lambda)
    (hC : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (residual :
      UnconditionalAssembly.PaperFaithfulAssemblyRemainder.ClosedTubeInvarianceResidual
        B Q c dlt)
    (hBcont : Continuous B) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (nhds (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail
        (fun k => c2ConstVar P0 P1 khat G1 Cg *
          (K ^ k * d (n + k))) 0) := by
  exact exists_markedLimit_of_approx_variableSpeed_transport
    hK hweighted hmap hdefect hC
    (UnconditionalAssembly.PaperFaithfulAssemblyRemainder.pullback_mem_closedTube
      residual)
    hBcont

end PaperFaithfulApproximatePullback
