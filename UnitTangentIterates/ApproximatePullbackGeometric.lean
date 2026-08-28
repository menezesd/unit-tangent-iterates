import UnitTangentIterates.ApproximatePullbackClosedTube
import UnitTangentIterates.WeightedRecursiveDefect

/-!
# Geometric approximate pullback assembly

This is the paper-facing form of the approximate variable-speed shadowing
argument.  Exponential model defects are allowed to be amplified by `K` at
each selected-rear pullback; the sharp condition is `K * q < 1`.
-/

noncomputable section

open Function Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace PaperFaithfulApproximatePullback

/-- Geometrically decaying approximate model defects produce a simultaneous
exact inverse orbit in the closed tube.  No minimizing normal path and no
nonexpansiveness assumption `K <= 1` are used. -/
theorem exists_markedLimit_of_approx_variableSpeed_transport_geometric
    {B : Data -> Data} {Q : Nat -> Data} {d : Nat -> Real}
    {K D q P0 P1 khat G1 Cg c dlt : Real}
    (hK : 0 <= K) (hD : 0 <= D) (hq : 0 <= q) (hKq : K * q < 1)
    (hd : forall n, 0 <= d n) (hdgeo : forall n, d n <= D * q ^ n)
    (hmap : forall (p r : Data) (Gamma : NormalPath p r),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma ->
      forall eps : Real, 0 < eps -> exists Delta : NormalPath (B p) (B r),
        cost Delta <= K * cost Gamma + eps /\
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta)
    (hdefect : forall n : Nat, forall eps : Real, 0 < eps ->
      exists Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda <= d n + eps /\
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Lambda)
    (hC : 0 <= c2ConstVar P0 P1 khat G1 Cg)
    (residual :
      UnconditionalAssembly.PaperFaithfulAssemblyRemainder.ClosedTubeInvarianceResidual
        B Q c dlt)
    (hBcont : Continuous B) :
    exists X : Nat -> Data,
      (forall n, IsTubeMember c 0 dlt (X n)) /\
      (forall n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (nhds (X n))) /\
      (forall n, X n = B (X (n + 1))) /\
      (forall n, dist (Q n) (X n) <= ShadowingTails.tail
        (fun k => c2ConstVar P0 P1 khat G1 Cg *
          (K ^ k * d (n + k))) 0) := by
  exact exists_markedLimit_of_approx_variableSpeed_transport_closedTube
    hK
    (PathMetric.WeightedRecursiveDefect.summable_pullbackError_of_geometric
      hK hD hq hKq hd hdgeo)
    hmap hdefect hC residual hBcont

end PaperFaithfulApproximatePullback
