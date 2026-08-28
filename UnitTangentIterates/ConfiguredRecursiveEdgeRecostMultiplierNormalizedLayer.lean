import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedSuccessor
import UnitTangentIterates.ConfiguredRecursiveEdgeGaugeMajorantShift

/-!
# Diagonal normalized-state layer

At depth `k`, row `n` is indexed by the shifted gauge output and scalar
profiles at `n+k`.  Hence the predecessor `(n+1,k)` and successor `(n,k+1)`
have identical indices.
-/

namespace ConfiguredRecursiveEdgeRecostMultiplierNormalizedLayer

open ConfiguredRecursiveEdgeRecostedNormalizedReachableState
open ConfiguredRecursiveEdgeRecostedScaledGeometricStep

structure Layer
    {Q : ℕ → MarkedSpace.Data} {e : ℕ → ℕ → ℝ}
    {P0 P1geom G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ}
    {MA NA Etotal Dtarget : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget)
    (stateP1 defect : ℕ → ℝ)
    (X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1geom G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) where
  normalized : ∀ n,
    State (O.shiftOutput (n + X.depth)) (X.stage n)
      (stateP1 (n + X.depth)) X.depth
      (defect (n + X.depth + 1))

namespace Layer

noncomputable def next
    {Q : ℕ → MarkedSpace.Data} {e : ℕ → ℕ → ℝ}
    {P0 P1geom G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ}
    {MA NA Etotal Dtarget : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}
    {stateP1 defect : ℕ → ℝ}
    {X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1geom G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh}
    (L : Layer O stateP1 defect X)
    (G : StepInput X)
    (hE : Etotal ≤ 1 / 8)
    (hcur : ∀ n,
      (G.scaled n).eps ≤
        (O.shiftOutput (n + 1 + X.depth)).major (X.depth + 1))
    (hupper : ∀ n,
      (G.scaled n).slice.periodUpper ≤ stateP1 (n + 1 + X.depth)) :
    Layer O stateP1 defect G.next := by
  refine { normalized := fun n => ?_ }
  have Hprev := L.normalized (n + 1)
  have Hnext :=
    ConfiguredRecursiveEdgeRecostMultiplierNormalizedSuccessor.nextState
      G n Hprev hE (hcur n) (hupper n)
  convert Hnext using 1 <;>
    simp [ConfiguredRecursiveEdgeRecostedScaledGeometricStep.StepInput.next,
      ConfiguredRecursiveEdgeRecostedGeometricState.State.next,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Layer

end ConfiguredRecursiveEdgeRecostMultiplierNormalizedLayer
