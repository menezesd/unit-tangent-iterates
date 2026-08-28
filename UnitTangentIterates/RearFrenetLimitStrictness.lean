import Mathlib
import UnitTangentIterates.PhysicalSelectedRearStrictnessAdapter
import UnitTangentIterates.UnconditionalAssemblyRemainder

noncomputable section

open Filter Function Set Topology

namespace PhysicalSelectedRearStrictnessAdapter

/-- The exact differential certificate missing from the physical selected-rear
adapter.  Unlike bare `ContDiff 3`, it identifies the supplied scalar `k` with
the curvature of the reconstructed marked rear. -/
structure RearFrenetCertificate (q : MarkedSpace.Data) where
  psi : ℝ → ℝ
  k : ℝ → ℝ
  k' : ℝ → ℝ
  curve_deriv : ∀ s, HasDerivAt (MarkedSpace.ev q)
    (Complex.exp (Complex.I * (psi s : ℂ))) s
  angle_deriv : ∀ s, HasDerivAt psi (k s) s
  curvature_deriv : ∀ s, HasDerivAt k (k' s) s
  curvature_periodic : Periodic k (MarkedSpace.perim q)
  curvature_nonnegative : ∀ s, 0 ≤ k s
  next_nonnegative : ∀ s,
    0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2)
  curvature_nonzero : ∃ s, k s ≠ 0

/-- A rear Frenet certificate is exactly the strictness datum consumed by the
nonnegative-tube capstone. -/
def RearFrenetCertificate.toLimitStrictnessData
    {q : MarkedSpace.Data} (F : RearFrenetCertificate q) :
    UnconditionalAssembly.LimitStrictnessData q where
  theta := F.psi
  k := F.k
  k' := F.k'
  curve_deriv := F.curve_deriv
  angle_deriv := F.angle_deriv
  curvature_deriv := F.curvature_deriv
  curvature_periodic := F.curvature_periodic
  curvature_nonnegative := F.curvature_nonnegative
  next_nonnegative := F.next_nonnegative
  curvature_nonzero := F.curvature_nonzero

/-- Strengthened physical closure output: canonical selected-rear
identification and regularity are retained together with the Frenet identities
needed to identify its actual curvature. -/
structure PhysicalLimitStrictnessDataWithFrenet
    (kap : ℝ) (p q : MarkedSpace.Data) (P : ℝ)
    (d : NormalizedSelectedRearClosure.SteeringData kap)
    (theta0 : ℝ) where
  physical : ∃ k k', PhysicalLimitStrictnessData kap p q P d theta0 k k'
  frenet : RearFrenetCertificate q

/-- Direct sound package from the strengthened physical output. -/
def PhysicalLimitStrictnessDataWithFrenet.toLimitStrictnessData
    {kap P theta0 : ℝ} {p q : MarkedSpace.Data}
    {d : NormalizedSelectedRearClosure.SteeringData kap}
    (F : PhysicalLimitStrictnessDataWithFrenet kap p q P d theta0) :
    UnconditionalAssembly.LimitStrictnessData q :=
  F.frenet.toLimitStrictnessData

/-- Sequence-level Frenet closure data for controlled-junction limits. -/
structure RearFrenetLimitFamily (Q : ℕ → ℕ → MarkedSpace.Data) where
  frenet : ∀ (X : ℕ → MarkedSpace.Data),
    (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
    ∀ n, RearFrenetCertificate (X n)

/-- Produce the exact strictness callback of
`GaugeControlledClosingInputsNonnegative`. -/
def RearFrenetLimitFamily.limitStrictness
    {Q : ℕ → ℕ → MarkedSpace.Data} (F : RearFrenetLimitFamily Q) :
    ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, UnconditionalAssembly.LimitStrictnessData (X n) := by
  intro X hX n
  exact (F.frenet X hX n).toLimitStrictnessData

end PhysicalSelectedRearStrictnessAdapter
