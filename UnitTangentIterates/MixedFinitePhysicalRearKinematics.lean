import UnitTangentIterates.PhysicalRearLimitHarnackAdapter
import UnitTangentIterates.GaugeRearFamilyVariableTerminal

/-!
# Mixed finite physical-rear kinematics

Rich recursive stages retain an ordinary physical rear representative while
their front is the actual variable-marked endpoint in the preceding column.
The two arrays must not be identified: their marked perimeters need not agree.
This module proves the limit Harnack closure directly from those mixed edges.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace PathMetric

/-- Physical rear kinematics whose rear lies in the retained ordinary array
`B`, while its front is the actual variable-marked array `P`. -/
structure MixedFinitePhysicalRearKinematics
    (kh : ℝ) (B P : ℕ → ℕ → Data) : Prop where
  stage : ∀ n k, Nonempty
    (PhysicalRearLimitKinematics kh (B n (k + 1)) (P (n + 1) k))

/-- Mixed finite stages supply differentiable Harnack strictness on every
limit of the retained physical rear rows.  Front and rear tube constants are
independent; only positivity of their respective speed floors is used. -/
def limitStrictnessDataH_of_mixedFinitePhysicalRearKinematics
    {kh cb db cp dp : ℝ} {B P : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hcp : 0 < cp)
    (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (hPtube : ∀ n k, IsTubeMember cp 0 dp (P n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B P)
    (X : ℕ → Data) (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (n : ℕ) : UnconditionalAssembly.LimitStrictnessDataH (X n) := by
  have hXmem : IsTubeMember cb 0 db (X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hX n)
      (Eventually.of_forall (hBtube n))
  have hXshift : Tendsto (fun k => B n (k + 1)) atTop (nhds (X n)) :=
    (hX n).comp (tendsto_add_atTop_nat 1)
  apply UnconditionalAssembly.limitStrictnessDataH_of_limit'
    (P := fun k => B n (k + 1)) hcb hXmem hXshift
  intro k a b hab
  let K := Nonempty.some (mixed.stage n k)
  let S := K.toStageComponents hkh0 hkh1 hcp (hPtube (n + 1) k)
  let D := S.limitStrictness hcp (hPtube (n + 1) k)
  let DH := D.toH (fun s => (D.curvature_deriv s).differentiableAt)
  have hcurv : ∀ s, D.k s =
      UnconditionalAssembly.arcCurv (B n (k + 1)) s :=
    RearTrackEmbedded.curvature_eq_arcCurv hcb (hBtube n (k + 1))
      D.curve_deriv D.angle_deriv
  have hH := DH.curvature_harnack a b hab
  change Real.exp (a - b) * (D.k a / Real.sqrt (1 + D.k a ^ 2)) ≤
    D.k b / Real.sqrt (1 + D.k b ^ 2) at hH
  simpa only [hcurv a, hcurv b] using hH

end PathMetric

namespace GaugeRearFamilyVariableTerminal

open PathMetric VariableMarkedTube

/-- The mixed physical package discharges the rich family's Harnack-closure
callback after marking compactness identifies a variable row limit as a
surjective oriented reparametrization of its retained physical-row limit. -/
def harnackClosed_of_mixedFinitePhysicalRearLimit
    {kh cb db cp dp : ℝ} {B P : ℕ → ℕ → Data} {X : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (hPtube : ∀ n k, IsTubeMember cp 0 dp (P n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B P)
    (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (limitReparam : ∀ n x, Tendsto (P n) atTop (nhds x) →
      LimitOrientedReparametrization (X n) x) :
    ∀ n x, Tendsto (P n) atTop (nhds x) →
      (∀ k, ArclengthHarnackCertificate (P n k)) →
      ArclengthHarnackCertificate x := by
  intro n x hx _
  let W := limitReparam n x hx
  have hbase : IsTubeMember cb 0 db (X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hX n)
      (Eventually.of_forall (hBtube n))
  exact arclengthHarnack_of_orientedReparametrization hcb hdb hbase
    W.reparametrization W.surjective
    (limitStrictnessDataH_of_mixedFinitePhysicalRearKinematics
      hkh0 hkh1 hcb hcp hBtube hPtube mixed X hX n)

/-- Mixed physical rear limits also give the stronger oriented ordinary
representative needed by the paper-facing unit-tangent orbit. -/
def orientedRepresentativeClosed_of_mixedFinitePhysicalRearLimit
    {kh cb db cp dp : ℝ} {B P : ℕ → ℕ → Data} {X : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (hPtube : ∀ n k, IsTubeMember cp 0 dp (P n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B P)
    (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (limitReparam : ∀ n x, Tendsto (P n) atTop (nhds x) →
      LimitOrientedReparametrization (X n) x) :
    ∀ n x, Tendsto (P n) atTop (nhds x) →
      OrientedArclengthRepresentative x := by
  intro n x hx
  let W := limitReparam n x hx
  have hbase : IsTubeMember cb 0 db (X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hX n)
      (Eventually.of_forall (hBtube n))
  exact orientedArclengthRepresentative_of_orientedReparametrization
    hcb hdb W.lambda_pos hbase W.reparametrization W.psi_hasDerivAt
    W.dpsi_continuous W.surjective
    (limitStrictnessDataH_of_mixedFinitePhysicalRearKinematics
      hkh0 hkh1 hcb hcp hBtube hPtube mixed X hX n)

end GaugeRearFamilyVariableTerminal
