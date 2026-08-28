import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.RearTrackEmbeddedFloorFree
import UnitTangentIterates.TubeHarnackStrictness

/-!
# Harnack strictness of physical rear limits

Finite physical selected-rear stages have the differentiable strictness
package furnished by their rear Frenet chain.  Its integrated Harnack form is
closed under marked convergence, so the limiting row needs no limiting
curvature derivative and no closure theorem for the auxiliary steering data.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace PathMetric

/-- Physical kinematics on the actual pullback edge
`Q n (k+1) = selInv (Q (n+1) k)`.  The two endpoints lie on diagonally
adjacent rows, rather than at the same pullback depth. -/
structure FinitePullbackPhysicalRearKinematics
    (kh : ℝ) (Q : ℕ → ℕ → Data) : Prop where
  stage : ∀ n k, Nonempty
    (PhysicalRearLimitKinematics kh (Q n (k + 1)) (Q (n + 1) k))

/-- Aligned finite pullback kinematics supply `LimitStrictnessDataH` at every
marked row limit.  The rear row is shifted by one pullback depth.  The
differential finite-stage certificate is used only to obtain its integrated
Harnack inequality; the limit package is reconstructed from closed-tube
membership and pointwise convergence of intrinsic curvature. -/
def limitStrictnessDataH_of_finitePullbackPhysicalRearKinematics
    {kh c dlt : ℝ} {Q : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (finite : FinitePullbackPhysicalRearKinematics kh Q)
    (X : ℕ → Data) (hX : ∀ n, Tendsto (Q n) atTop (nhds (X n)))
    (n : ℕ) : UnconditionalAssembly.LimitStrictnessDataH (X n) := by
  have hXmem : IsTubeMember c 0 dlt (X n) :=
    (isClosed_tube c 0 dlt).mem_of_tendsto (hX n)
      (Eventually.of_forall (htube n))
  have hXshift : Tendsto (fun k => Q n (k + 1)) atTop (nhds (X n)) :=
    (hX n).comp (tendsto_add_atTop_nat 1)
  apply UnconditionalAssembly.limitStrictnessDataH_of_limit'
    (P := fun k => Q n (k + 1)) hc hXmem hXshift
  intro k a b hab
  let K := Nonempty.some (finite.stage n k)
  let S := K.toStageComponents hkh0 hkh1 hc (htube (n + 1) k)
  let D := S.limitStrictness hc (htube (n + 1) k)
  let DH := D.toH (fun s => (D.curvature_deriv s).differentiableAt)
  have hcurv : ∀ s, D.k s =
      UnconditionalAssembly.arcCurv (Q n (k + 1)) s :=
    RearTrackEmbedded.curvature_eq_arcCurv hc (htube n (k + 1))
      D.curve_deriv D.angle_deriv
  have hH := DH.curvature_harnack a b hab
  change Real.exp (a - b) * (D.k a / Real.sqrt (1 + D.k a ^ 2)) ≤
    D.k b / Real.sqrt (1 + D.k b ^ 2) at hH
  simpa only [hcurv a, hcurv b] using hH

/-- `Nonempty` callback form used by closing interfaces which treat limit
strictness as supplied geometric data. -/
def nonempty_limitStrictnessDataH_of_finitePullbackPhysicalRearKinematics
    {kh c dlt : ℝ} {Q : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (finite : FinitePullbackPhysicalRearKinematics kh Q) :
    ∀ (X : ℕ → Data), (∀ n, Tendsto (Q n) atTop (nhds (X n))) →
      ∀ n, Nonempty (UnconditionalAssembly.LimitStrictnessDataH (X n)) := by
  intro X hX n
  exact ⟨limitStrictnessDataH_of_finitePullbackPhysicalRearKinematics
    hkh0 hkh1 hc htube finite X hX n⟩

/-- Direct oval conclusion for every simultaneous marked row limit of an
aligned finite physical pullback family. -/
theorem isOval_ev_of_finitePullbackPhysicalRearKinematics
    {kh c dlt : ℝ} {Q : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c) (hdlt : 0 < dlt)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (finite : FinitePullbackPhysicalRearKinematics kh Q)
    (X : ℕ → Data) (hX : ∀ n, Tendsto (Q n) atTop (nhds (X n)))
    (n : ℕ) : MainTheoremConditional.IsOval (ev (X n)) := by
  have hXmem : IsTubeMember c 0 dlt (X n) :=
    (isClosed_tube c 0 dlt).mem_of_tendsto (hX n)
      (Eventually.of_forall (htube n))
  exact UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH hc hdlt hXmem
    (limitStrictnessDataH_of_finitePullbackPhysicalRearKinematics
      hkh0 hkh1 hc htube finite X hX n)

end PathMetric
