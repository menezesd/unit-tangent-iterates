import UnitTangentIterates.GaugeMarkingDefectFrameC2
import UnitTangentIterates.GaugeRearFamilyFundamental
import UnitTangentIterates.EnrichedPhysicalRowConvergence
import UnitTangentIterates.EnrichedPhysicalConstructionCore
import UnitTangentIterates.EnrichedPhysicalHarnackClosureAdapters
import UnitTangentIterates.GaugeFlowMarkedTerminalJets

/-! The exact gauge-marking endpoint modulus and its rowwise convergence. -/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace ConfiguredGaugeEndpointDefect

open MarkingDeviationC2 MarkingFlowDefectC2
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalRowConvergence

/-- Apply the `C²` gauge-marking defect theorem directly to the frame retained
by the long selected-rear construction.  No flow, periodicity, or derivative
bound callback remains at this boundary. -/
theorem dist_le_of_retainedGaugeFrame
    {p q b q' : Data} (Gamma : NormalPath p q)
    {Phi : ℝ → ℝ → ℝ} {Q Q' m : ℝ → ℝ}
    {xi : ℝ → ℝ → ℝ} {kappa kappa2 : ℝ}
    (R : GaugeRearFamilyFundamental.RetainedGaugeFrame
      Phi Q Q' m xi kappa kappa2)
    (hm : Continuous m) (hGammam : Gamma.m = m)
    {Lmax L kb kL cq kminq dltq : ℝ} {Θ k : ℝ → ℝ}
    (hQ0 : 0 < Q 0) (hQmax : ∀ t, Q t ≤ Lmax)
    (hQT : Q Gamma.T = L)
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b)
    (hLb : perim b = L)
    (hev : ∀ s, HasDerivAt (ev b)
      (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s)
    (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hq'1 : ∀ u, q'.1 u = ev b (Phi Gamma.T u))
    (hq'd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) :
    dist q' b ≤ markingC2Bound (2 * Lmax * kappa * Gamma.cost)
      (flowDefectC1Int (Q 0) (kappa * Gamma.cost))
      (flowDefectC2Int (Q 0) (kappa * Gamma.cost)
        (kappa2 * Gamma.cost)) L kb kL := by
  apply GaugeMarkingDefectFrameC2.dist_le_of_frameData_cost
    (Phi := Phi) (Q := Q) (Q' := Q')
    (C := fun t => kappa * m t) (C2 := fun t => kappa2 * m t)
    Gamma R.frame R.period_deriv R.v_periodic R.xi_quasiPeriodic R.flow
    R.initial hQ0 R.xi_zero R.rate1_bound (continuous_const.mul hm)
    R.rate2_bound (continuous_const.mul hm) hQmax
  · intro t
    rw [← hGammam]
  · intro t
    rw [← hGammam]
  · exact hQT
  · exact hcq
  · exact hb
  · exact hLb
  · exact hev
  · exact hΘ
  · exact hkb
  · exact hklip
  · exact hq'1
  · exact hq'd
  · exact hq'v

/-- The ordinary physical endpoint facts retained alongside an actual gauge
terminal.  The flow endpoint itself supplies the marked derivative identities;
this package contains only geometry of its ordinary arclength representative. -/
structure TerminalPhysicalFacts (b : Data) where
  cq : ℝ
  kmin : ℝ
  dlt : ℝ
  L : ℝ
  kb : ℝ
  kL : ℝ
  Theta : ℝ → ℝ
  curvature : ℝ → ℝ
  cq_pos : 0 < cq
  tube : IsTubeMember cq kmin dlt b
  perim_eq : perim b = L
  curve_frenet : ∀ s, HasDerivAt (ev b)
    (Complex.exp (Complex.I * (Theta s : ℂ))) s
  angle_deriv : ∀ s, HasDerivAt Theta (curvature s) s
  curvature_bound : ∀ s, |curvature s| ≤ kb
  curvature_lipschitz : ∀ s t,
    |curvature s - curvature t| ≤ kL * |s - t|

/-- The no-callback terminal application: `TerminalJets` discharges the
terminal curve/velocity derivatives and position equation, while
`TerminalPhysicalFacts` supplies the ordinary physical Frenet data. -/
theorem dist_terminalJets_le_of_retainedGaugeFrame
    {p q b : Data} (Gamma : NormalPath p q)
    {Phi : ℝ → ℝ → ℝ} {Q Q' m : ℝ → ℝ}
    {xi xiX xiXX : ℝ → ℝ → ℝ} {kappa kappa2 ell T : ℝ}
    (R : GaugeRearFamilyFundamental.RetainedGaugeFrame
      Phi Q Q' m xi kappa kappa2)
    (J : GaugeFlowMarkedTerminalJets.TerminalJets
      xi xiX xiXX Phi ell (perim b) T b)
    (B : TerminalPhysicalFacts b)
    (hm : Continuous m) (hGammam : Gamma.m = m)
    (hT : Gamma.T = T) {Lmax : ℝ}
    (hQ0 : 0 < Q 0) (hQmax : ∀ t, Q t ≤ Lmax)
    (hQT : Q Gamma.T = perim b) :
    dist J.rear b ≤
      markingC2Bound (2 * Lmax * kappa * Gamma.cost)
        (flowDefectC1Int (Q 0) (kappa * Gamma.cost))
        (flowDefectC2Int (Q 0) (kappa * Gamma.cost)
          (kappa2 * Gamma.cost)) B.L B.kb B.kL := by
  apply dist_le_of_retainedGaugeFrame Gamma R hm hGammam hQ0 hQmax
    (hQT.trans B.perim_eq)
    B.cq_pos B.tube B.perim_eq B.curve_frenet B.angle_deriv
    B.curvature_bound B.curvature_lipschitz
  · intro u
    rw [hT, J.position]
    simp [ev]
  · exact J.curve_deriv
  · exact J.vel_deriv

/-- The endpoint modulus occurring literally in
`GaugeMarkingDefectFrameC2.dist_le_of_frameData_cost`.  All geometric
constants are row-indexed; only the stage cost depends on the depth. -/
def rho
    (ell Lmax kappa kappa2 L kb kL : ℕ → ℝ)
    (stageCost : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  markingC2Bound
    (2 * Lmax n * kappa n * stageCost n k)
    (flowDefectC1Int (ell n) (kappa n * stageCost n k))
    (flowDefectC2Int (ell n) (kappa n * stageCost n k)
      (kappa2 n * stageCost n k))
    (L n) (kb n) (kL n)

theorem rho_nonneg
    {ell Lmax kappa kappa2 L kb kL : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (hLmax : ∀ n, 0 ≤ Lmax n) (hkappa : ∀ n, 0 ≤ kappa n)
    (hcost : ∀ n k, 0 ≤ stageCost n k) :
    ∀ n k, 0 ≤ rho ell Lmax kappa kappa2 L kb kL stageCost n k := by
  intro n k
  apply markingC2Bound_nonneg
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hLmax n))
    (hkappa n)) (hcost n k)

theorem rho_tendsto_zero
    {ell Lmax kappa kappa2 L kb kL : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (hcost : ∀ n, Tendsto (stageCost n) atTop (nhds 0)) :
    ∀ n, Tendsto (rho ell Lmax kappa kappa2 L kb kL stageCost n)
      atTop (nhds 0) := by
  intro n
  have hk : Tendsto (fun k => kappa n * stageCost n k) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (hcost n) using 1 <;> simp
  have hk2 : Tendsto (fun k => kappa2 n * stageCost n k) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (hcost n) using 1 <;> simp
  have he0 : Tendsto
      (fun k => 2 * Lmax n * kappa n * stageCost n k) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (hcost n) using 1 <;> simp
  have he1 := tendsto_flowDefectC1Int_zero (ell := ell n) hk
  have he2 := tendsto_flowDefectC2Int_zero (ell := ell n) hk hk2
  exact tendsto_markingC2Bound_zero he0 he1 he2

/-- Turn the exact per-stage applications of the gauge marking-defect theorem
into the convergence certificate consumed by retained physical rows. -/
def endpointDefectCertificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (ell Lmax kappa kappa2 L kb kL : ℕ → ℝ)
    (stageCost : ℕ → ℕ → ℝ)
    (hLmax : ∀ n, 0 ≤ Lmax n) (hkappa : ∀ n, 0 ≤ kappa n)
    (hcost0 : ∀ n k, 0 ≤ stageCost n k)
    (hcostlim : ∀ n, Tendsto (stageCost n) atTop (nhds 0))
    (hterminal : ∀ n k,
      dist (F.richStage n k).terminalBase (F.P n (k + 1)) ≤
        rho ell Lmax kappa kappa2 L kb kL stageCost n k) :
    EndpointDefectCertificate F
      (rho ell Lmax kappa kappa2 L kb kL stageCost) where
  rho_nonneg := rho_nonneg hLmax hkappa hcost0
  terminalBase_dist := hterminal
  rho_tendsto_zero := rho_tendsto_zero hcostlim

/-- Provider-level form used before a final `Construction` exists.  The
depth-zero defect is definitionally zero and every successor defect is the
selected stage's terminal-base/endpoint estimate. -/
def coreEndpointDefectCertificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : EnrichedPhysicalChosenRichFamily.GaugeFamily
      Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : EnrichedPhysicalChosenRichFamily.ConstructionCore
      Q e P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate
      a MA NA K0 K1 K2)
    {rho : ℕ → ℕ → ℝ}
    (hrho : ∀ n, Tendsto (rho n) atTop (nhds 0))
    (hterminal : ∀ n k,
      dist ((EnrichedPhysicalChosenRichFamily.chosenColumn
        F.baseProvider F.mapProvider k).step.richStage n).terminalBase
        ((EnrichedPhysicalChosenRichFamily.chosenColumn
          F.baseProvider F.mapProvider k).step.next n) ≤ rho n k) :
    F.EndpointDefectCertificate where
  tendsToZero :=
    EnrichedPhysicalHarnackClosureAdapters.retainedRows_defect_tendsto_zero
      F.baseProvider F.mapProvider hrho hterminal

end ConfiguredGaugeEndpointDefect
