import UnitTangentIterates.GaugeFlowMarkedData
import UnitTangentIterates.GaugeRearEndpointCurvature

/-!
# Public spatial jets of a gauge-flow terminal marking

`GaugeFlowMarkedData.exists_data_of_flow_marking` constructs the correct
marked endpoint but historically erased the first two spatial flow jets.
This sibling result retains them for that same endpoint.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace

namespace GaugeFlowMarkedTerminalJets

open FlowDerivative GaugeFlowDerivCost GaugeFlowTimeDerivative
  FlowJointContinuity GaugeRearEndpointCurvature RearOwnArclength

/-- The actual marked endpoint together with the unscaled first and second
spatial derivatives of its terminal flow marking. -/
structure TerminalJets
    (xi xiX xiXX Phi : ℝ → ℝ → ℝ) (ell L t0 : ℝ) (b : Data) where
  rear : Data
  flow1 : ℝ → ℝ
  flow2 : ℝ → ℝ
  flow1_eq : ∀ u, flow1 u =
    flowDeriv (fun a y => -xiX a y) Phi ell t0 u
  flow2_eq : ∀ u, flow2 u =
    flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y)
      Phi ell t0 u
  position : ∀ u, rear.1 u = b.1 (Phi t0 u / L)
  curve_deriv : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u
  vel_deriv : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u
  flow_deriv : ∀ u, HasDerivAt (fun v => Phi t0 v) (flow1 u) u
  flow1_deriv : ∀ u, HasDerivAt flow1 (flow2 u) u
  flow1_pos : ∀ u, 0 < flow1 u
  flow2_cont : Continuous flow2

/-- Strong sibling of `GaugeFlowMarkedData.exists_data_of_flow_marking` which
retains the terminal spatial jets. -/
theorem exists_terminalJets
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {m : ℝ → ℝ}
    {ell kappa kappa2 T L t0 : ℝ} {b : Data}
    (hT : 0 < T) (hell : 0 < ell) (hL : 0 < L)
    (hxiC : Continuous (uncurry xi))
    (hxiXd : ∀ s x, HasDerivAt (xi s) (xiX s x) x)
    (hxiXc : Continuous (uncurry xiX))
    (hxiXXd : ∀ s x, HasDerivAt (xiX s) (xiXX s x) x)
    (hxiXXc : Continuous (uncurry xiXX))
    (hC : ∀ t x, |xiX t x| ≤ kappa * m t)
    (hC2 : ∀ t x, |xiXX t x| ≤ kappa2 * m t)
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t)
    (hb1 : ∀ u, HasDerivAt (⇑b.1) (b.2.1 u) u)
    (hb2 : ∀ u, HasDerivAt (⇑b.2.1) (b.2.2 u) u) :
    Nonempty (TerminalJets xi xiX xiXX Phi ell L t0 b) := by
  obtain ⟨rear, hposition, hcurve, hvel⟩ :=
    GaugeFlowMarkedData.exists_data_of_flow_marking hT hell hL hxiC
      hxiXd hxiXc hxiXXd hxiXXc hC hC2 hkappa hkappa2 hmc hm0 hmstop
      hPhi0 hPhid hb1 hb2
  obtain ⟨B, hBnn, hB⟩ := GaugeFlowDerivCost.exists_bound_of_stop
    hmc hm0 hmstop hT
  have hxdneg : ∀ s x, HasDerivAt ((fun a y => -xi a y) s)
      ((fun a y => -xiX a y) s x) x := fun s x => (hxiXd s x).neg
  have hxxdneg : ∀ s x, HasDerivAt ((fun a y => -xiX a y) s)
      ((fun a y => -xiXX a y) s x) x := fun s x => (hxiXXd s x).neg
  have hbd1 : ∀ s x, |(fun a y => -xiX a y) s x| ≤ kappa * B := by
    intro s x
    simp only [abs_neg]
    exact (hC s x).trans (mul_le_mul_of_nonneg_left (hB s) hkappa)
  have hbd2 : ∀ s x, |(fun a y => -xiXX a y) s x| ≤ kappa2 * B := by
    intro s x
    simp only [abs_neg]
    exact (hC2 s x).trans (mul_le_mul_of_nonneg_left (hB s) hkappa2)
  have hlip : ∀ t, LipschitzWith (Real.toNNReal (kappa * B))
      ((fun a y => -xi a y) t) :=
    fun t => lipschitzWith_of_deriv_bound (mul_nonneg hkappa hBnn) hxdneg hbd1 t
  have hcont : Continuous (uncurry fun a y => -xi a y) := by
    simpa [Function.uncurry] using hxiC.neg
  have hxcont : Continuous (uncurry fun a y => -xiX a y) := by
    simpa [Function.uncurry] using hxiXc.neg
  have hxxcont : Continuous (uncurry fun a y => -xiXX a y) := by
    simpa [Function.uncurry] using hxiXXc.neg
  have hPhid' : ∀ u t, HasDerivAt (fun r => Phi r u)
      ((fun a y => -xi a y) t (Phi t u)) t := hPhid
  let flow1 : ℝ → ℝ := fun u =>
    flowDeriv (fun a y => -xiX a y) Phi ell t0 u
  let flow2 : ℝ → ℝ := fun u =>
    flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y)
      Phi ell t0 u
  have hflow1 : ∀ u, HasDerivAt (fun v => Phi t0 v) (flow1 u) u :=
    fun u => hasDerivAt_flow_initial hlip hcont hPhid' hell hPhi0 hxdneg u t0
  have hflow2 : ∀ u, HasDerivAt flow1 (flow2 u) u :=
    fun u => hasDerivAt_flowDeriv hlip hcont hPhid' hell hPhi0 hxdneg
      hxcont hxxdneg hxxcont hbd2 u t0
  have hflowpos : ∀ u, 0 < flow1 u :=
    fun u => flowDeriv_pos hell t0 u
  have hflow2cont : Continuous flow2 :=
    continuous_flowDeriv2_initial hlip hPhid' hPhi0 hxcont hxxcont t0
  exact ⟨{
    rear := rear
    flow1 := flow1
    flow2 := flow2
    flow1_eq := fun _ => rfl
    flow2_eq := fun _ => rfl
    position := hposition
    curve_deriv := hcurve
    vel_deriv := hvel
    flow_deriv := hflow1
    flow1_deriv := hflow2
    flow1_pos := hflowpos
    flow2_cont := hflow2cont }⟩

/-- Apply the selected-rear sign theorem directly to the exact endpoint and
terminal flow retained by `TerminalJets`. -/
theorem rear_orientedCurvature_nonnegative
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L t0 : ℝ} {b : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L t0 b)
    {F : ℝ → ℝ → ℂ} {Θ delta K sf : ℝ → ℝ → ℝ}
    {T kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ s, 0 ≤ delta T s)
    (hstrip1 : ∀ s, delta T s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0)
    (ht0 : t0 = T)
    (hterminal : ∀ u, J.rear.1 u = rearOwn F Θ delta sf T (Phi T u)) :
    ∀ u, 0 ≤
      ((starRingEnd ℂ) (J.rear.2.1 u) * J.rear.2.2 u).im := by
  subst t0
  exact rearOwn_terminal_orientedCurvature_nonnegative hkh0 hkh1 hstrip0
    hstrip1 hF hΘ hsteer hsf hcos hterminal J.curve_deriv J.vel_deriv
    J.flow_deriv J.flow1_deriv (fun u => (J.flow1_pos u).le)

end GaugeFlowMarkedTerminalJets
