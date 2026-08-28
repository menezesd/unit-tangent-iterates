import Mathlib
import UnitTangentIterates.MarkedDataOfMarking
import UnitTangentIterates.GaugeFlowDerivCost
import UnitTangentIterates.FlowJointContinuity

/-!
# The comparison curve of a gauge marking is an element of the marked space

The `C²` comparison estimates of the selected inverse are stated for *some*
datum `q'` of the marked space whose position reads a member `b` of the tube in
the gauge marking `Φ` of the path, that is, with

`q'(u) = b(Φ(T,u)/L)` ,  `L = perim b` .

This file produces such a datum, so that the estimates become unconditional.

The marking is the flow of `−ξ` started at the affine marking of length `ℓ`, so
`GaugeFlowDerivCost.lean` bounds its two derivatives in the parameter by
`costP1` and `costG1`, and `FlowJointContinuity.lean` gives their continuity in
the parameter.  The reparametrization `ψ = Φ(T,·)/L` is therefore a `C²`
marking with continuous bounded derivatives, and
`MarkedDataOfMarking.exists_data_of_marking` turns it into an element of
`MarkedSpace.Data`.

Main result: `exists_data_of_flow_marking`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace

namespace GaugeFlowMarkedData

open FlowDerivative GaugeFlowDerivCost GaugeFlowTimeDerivative FlowJointContinuity

/-- **The comparison datum of a gauge marking.**  If `Φ` is the flow of `−ξ`
started at the affine marking of length `ℓ`, and the two arclength derivatives
of `ξ` are dominated by `κ·m` and `κ₂·m` for a cost density `m` supported in the
time window, then for every member `b` of the marked space and every `L > 0` the
reparametrized curve `u ↦ b(Φ(t₀,u)/L)` is again an element of the marked
space, together with its first two derivatives. -/
theorem exists_data_of_flow_marking
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {m : ℝ → ℝ} {ell kappa kappa2 T L t0 : ℝ} {b : Data}
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
    ∃ q' : Data, (∀ u, q'.1 u = b.1 (Phi t0 u / L)) ∧
      (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) ∧
      (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) := by
  -- the cost density is bounded, so the field is globally Lipschitz
  obtain ⟨B, hBnn, hB⟩ := exists_bound_of_stop hmc hm0 hmstop hT
  have hxdneg : ∀ s x, HasDerivAt ((fun a y => -xi a y) s) ((fun a y => -xiX a y) s x) x :=
    fun s x => (hxiXd s x).neg
  have hxxdneg : ∀ s x,
      HasDerivAt ((fun a y => -xiX a y) s) ((fun a y => -xiXX a y) s x) x :=
    fun s x => (hxiXXd s x).neg
  have hbd1 : ∀ s x, |(fun a y => -xiX a y) s x| ≤ kappa * B := by
    intro s x
    simp only [abs_neg]
    exact (hC s x).trans (mul_le_mul_of_nonneg_left (hB s) hkappa)
  have hbd2 : ∀ s x, |(fun a y => -xiXX a y) s x| ≤ kappa2 * B := by
    intro s x
    simp only [abs_neg]
    exact (hC2 s x).trans (mul_le_mul_of_nonneg_left (hB s) hkappa2)
  have hlip : ∀ t, LipschitzWith (Real.toNNReal (kappa * B)) ((fun a y => -xi a y) t) :=
    fun t => lipschitzWith_of_deriv_bound (mul_nonneg hkappa hBnn) hxdneg hbd1 t
  have hcont : Continuous (uncurry fun a y => -xi a y) := by
    simpa [Function.uncurry] using hxiC.neg
  have hxcont : Continuous (uncurry fun a y => -xiX a y) := by
    simpa [Function.uncurry] using hxiXc.neg
  have hxxcont : Continuous (uncurry fun a y => -xiXX a y) := by
    simpa [Function.uncurry] using hxiXXc.neg
  have hPhid' : ∀ u t,
      HasDerivAt (fun r => Phi r u) ((fun a y => -xi a y) t (Phi t u)) t := hPhid
  -- the two derivatives of the marking in the parameter
  have hphi1 : ∀ u, HasDerivAt (fun u' => Phi t0 u')
      (flowDeriv (fun a y => -xiX a y) Phi ell t0 u) u :=
    fun u => hasDerivAt_flow_initial hlip hcont hPhid' hell hPhi0 hxdneg u t0
  have hphi2 : ∀ u, HasDerivAt (fun u' => flowDeriv (fun a y => -xiX a y) Phi ell t0 u')
      (flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t0 u) u :=
    fun u => hasDerivAt_flowDeriv hlip hcont hPhid' hell hPhi0 hxdneg hxcont hxxdneg
      hxxcont hbd2 u t0
  -- their continuity in the parameter
  have hc1 : Continuous fun u => flowDeriv (fun a y => -xiX a y) Phi ell t0 u :=
    continuous_flowDeriv_initial hlip hPhid' hPhi0 hxcont t0
  have hc2 : Continuous fun u =>
      flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t0 u :=
    continuous_flowDeriv2_initial hlip hPhid' hPhi0 hxcont hxxcont t0
  -- and their bounds, as functions of the cost
  have hCstop : ∀ s ∉ Ioo (0 : ℝ) T, kappa * m s = 0 := by
    intro s hs; rw [hmstop s hs, mul_zero]
  have hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, kappa2 * m s = 0 := by
    intro s hs; rw [hmstop s hs, mul_zero]
  have hP1 : ∀ u, |flowDeriv (fun a y => -xiX a y) Phi ell t0 u|
      ≤ costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) := by
    intro u
    rw [abs_of_pos (flowDeriv_pos hell t0 u)]
    exact flowDeriv_le_costP1 (h := fun a y => -xi a y) (C := fun a => kappa * m a) hPhid'
      hxcont hell (fun a x => by simpa only [abs_neg] using hC a x)
      (continuous_const.mul hmc) hCstop hmc (fun _ => le_rfl) hT t0 u
  have hG1 : ∀ u,
      |flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t0 u|
        ≤ costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s) := fun u =>
    abs_flowDeriv2_le_costG1 (h := fun a y => -xi a y) (C := fun a => kappa * m a)
      (C2 := fun a => kappa2 * m a) hPhid' hxcont hxxcont hell
      (fun a x => by simpa only [abs_neg] using hC a x)
      (continuous_const.mul hmc) hCstop (fun a x => by simpa only [abs_neg] using hC2 a x)
      (continuous_const.mul hmc) hC2stop hmc (fun _ => le_rfl) (fun _ => le_rfl) hT t0 u
  -- the marking, rescaled by the perimeter
  obtain ⟨q', hq'0, -, -, hq'1, hq'2⟩ :=
    MarkedDataOfMarking.exists_data_of_marking (b := b)
      (psi := fun u => Phi t0 u / L)
      (psi1 := fun u => flowDeriv (fun a y => -xiX a y) Phi ell t0 u / L)
      (psi2 := fun u =>
        flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t0 u / L)
      (A1 := costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) / L)
      (A2 := costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s) / L)
      hb1 hb2 (fun u => (hphi1 u).div_const L) (fun u => (hphi2 u).div_const L)
      (hc1.div_const L) (hc2.div_const L)
      (fun u => by
        rw [abs_div, abs_of_pos hL]
        gcongr
        exact hP1 u)
      (fun u => by
        rw [abs_div, abs_of_pos hL]
        gcongr
        exact hG1 u)
  exact ⟨q', hq'0, hq'1, hq'2⟩

end GaugeFlowMarkedData
