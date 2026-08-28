import Mathlib
import UnitTangentIterates.GaugeSupDensities
import UnitTangentIterates.GaugeFlowDerivCost

/-!
# The sup densities of a family solving the inverse Jacobi ODE, in its gauge
marking

The path metric asks the cost density `m` of a normal path to dominate, at every
time, the three sup norms of its normal velocity *in the parameter of the path*
(`PathMetric.NormalPath.le_m_sup`).  For the family of selected rears that
parameter is the gauge marking `Φ`, the flow of minus the tangential component
`ξ` of the motion, and the normal velocity `η` solves the inverse Jacobi ODE
`∂ₓη = g − η`.

This file combines the two.  The flow derivatives of the marking are bounded by
the constants of `GaugeFlowDerivCost.lean`,

`0 < ∂_uΦ ≤ costP1 ℓ κ M` ,  `|∂²_uΦ| ≤ costG1 ℓ κ κ₂ M` ,

as soon as the two arclength derivatives of the field are dominated by `κ·m` and
`κ₂·m`; the ODE gives `|∂ₓη| ≤ 2S₀` and `|∂²ₓη| ≤ D + 2S₀` from sup bounds `S₀`
for `η` and for `g` and `D` for `∂ₓg`; and the chain rule of
`GaugeSupDensities.lean` turns the two into the three sup norms.  What is asked
of the cost density is therefore

`S₀ ≤ m` ,  `2S₀·costP1 ≤ m` ,  `(D + 2S₀)·costP1² + 2S₀·costG1 ≤ m` ,

three conditions in which the marking no longer appears.

Main result: `supNorm_le_of_flow_jacobi`.
-/

noncomputable section

open Set Function MarkedTopology MeasureTheory

namespace GaugeFlowSupJacobi

open FlowDerivative GaugeFlowDerivCost GaugeFlowTimeDerivative GaugeSupDensities

/-- **The three sup densities of the normal rate of a family read in its gauge
marking.**  The marking is the flow of `−ξ` started at the affine marking of
length `ℓ`; the normal rate solves the inverse Jacobi ODE. -/
theorem supNorm_le_of_flow_jacobi
    {xi xiX xiXX eta g gS Phi : ℝ → ℝ → ℝ} {m S0 Dd : ℝ → ℝ}
    {ell kappa kappa2 T : ℝ}
    (hT : 0 < T) (hell : 0 < ell)
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
    (hjac : ∀ t x, HasDerivAt (eta t) (g t x - eta t x) x)
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hetabd : ∀ t x, |eta t x| ≤ S0 t) (hgbd : ∀ t x, |g t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t)
    (hd0 : ∀ t, S0 t ≤ m t)
    (hd1 : ∀ t, 2 * S0 t * costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) ≤ m t)
    (hd2 : ∀ t, (Dd t + 2 * S0 t) * costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) ^ 2
      + 2 * S0 t * costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s) ≤ m t) :
    ∀ t, ∀ j ≤ 2, supNorm (iteratedDeriv j (fun u => eta t (Phi t u))) ≤ m t := by
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
  have hphi1 : ∀ t u, HasDerivAt (fun u' => Phi t u')
      (flowDeriv (fun a y => -xiX a y) Phi ell t u) u :=
    fun t u => hasDerivAt_flow_initial hlip hcont hPhid' hell hPhi0 hxdneg u t
  have hphi2 : ∀ t u, HasDerivAt (fun u' => flowDeriv (fun a y => -xiX a y) Phi ell t u')
      (flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t u) u :=
    fun t u => hasDerivAt_flowDeriv hlip hcont hPhid' hell hPhi0 hxdneg hxcont hxxdneg
      hxxcont hbd2 u t
  -- and their bounds, as functions of the cost
  have hCstop : ∀ s ∉ Ioo (0 : ℝ) T, kappa * m s = 0 := by
    intro s hs; rw [hmstop s hs, mul_zero]
  have hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, kappa2 * m s = 0 := by
    intro s hs; rw [hmstop s hs, mul_zero]
  have hP1 : ∀ t u, |flowDeriv (fun a y => -xiX a y) Phi ell t u|
      ≤ costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) := by
    intro t u
    rw [abs_of_pos (flowDeriv_pos hell t u)]
    exact flowDeriv_le_costP1 (h := fun a y => -xi a y) (C := fun a => kappa * m a) hPhid' hxcont hell
      (fun a x => by simpa only [abs_neg] using hC a x) (continuous_const.mul hmc) hCstop hmc
      (fun _ => le_rfl) hT t u
  have hG1 : ∀ t u,
      |flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t u|
        ≤ costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s) := fun t u =>
    abs_flowDeriv2_le_costG1 (h := fun a y => -xi a y) (C := fun a => kappa * m a)
      (C2 := fun a => kappa2 * m a) hPhid' hxcont hxxcont hell (fun a x => by simpa only [abs_neg] using hC a x)
      (continuous_const.mul hmc) hCstop (fun a x => by simpa only [abs_neg] using hC2 a x)
      (continuous_const.mul hmc) hC2stop hmc (fun _ => le_rfl) (fun _ => le_rfl) hT t u
  -- the chain rule
  intro t
  refine supNorm_iteratedDeriv_comp_le
    (phi1 := fun u => flowDeriv (fun a y => -xiX a y) Phi ell t u)
    (phi2 := fun u =>
      flowDeriv2 (fun a y => -xiX a y) (fun a y => -xiXX a y) Phi ell t u)
    (e1 := fun x => g t x - eta t x) (e2 := fun x => gS t x - (g t x - eta t x))
    (S0 := S0 t) (S1 := 2 * S0 t) (S2 := Dd t + 2 * S0 t)
    (P1 := costP1 ell kappa (∫ s in (0 : ℝ)..T, m s))
    (G1 := costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s))
    (fun u => hphi1 t u) (fun u => hphi2 t u) (hjac t)
    (fun x => (hgSd t x).sub (hjac t x)) (fun x => hetabd t x) (fun x => ?_)
    (fun x => ?_) (fun u => hP1 t u) (fun u => hG1 t u) (hd0 t) (hd1 t) (hd2 t)
  · have h3 : |g t x - eta t x| ≤ |g t x| + |eta t x| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (g t x) (-eta t x)
    have := hgbd t x
    have := hetabd t x
    linarith
  · have h3 : |gS t x - (g t x - eta t x)| ≤ |gS t x| + |g t x - eta t x| :=
      abs_sub _ _
    have h4 : |g t x - eta t x| ≤ |g t x| + |eta t x| := abs_sub _ _
    have := hgSbd t x
    have := hgbd t x
    have := hetabd t x
    linarith

end GaugeFlowSupJacobi
