import Mathlib
import UnitTangentIterates.ProfiledInterpolationGlobalBounds
import UnitTangentIterates.ProfiledInterpolationFlowBounds
import UnitTangentIterates.GaugeMarkedDataOfNormalRate

/-! # Quantitative input package for the profiled interpolation -/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath

namespace ProfiledInterpolationBounds

open ProfiledInterpolationFields InterpolationPathDist InterpolationFrame
  InterpolationVariableSpeedConstants InterpolationControlledJunctionFinal
  NormalPathC2IncrementVariableSpeed

structure Bounds
    (p q : Data) (k0 k1 k0' k1' : ℝ → ℝ)
    (theta0 L kstar kd dsup eps : ℝ) (Phi : ℝ → ℝ → ℝ) where
  K : NNReal
  K2 : NNReal
  C : ℝ → ℝ
  C2 : ℝ → ℝ
  Kx : ℝ → ℝ
  Rb : ℝ → ℝ
  S0 : ℝ → ℝ
  S1 : ℝ → ℝ
  S2 : ℝ → ℝ
  m : ℝ → ℝ
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  r : ℝ
  kx : ℝ
  hlip : ∀ t, LipschitzWith K (h k0 k1 theta0 L t)
  hxxK : ∀ t x, |hxx k0 k1 k0' k1' theta0 L t x| ≤ (K2 : ℝ)
  hP1 : ∀ t u, FlowDerivative.flowDeriv
    (hx k0 k1 theta0 L) (PhiB Phi) (2 * L) t u ≤ costFac kstar L eps
  hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2
    (hx k0 k1 theta0 L) (hxx k0 k1 k0' k1' theta0 L)
    (PhiB Phi) (2 * L) t u| ≤ interpolationG1 kstar kd L eps
  hk : ∀ t x, |kappa k0 k1 t x| ≤ kstar
  hC : ∀ t x, |hx k0 k1 theta0 L t x| ≤ C t
  hC2 : ∀ t x, |hxx k0 k1 k0' k1' theta0 L t x| ≤ C2 t
  hCnn : ∀ t, 0 ≤ C t
  hC2nn : ∀ t, 0 ≤ C2 t
  hcost : ∀ t, C t * costFac kstar L eps ≤
    kstar * costFac kstar L eps * m t
  hcost2 : ∀ t, C t * interpolationG1 kstar kd L eps +
    C2 t * costFac kstar L eps ^ 2 ≤ interpolationCgFinal kstar kd L eps * m t
  hKxbd : ∀ t x, |kX k0' k1' t x| ≤ Kx t
  hRbd : ∀ t x, |h k0 k1 theta0 L t x| ≤ Rb t
  hKxnn : ∀ t, 0 ≤ Kx t
  hS0bd : ∀ t x, |en k0 k1 theta0 L t x| ≤ S0 t
  hS1bd : ∀ t x, |enS k0 k1 theta0 L t x| ≤ S1 t
  hS2bd : ∀ t x, |enSS k0 k1 k0' k1' theta0 L t x| ≤ S2 t
  hS0m : ∀ t, S0 t ≤ c0 * m t
  hS1m : ∀ t, S1 t ≤ c1 * m t
  hS2m : ∀ t, S2 t ≤ c2 * m t
  hRbm : ∀ t, Rb t ≤ r * m t
  hKxm : ∀ t, Kx t ≤ kx
  hr : 0 ≤ r
  hm0 : ∀ t, 0 ≤ m t
  hnumA : c1 + 2 * kstar * r ≤ 1 / interpolationP0 kstar kd L eps
  hnumK : c2 + kstar ^ 2 * c0 + 2 * r * kx ≤
    1 / interpolationP0 kstar kd L eps ^ 2 + kstar ^ 2
  hstart : ∀ u, Y k0 k1 theta0 L 0 (PhiB Phi 0 u) = p.1 u
  hfinish : ∀ u, Y k0 k1 theta0 L 1 (PhiB Phi 1 u) = q.1 u
  hmc : Continuous m
  hmstop : ∀ t ∉ Ioo (0 : ℝ) 1, m t = 0
  hmbd : ∀ t u, |en k0 k1 theta0 L t (PhiB Phi t u)| ≤ m t
  hmsup : ∀ t, ∀ j ≤ 2,
    MarkedTopology.supNorm
      (iteratedDeriv j (fun u => en k0 k1 theta0 L t (PhiB Phi t u))) ≤ m t
  hcostIntegral : (∫ t in (0 : ℝ)..1, m t) ≤
    interpPathCost kstar kd dsup L eps

/-- Apply the strengthened non-fundamental normal-rate theorem from the
qualitative and quantitative packages. -/
theorem exists_path
    {p q : Data} {k0 k1 k0' k1' : ℝ → ℝ}
    {theta0 L kstar kd dsup eps : ℝ} {Phi : ℝ → ℝ → ℝ}
    (Q : Certificate k0 k1 k0' k1' theta0 L Phi)
    (D : Bounds p q k0 k1 k0' k1' theta0 L kstar kd dsup eps Phi)
    (hL : 0 < L) :
    ∃ Gamma : NormalPath p q, Gamma.T = 1 ∧
      (∀ t u, Gamma.X t u = Y k0 k1 theta0 L t (PhiB Phi t u)) ∧
      (∀ t u, Gamma.eta t u = en k0 k1 theta0 L t (PhiB Phi t u)) ∧
      Gamma.m = D.m ∧ cost Gamma = (∫ t in (0 : ℝ)..1, D.m t) ∧
      IsVariableSpeedNormalPath
        (interpolationP0 kstar kd L eps) (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps) (interpolationCgFinal kstar kd L eps) Gamma := by
  exact GaugeMarkedDataOfNormalRate.exists_variableSpeed_normalPath_of_normal_rate_with_eta_X
    Q.Y_C1 Q.tangent Q.motion Q.angle_space D.hlip Q.field_cont Q.field_flow
    (by linarith : 0 < 2 * L) Q.phi_initial Q.field_space Q.field1_cont
    Q.field_space2 Q.field2_cont D.hxxK D.hP1 D.hG1 D.hk D.hC D.hC2
    D.hCnn D.hC2nn D.hcost D.hcost2 Q.angle_C1 Q.kappa_C1
    Q.angle_time Q.kappa_time Q.kappa_space Q.alphaT_cont Q.kT_cont Q.kX_cont
    Q.kappa_C1.continuous D.hKxbd D.hRbd D.hKxnn Q.en_space Q.en_space2
    Q.alphaT_space Q.mixed_expanded D.hS0bd D.hS1bd D.hS2bd
    D.hS0m D.hS1m D.hS2m D.hRbm D.hKxm D.hr D.hm0 D.hnumA D.hnumK
    one_pos Q.en_cont D.hstart D.hfinish D.hmc D.hmstop D.hmbd D.hmsup

/-- The complete profiled interpolation package produces the public controlled
junction directly.  In particular, callers no longer have to postulate the
opaque `hpath` premise of `InterpolationControlledJunctionFinal`: its path,
endpoints, normal-rate identity, variable-speed estimates, and cost bound are
all consequences of `Certificate` and `Bounds`. -/
theorem exists_interpolationControlledJunctionOutput
    {p q : Data} {k0 k1 k0' k1' : ℝ → ℝ}
    {theta0 L kstar kd dsup eps : ℝ} {Phi : ℝ → ℝ → ℝ}
    (Q : Certificate k0 k1 k0' k1' theta0 L Phi)
    (D : Bounds p q k0 k1 k0' k1' theta0 L kstar kd dsup eps Phi)
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (hL : 0 < L) :
    ∃ I : InterpolationControlledJunctionOutput p q
        (interpolationP0 kstar kd L eps) (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps)
        (interpPathCost kstar kd dsup L eps),
      I.path.eta = pathEta k0 k1 theta0 L Phi := by
  obtain ⟨Gamma, hT, hX, heta, _hm, hcost, hvar⟩ := exists_path Q D hL
  apply InterpolationControlledJunctionFinal.exists_interpolationControlledJunctionOutput C
  refine ⟨Gamma, ?_, ?_, ?_, hvar, hcost.trans_le D.hcostIntegral⟩
  · funext u
    exact (hX 0 u).trans (D.hstart u)
  · rw [hT]
    funext u
    exact (hX 1 u).trans (D.hfinish u)
  · funext t u
    simpa [pathEta, scaledEta, en, PhiB] using heta t u

end ProfiledInterpolationBounds
