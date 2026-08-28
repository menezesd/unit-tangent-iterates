import UnitTangentIterates.GaugeGeometrySeparatedSliceCertificate
import UnitTangentIterates.GaugeNormalPathVariableSeparated

/-! The separated inverse-Jacobi certificate transported by the actual
variable-period gauge flow. -/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric
  RearTrack ArclengthInverse

namespace GaugeGeometryVariableSeparatedFlowed

open UniformFrameBounds GaugeNormalPath GaugeJacobiAssemblyVariable
  JacobiArclengthUniform SelectedInversePathGeometry
  SelectedRearArclengthEstimates PathMetricJacobi
  GaugeNormalPathSeparated

theorem flowedBounds
    {p q : Data} (Gamma : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ}
    {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hetaRper : ∀ t, Periodic (etaR t) (Qf t))
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hlink : ∀ t u, Gamma.eta t u = etaF t (P t * u))
    (hvper : ∀ t, Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, etaR t = fun _ => 0) :
    FlowedBounds Gamma.eta (fun t u => etaR t (Phi t u))
      (gaugeCW P1 D.rateLip Gamma.T (Qf 0))
      (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
      (flowFirst
        (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
        D.rateLip Gamma.T (Qf 0))
      (flowFirst (1 / Real.sqrt (1 - kh ^ 2))
        D.rateLip Gamma.T (Qf 0))
      (flowSecond
          (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
          D.rateLip Gamma.T (Qf 0) +
        flowDrift
          (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
          D.rateLip D.rateBound2 Gamma.T (Qf 0))
      (flowSecond
          (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
            1 / Real.sqrt (1 - kh ^ 2))
          D.rateLip Gamma.T (Qf 0) +
        flowDrift (1 / Real.sqrt (1 - kh ^ 2))
          D.rateLip D.rateBound2 Gamma.T (Qf 0))
      (flowSecond (1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2))
        D.rateLip Gamma.T (Qf 0)) := by
  let c : ℝ := Real.sqrt (1 - kh ^ 2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by nlinarith)
  have hPpos : ∀ t, 0 < P t := fun t => hP0.trans_le (hPl t)
  have hP1 : 0 < P1 := (hPpos 0).trans_le (hPu 0)
  have hdeltac : ∀ t, Continuous (delta t) := fun t =>
    Differentiable.continuous fun s => (hsteer t s).differentiableAt
  have hcos : ∀ t s, c ≤ Real.cos (delta t s) := fun t s =>
    Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s)
  have hQpos : ∀ t, 0 < Qf t := by
    intro t
    rw [hQdef t]
    exact lt_of_lt_of_le (mul_pos hc (hPpos t))
      (rearArclength_ge (hdeltac t) (hcos t) (hPpos t).le)
  have C := GaugeGeometrySeparatedSliceCertificate.certificate
    hP0 hkh0 hkh1 hPl hPu hsteer hstrip0 hstrip1 hdper hK
    hetaFd hetaFsc hetaFper hsfinv hetaR
    (fun t => by simpa [hQdef t] using hetaRper t)
  have hden : 0 < 1 - Real.exp (-(c * P0)) :=
    JacobiNormalized.one_sub_exp_pos (mul_pos hc hP0)
  exact GaugeNormalPathVariableSeparated.flowedBounds Gamma D hQpos hQd
    hvper hxiqp hPhid hPhi0 hetaC2 hetaRper hrest
    hP1.le (div_nonneg hP1.le hden.le)
    (div_nonneg hP1.le hden.le) (one_div_nonneg.mpr hc.le)
    (div_nonneg hP1.le hden.le)
    (add_nonneg
      (div_nonneg (mul_nonneg (by positivity) (sq_nonneg kh)) (by positivity))
      (one_div_nonneg.mpr hc.le))
    (one_div_nonneg.mpr (mul_nonneg hP0.le (sq_nonneg c)))
    (fun t _ => by simpa [hQdef t, hlink] using C.w t)
    (fun t _ => by simpa [c, hlink] using C.s0 t)
    (fun t _ => by
      have ht : Gamma.eta t = fun u => etaF t (P t * u) := funext (hlink t)
      rw [ht]
      simpa [c] using C.separated t)

end GaugeGeometryVariableSeparatedFlowed
