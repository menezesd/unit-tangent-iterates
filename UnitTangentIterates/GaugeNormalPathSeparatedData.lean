import UnitTangentIterates.GaugeNormalPathSeparated
import UnitTangentIterates.PathMetricJacobi
import UnitTangentIterates.ArclengthInverse

/-! Construct a normal path while retaining its separated density data. -/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace GaugeNormalPathSeparatedData

open GaugeNormalPathSeparated PathMetricJacobi

theorem exists_normalPath_of_flowedBounds
    {p q p' q' : Data} (Gamma : NormalPath p q)
    {XR nuR : ℝ → ℝ → ℂ} {eta : ℝ → ℝ → ℝ}
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Gamma.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u)
      ((eta t u : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (eta t u : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (eta t))
    (hetaper : ∀ t, Periodic (eta t) 1)
    {CW C0 C10 C11 C20 C21 C22 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0)
    (hC10 : 0 ≤ C10) (hC11 : 0 ≤ C11)
    (hC20 : 0 ≤ C20) (hC21 : 0 ≤ C21) (hC22 : 0 ≤ C22)
    (F : FlowedBounds Gamma.eta eta CW C0 C10 C11 C20 C21 C22) :
    ∃ Delta : NormalPath p' q', Delta.T = Gamma.T ∧
      Delta.cost = jacobiConst CW C0 (C10 + C11) (C20 + C21 + C22) * Gamma.cost ∧
      Delta.eta = eta ∧
      FlowedBounds Gamma.eta Delta.eta CW C0 C10 C11 C20 C21 C22 := by
  have hW0 : ∀ t, 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := fun t =>
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
  have hS0 : ∀ t, 0 ≤ supNorm (Gamma.eta t) := fun t => supNorm_nonneg _
  have hS1 : ∀ t, 0 ≤ supNorm (iteratedDeriv 1 (Gamma.eta t)) :=
    fun t => supNorm_nonneg _
  have hbdd : ∀ t u, |eta t u| ≤ supNorm (eta t) := by
    intro t u
    exact le_supNorm
      (ArclengthInverse.bddAbove_abs_of_periodic one_pos
        (hetaC2 t).continuous (hetaper t)) u
  have hcollapsed1 : ∀ t, supNorm (iteratedDeriv 1 (eta t)) ≤
      (C10 + C11) * ((∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
        supNorm (Gamma.eta t)) := by
    intro t
    calc
      supNorm (iteratedDeriv 1 (eta t)) ≤
          C10 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            C11 * supNorm (Gamma.eta t) := F.s1 t
      _ ≤ (C10 + C11) * ((∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          supNorm (Gamma.eta t)) := by
        nlinarith [hW0 t, hS0 t]
  have hcollapsed2 : ∀ t, supNorm (iteratedDeriv 2 (eta t)) ≤
      (C20 + C21 + C22) *
        ((∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          supNorm (Gamma.eta t) + supNorm (iteratedDeriv 1 (Gamma.eta t))) := by
    intro t
    calc
      supNorm (iteratedDeriv 2 (eta t)) ≤
          C20 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            C21 * supNorm (Gamma.eta t) +
            C22 * supNorm (iteratedDeriv 1 (Gamma.eta t)) := F.s2 t
      _ ≤ (C20 + C21 + C22) *
          ((∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            supNorm (Gamma.eta t) + supNorm (iteratedDeriv 1 (Gamma.eta t))) := by
        nlinarith [hW0 t, hS0 t, hS1 t]
  obtain ⟨Delta, hT, -, -, hcost, heta⟩ :=
    PathMetricJacobi.exists_normalPath_of_jacobi_data Gamma
      hCW hC0 (add_nonneg hC10 hC11)
      (add_nonneg (add_nonneg hC20 hC21) hC22)
      hstart hfinish hderiv hcont hnu hbdd F.w F.s0 hcollapsed1 hcollapsed2
  refine ⟨Delta, hT, hcost, heta, ?_⟩
  simpa [heta] using F

end GaugeNormalPathSeparatedData
