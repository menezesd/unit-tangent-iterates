import UnitTangentIterates.PathMetric
import UnitTangentIterates.FrontRegularityPackage

/-!
# The cost-density hypotheses of the rear-family constructor
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace PathMetric

variable {p q : Data}

/-- **The rescaled cost density.**  The rear-family constructor asks for a
majorant `m` of `Γ.m / √(1−κ̂²)` that is continuous, nonnegative and vanishes
outside the time interval.  No construction is needed: the rescaling of `Γ.m`
itself has all four properties, because `NormalPath` already carries `cont_m`,
`m_nonneg` and `m_stop`, and the majorisation holds with equality. -/
def scaledDensity (Γ : NormalPath p q) (kh : ℝ) : ℝ → ℝ :=
  fun t => Γ.m t / Real.sqrt (1 - kh ^ 2)

theorem scaledDensity_continuous (Γ : NormalPath p q) (kh : ℝ) :
    Continuous (scaledDensity Γ kh) := Γ.cont_m.div_const _

theorem scaledDensity_nonneg {kh : ℝ} (Γ : NormalPath p q) (hkh0 : 0 ≤ kh)
    (hkh1 : kh < 1) (t : ℝ) : 0 ≤ scaledDensity Γ kh t := by
  have hc : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact div_nonneg (Γ.m_nonneg t) hc.le

theorem scaledDensity_stop (Γ : NormalPath p q) (kh : ℝ) {t : ℝ}
    (ht : t ∉ Ioo (0 : ℝ) Γ.T) : scaledDensity Γ kh t = 0 := by
  simp [scaledDensity, Γ.m_stop t ht]

theorem scaledDensity_ge (Γ : NormalPath p q) (kh : ℝ) (t : ℝ) :
    Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ scaledDensity Γ kh t := le_rfl

/-- **The rescaled cost.**  The constructor's Jacobi constants are evaluated at
`∫₀^T m`, and for this choice that integral is `cost Γ / √(1−κ̂²)` — so the
constants are explicit functions of the original cost, which is what the
shadowing estimate needs. -/
theorem integral_scaledDensity (Γ : NormalPath p q) (kh : ℝ) :
    (∫ t in (0 : ℝ)..Γ.T, scaledDensity Γ kh t)
      = cost Γ / Real.sqrt (1 - kh ^ 2) := by
  simp only [scaledDensity, cost]
  rw [intervalIntegral.integral_div]

end PathMetric
