import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource
import UnitTangentIterates.PathMetricRescale
import UnitTangentIterates.ScaledCostDensity

/-!
# Time rescaling does not repair marking-aware source cost

A marking-aware source dominates the child path density divided by
`sqrt (1 - kh^2)`.  Integration therefore gives the same unavoidable factor
in the total source mass.  A common positive reparametrization of time cannot
remove it: both the child density and the source density acquire the same
Jacobian, and both integrals are unchanged.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

open FiniteSmoothRearFamilyMarkingAwareSource

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- The total density carried by a marking-aware source. -/
def sourceMass (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ :=
  ∫ t in (0 : ℝ)..Gamma.T, A.m t

/-- Density domination already forces the inverse-cosine loss in total mass. -/
theorem scaledCost_le_sourceMass
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    cost Gamma / Real.sqrt (1 - kh ^ 2) ≤ sourceMass A := by
  rw [← PathMetric.integral_scaledDensity]
  exact intervalIntegral.integral_mono_on Gamma.T_pos.le
    ((PathMetric.scaledDensity_continuous Gamma kh).intervalIntegrable 0 Gamma.T)
    (A.density_continuous.intervalIntegrable 0 Gamma.T)
    (fun t _ ↦ A.density_domination t)

/-- In particular, the source mass is never smaller than the child cost. -/
theorem cost_le_sourceMass
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    cost Gamma ≤ sourceMass A := by
  have hsqrt_pos : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hsqrt_le : Real.sqrt (1 - kh ^ 2) ≤ 1 := by
    have hsquare : (Real.sqrt (1 - kh ^ 2)) ^ 2 = 1 - kh ^ 2 :=
      Real.sq_sqrt (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
    nlinarith [Real.sqrt_nonneg (1 - kh ^ 2), sq_nonneg kh]
  have hcost_scaled : cost Gamma ≤ cost Gamma / Real.sqrt (1 - kh ^ 2) := by
    rw [le_div_iff₀ hsqrt_pos]
    exact mul_le_of_le_one_right (Gamma.cost_nonneg) hsqrt_le
  exact hcost_scaled.trans (scaledCost_le_sourceMass A)

/-- If the curvature parameter and child cost are positive, the source mass
is strictly larger than the child cost.  Thus a bound in the opposite
direction cannot be obtained by changing the speed of the same path. -/
theorem not_sourceMass_le_cost
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hkh : 0 < kh) (hcost : 0 < cost Gamma) :
    ¬ sourceMass A ≤ cost Gamma := by
  intro hle
  have hsqrt_pos : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [A.kh_lt_one])
  have hsquare : (Real.sqrt (1 - kh ^ 2)) ^ 2 = 1 - kh ^ 2 :=
    Real.sq_sqrt (by nlinarith [A.kh_lt_one])
  have hsqrt_lt : Real.sqrt (1 - kh ^ 2) < 1 := by
    nlinarith [Real.sqrt_nonneg (1 - kh ^ 2), sq_pos_of_pos hkh]
  have hscaled : cost Gamma / Real.sqrt (1 - kh ^ 2) ≤ cost Gamma :=
    (scaledCost_le_sourceMass A).trans hle
  have := (div_le_iff₀ hsqrt_pos).mp hscaled
  nlinarith

/-- The density obtained by running `m` at speed `a`. -/
def rescaledDensity (a : ℝ) (m : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ a * m (a * t)

/-- A positive time rescaling leaves the integral of an arbitrary continuous
density unchanged. -/
theorem integral_rescaledDensity
    (m : ℝ → ℝ) (_hm : Continuous m) {T a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..(T / a), rescaledDensity a m t) =
      ∫ t in (0 : ℝ)..T, m t := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hcomp : (∫ t in (0 : ℝ)..(T / a), m (a * t)) =
      a⁻¹ • ∫ x in (a * 0)..(a * (T / a)), m x :=
    intervalIntegral.integral_comp_mul_left m hane
  rw [show (∫ t in (0 : ℝ)..(T / a), rescaledDensity a m t) =
      ∫ t in (0 : ℝ)..(T / a), a * m (a * t) from rfl]
  rw [intervalIntegral.integral_const_mul, hcomp, mul_zero,
    mul_div_cancel₀ _ hane, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hane,
    one_mul]

/-- The source density and the child density retain their pointwise order
after a common positive time rescaling. -/
theorem rescaled_density_domination
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) {a : ℝ} (ha : 0 < a)
    (t : ℝ) :
    (Gamma.rescale ha).m t / Real.sqrt (1 - kh ^ 2) ≤
      rescaledDensity a A.m t := by
  dsimp [NormalPath.rescale, rescaledDensity]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (A.density_domination (a * t)) ha.le

/-- Any homogeneous pointwise inequality, including the composition `d1` and
`d2` inequalities after their invariant integral constants are fixed, is
equivalent before and after a common positive time rescaling. -/
theorem common_rescale_inequality_iff
    {a x y : ℝ} (ha : 0 < a) :
    a * x ≤ a * y ↔ x ≤ y := by
  constructor <;> intro h
  · nlinarith
  · exact mul_le_mul_of_nonneg_left h ha.le

end FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
