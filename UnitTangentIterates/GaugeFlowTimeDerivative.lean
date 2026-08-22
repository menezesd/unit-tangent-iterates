import Mathlib
import UnitTangentIterates.FlowDerivative

/-!
# The time derivatives of the two parameter derivatives of a gauge flow

`FlowDerivative.lean` computes the derivative of a scalar flow in its initial
condition in closed form,

`∂_uΦ(t,u) = flowDeriv = ℓ · exp ∫₀^t ∂ₓh(s, Φ(s,u)) ds`,

and its parameter derivative

`∂²_uΦ(t,u) = flowDeriv2 = flowDeriv(t,u) · ∫₀^t ∂²ₓh(s,Φ(s,u))·flowDeriv(s,u) ds`.

The variable-speed estimate of `NormalPathC2IncrementVariableSpeed.lean` asks
for the derivatives of these two quantities in the *time*, and for bounds on
them by multiples of the cost density.  Both are immediate from the closed
forms: differentiating the primitive gives the variational equations

`∂_t ∂_uΦ = ∂ₓh(t,Φ)·∂_uΦ`,
`∂_t ∂²_uΦ = ∂ₓh(t,Φ)·∂²_uΦ + ∂²ₓh(t,Φ)·(∂_uΦ)²`,

so that a bound `|∂ₓh(t,·)| ≤ C t` together with `∂_uΦ ≤ P₁` bounds the first by
`C t · P₁`, and a bound `|∂²ₓh(t,·)| ≤ C₂ t` together with `|∂²_uΦ| ≤ G₁` bounds
the second by `C t · G₁ + C₂ t · P₁²` — exactly the two shapes
`IsVariableSpeedFamily` prescribes once `C t ≤ κ·m t` and `C₂ t ≤ κ₂·m t`.

Main results: `hasDerivAt_flowDeriv_time`, `hasDerivAt_flowDeriv2_time`,
`abs_flowDeriv_time_le`, `abs_flowDeriv2_time_le`.
-/

noncomputable section

open Set Filter Topology MeasureTheory Function

namespace GaugeFlowTimeDerivative

open FlowDerivative

variable {h hx hxx : ℝ → ℝ → ℝ} {ell : ℝ} {Phi : ℝ → ℝ → ℝ}

/-- The closed form of the second derivative of the flow in its initial
condition, as it appears in `FlowDerivative.hasDerivAt_flowDeriv`. -/
def flowDeriv2 (hx hxx : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ → ℝ) (ell : ℝ) (t u : ℝ) : ℝ :=
  flowDeriv hx Phi ell t u * ∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u

section

variable (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)

include hPhid

/-- The flow line is continuous in the time. -/
theorem continuous_flow_time (u : ℝ) : Continuous fun s => Phi s u := by
  have hd : Differentiable ℝ fun s => Phi s u := fun s => (hPhid u s).differentiableAt
  exact hd.continuous

/-- The field read along the flow line is continuous in the time. -/
theorem continuous_hx_flow (hxcont : Continuous (uncurry hx)) (u : ℝ) :
    Continuous fun s => hx s (Phi s u) :=
  hxcont.comp (continuous_id.prodMk (continuous_flow_time hPhid u))

/-- **The variational equation for the derivative of the flow in its initial
condition.** -/
theorem hasDerivAt_flowDeriv_time (hxcont : Continuous (uncurry hx)) (u t : ℝ) :
    HasDerivAt (fun r => flowDeriv hx Phi ell r u)
      (hx t (Phi t u) * flowDeriv hx Phi ell t u) t := by
  have hg : Continuous fun s => hx s (Phi s u) := continuous_hx_flow hPhid hxcont u
  have hA : HasDerivAt (fun r => ∫ s in (0:ℝ)..r, hx s (Phi s u)) (hx t (Phi t u)) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have h1 := (hA.exp).const_mul ell
  refine h1.congr_deriv ?_
  simp only [flowDeriv]
  ring

/-- The derivative of the flow in its initial condition is continuous in the
time, and so is its time derivative. -/
theorem continuous_flowDeriv_time_deriv (hxcont : Continuous (uncurry hx)) (u : ℝ) :
    Continuous fun t => hx t (Phi t u) * flowDeriv hx Phi ell t u :=
  (continuous_hx_flow hPhid hxcont u).mul
    (FlowDerivative.continuous_flowDeriv_time hPhid hxcont u)

/-- **The variational equation for the second derivative of the flow in its
initial condition.** -/
theorem hasDerivAt_flowDeriv2_time (hxcont : Continuous (uncurry hx))
    (hxxcont : Continuous (uncurry hxx)) (u t : ℝ) :
    HasDerivAt (fun r => flowDeriv2 hx hxx Phi ell r u)
      (hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u
        + hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2) t := by
  have hF : HasDerivAt (fun r => flowDeriv hx Phi ell r u)
      (hx t (Phi t u) * flowDeriv hx Phi ell t u) t :=
    hasDerivAt_flowDeriv_time hPhid hxcont u t
  have hint : Continuous fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u :=
    (hxxcont.comp (continuous_id.prodMk (continuous_flow_time hPhid u))).mul
      (FlowDerivative.continuous_flowDeriv_time hPhid hxcont u)
  have hJ : HasDerivAt
      (fun r => ∫ s in (0:ℝ)..r, hxx s (Phi s u) * flowDeriv hx Phi ell s u)
      (hxx t (Phi t u) * flowDeriv hx Phi ell t u) t :=
    intervalIntegral.integral_hasDerivAt_right (hint.intervalIntegrable 0 t)
      (hint.stronglyMeasurableAtFilter _ _) hint.continuousAt
  have h1 := hF.mul hJ
  refine h1.congr_deriv ?_
  simp only [flowDeriv2]
  ring

/-- The time derivative of the second derivative of the flow in its initial
condition is continuous in the time. -/
theorem continuous_flowDeriv2_time_deriv (hxcont : Continuous (uncurry hx))
    (hxxcont : Continuous (uncurry hxx)) (u : ℝ) :
    Continuous fun t => hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u
      + hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2 := by
  have hFc : Continuous fun s => flowDeriv hx Phi ell s u :=
    FlowDerivative.continuous_flowDeriv_time hPhid hxcont u
  have hint : Continuous fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u :=
    (hxxcont.comp (continuous_id.prodMk (continuous_flow_time hPhid u))).mul hFc
  have hJd : ∀ r : ℝ, HasDerivAt
      (fun r' => ∫ s in (0:ℝ)..r', hxx s (Phi s u) * flowDeriv hx Phi ell s u)
      (hxx r (Phi r u) * flowDeriv hx Phi ell r u) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hint.intervalIntegrable 0 r)
      (hint.stronglyMeasurableAtFilter _ _) hint.continuousAt
  have hJ : Continuous fun r => ∫ s in (0:ℝ)..r, hxx s (Phi s u) * flowDeriv hx Phi ell s u := by
    have hd : Differentiable ℝ
        fun r => ∫ s in (0:ℝ)..r, hxx s (Phi s u) * flowDeriv hx Phi ell s u :=
      fun r => (hJd r).differentiableAt
    exact hd.continuous
  have h2 : Continuous fun t => flowDeriv2 hx hxx Phi ell t u := by
    simpa [flowDeriv2] using hFc.mul hJ
  exact ((continuous_hx_flow hPhid hxcont u).mul h2).add
    ((hxxcont.comp (continuous_id.prodMk (continuous_flow_time hPhid u))).mul (hFc.pow 2))

end

/-! ### The bounds -/

/-- **The time derivative of the speed is bounded by the field derivative times
the speed.** -/
theorem abs_flowDeriv_time_le {C : ℝ → ℝ} {P1 : ℝ} {t u : ℝ}
    (hell : 0 < ell) (hxbd : |hx t (Phi t u)| ≤ C t)
    (hFbd : flowDeriv hx Phi ell t u ≤ P1) (hC : 0 ≤ C t) :
    |hx t (Phi t u) * flowDeriv hx Phi ell t u| ≤ C t * P1 := by
  have hFpos : 0 < flowDeriv hx Phi ell t u := flowDeriv_pos hell t u
  rw [abs_mul, abs_of_pos hFpos]
  exact mul_le_mul hxbd hFbd hFpos.le hC

/-- **The time derivative of the speed derivative is bounded by the two field
bounds.** -/
theorem abs_flowDeriv2_time_le {C C2 : ℝ → ℝ} {P1 G1 : ℝ} {t u : ℝ}
    (hell : 0 < ell) (hxbd : |hx t (Phi t u)| ≤ C t) (hxxbd : |hxx t (Phi t u)| ≤ C2 t)
    (hDbd : |flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hFbd : flowDeriv hx Phi ell t u ≤ P1) (hC : 0 ≤ C t) (hC2 : 0 ≤ C2 t) :
    |hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u
        + hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2|
      ≤ C t * G1 + C2 t * P1 ^ 2 := by
  have hFpos : 0 < flowDeriv hx Phi ell t u := flowDeriv_pos hell t u
  have h1 : |hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u| ≤ C t * G1 := by
    rw [abs_mul]
    exact mul_le_mul hxbd hDbd (abs_nonneg _) hC
  have h2 : |hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2| ≤ C2 t * P1 ^ 2 := by
    rw [abs_mul, abs_pow, abs_of_pos hFpos]
    refine mul_le_mul hxxbd (pow_le_pow_left₀ hFpos.le hFbd 2) (by positivity) hC2
  calc |hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u
        + hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2|
      ≤ |hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u|
        + |hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2| := abs_add_le _ _
    _ ≤ C t * G1 + C2 t * P1 ^ 2 := add_le_add h1 h2

end GaugeFlowTimeDerivative
