import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource

/-! # Generic composition budgets from a scaled dominating density -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCompositionDensityBudgets

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource

variable {a b : Data} {Delta : NormalPath a b}
  {P0 kap khat Qmax C d Q kceil : ℝ}
  {A : MarkingAwareSource Delta P0 kap khat Qmax}

/-- A coefficient dominating the mass-one first and second flow costs turns a
raw path-density majorant into both hypotheses of `normal_sup_of_spatial`. -/
theorem of_scaled_density
    (raw : ℝ → ℝ)
    (hraw0 : ∀ t, 0 ≤ raw t)
    (hdom : ∀ t, Delta.m t / Real.sqrt (1 - kap ^ 2) ≤ raw t)
    (hm : ∀ t, A.m t = C * raw t)
    (hDd : ∀ t, A.Dd t ≤ d * raw t)
    (hd0 : 0 ≤ d)
    (hperiod0 : 0 ≤ rearPeriod A 0)
    (hperiod : rearPeriod A 0 ≤ Q)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hkceil0 : 0 ≤ kceil)
    (hk1le : GaugeMarkedDataOfRearFamily.rearKappa1 kap ≤ kceil)
    (hmass : (∫ s in (0 : ℝ)..Delta.T, A.m s) ≤ 1)
    (hfirst : 2 * GaugeFlowDerivCost.costP1 Q
      kceil 1 ≤ C)
    (hsecond :
      (d + 2) * GaugeFlowDerivCost.costP1 Q
          kceil 1 ^ 2 +
        2 * GaugeFlowDerivCost.costG1 Q
          kceil
          (GaugeMarkedDataOfRearFamily.rearKappa2 kap) 1 ≤ C) :
    (∀ t, 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) *
        GaugeFlowDerivCost.costP1 (rearPeriod A 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
          (∫ s in (0 : ℝ)..Delta.T, A.m s) ≤ A.m t) ∧
      (∀ t,
        (A.Dd t + 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2))) *
            GaugeFlowDerivCost.costP1 (rearPeriod A 0)
              (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
              (∫ s in (0 : ℝ)..Delta.T, A.m s) ^ 2 +
          2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) *
            GaugeFlowDerivCost.costG1 (rearPeriod A 0)
              (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
              (GaugeMarkedDataOfRearFamily.rearKappa2 kap)
              (∫ s in (0 : ℝ)..Delta.T, A.m s) ≤ A.m t) := by
  let M := ∫ s in (0 : ℝ)..Delta.T, A.m s
  let k1 := GaugeMarkedDataOfRearFamily.rearKappa1 kap
  let k2 := GaugeMarkedDataOfRearFamily.rearKappa2 kap
  let p := GaugeFlowDerivCost.costP1 (rearPeriod A 0) k1 M
  let pa := GaugeFlowDerivCost.costP1 (rearPeriod A 0) kceil M
  let p1 := GaugeFlowDerivCost.costP1 Q kceil 1
  let g := GaugeFlowDerivCost.costG1 (rearPeriod A 0) k1 k2 M
  let ga := GaugeFlowDerivCost.costG1 (rearPeriod A 0) kceil k2 M
  let g1 := GaugeFlowDerivCost.costG1 Q kceil k2 1
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg Delta.T_pos.le
    (fun t _ ↦ A.density_nonnegative t)
  have hk10 : 0 ≤ k1 :=
    GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1
  have hk20 : 0 ≤ k2 :=
    GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkap0 hkap1
  have hpK : p ≤ pa := by
    unfold p pa GaugeFlowDerivCost.costP1
    apply mul_le_mul_of_nonneg_left
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hk1le hM0
    exact hperiod0
  have hpa : pa ≤ p1 := by
    simpa [pa, p1, M] using
      GaugeFlowDerivCost.costP1_le hperiod0 hperiod hkceil0 hM0 hmass
  have hp : p ≤ p1 := hpK.trans hpa
  have hp0 : 0 ≤ p := by
    unfold p GaugeFlowDerivCost.costP1
    exact mul_nonneg hperiod0 (Real.exp_pos _).le
  have hgK : g ≤ ga := by
    unfold g ga GaugeFlowDerivCost.costG1
    have hpa0 : 0 ≤ pa := by
      unfold pa GaugeFlowDerivCost.costP1
      exact mul_nonneg hperiod0 (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hp0 hpa0).2 hpK) (mul_nonneg hk20 hM0)
  have hga : ga ≤ g1 := by
    simpa [ga, g1, M] using
      GaugeFlowDerivCost.costG1_le hperiod0 hperiod hkceil0 hk20 hM0 hmass
  have hg : g ≤ g1 := hgK.trans hga
  have hp10 : 0 ≤ p1 := hp0.trans hp
  have hg0 : 0 ≤ g := by
    unfold g GaugeFlowDerivCost.costG1
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hk20 hM0)
  have hg10 : 0 ≤ g1 := hg0.trans hg
  constructor
  · intro t
    have hr0 := hraw0 t
    have hrho0 : 0 ≤ Delta.m t / Real.sqrt (1 - kap ^ 2) :=
      div_nonneg (Delta.m_nonneg t) (Real.sqrt_nonneg _)
    rw [hm t]
    nlinarith [hdom t]
  · intro t
    have hr0 := hraw0 t
    have hrho0 : 0 ≤ Delta.m t / Real.sqrt (1 - kap ^ 2) :=
      div_nonneg (Delta.m_nonneg t) (Real.sqrt_nonneg _)
    have hfac : A.Dd t + 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) ≤
        (d + 2) * raw t := by nlinarith [hDd t, hdom t]
    have hupper0 : 0 ≤ (d + 2) * raw t :=
      mul_nonneg (add_nonneg hd0 (by norm_num)) hr0
    have hpsq : p ^ 2 ≤ p1 ^ 2 := (sq_le_sq₀ hp0 hp10).2 hp
    have hterm1 :
        (A.Dd t + 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2))) * p ^ 2 ≤
          ((d + 2) * p1 ^ 2) * raw t := by
      calc
        _ ≤ ((d + 2) * raw t) * p1 ^ 2 :=
          mul_le_mul hfac hpsq (sq_nonneg p) hupper0
        _ = _ := by ring
    have hterm2 :
        2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) * g ≤
          (2 * g1) * raw t := by nlinarith [hdom t]
    rw [hm t]
    nlinarith [hterm1, hterm2,
      mul_le_mul_of_nonneg_right hsecond hr0]

end FiniteSmoothRearFamilyMarkingAwareCompositionDensityBudgets
