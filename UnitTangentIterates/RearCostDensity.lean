import Mathlib
import UnitTangentIterates.GaugeFlowDerivCost

/-!
# Choosing the cost density of the family of selected rears

`SelInvRearFamilySupC2.dist_selInv_le_of_rear_family_sup_C2` bounds the marked
`C²` distance of the two selected inverses of the ends of a normal path of
fronts by a function of two costs: the cost `c = cost Γ` of the path of fronts,
and the total cost `M = ∫₀^T m` of the family of selected rears, `m` being an
auxiliary cost density which that statement asks the caller to provide,
subject to three conditions:

* it dominates the normal rate of the rears, `m_F/√(1−κ̂²) ≤ m`;
* `2 (m_F/√(1−κ̂²)) · costP1 ℓ κ̂ M ≤ m`;
* `(D + 2 m_F/√(1−κ̂²)) · costP1 ℓ κ̂ M ² + 2 (m_F/√(1−κ̂²)) · costG1 ℓ κ̂ κ₂ M ≤ m`.

Since `costP1 ℓ κ̂ M = ℓ e^{κ̂M}` and `costG1 ℓ κ̂ κ₂ M = (costP1)² κ₂ M` both
grow with `M`, and `M` is itself the integral of `m`, this is a fixed-point
condition on `m`.  This file solves it in the only case that matters: the
density `m` is taken proportional to the cost density of the path of fronts,
`m = C · m_F`, so that `M = C · c`, and as long as the resulting total cost is
at most one the two flow constants are bounded by their values at `M = 1`, which
makes all three conditions linear.  The constant is

`rearCostConst κ̂' κ̂ κ₂ ℓ d = max r (max (2 P₁ r) ((d + 2r) P₁² + 2 G₁ r))` ,

with `r = 1/√(1−κ̂'²)`, `P₁ = costP1 ℓ κ̂ 1`, `G₁ = costG1 ℓ κ̂ κ₂ 1`, and `d` the
constant with which the source density `D` of the inverse Jacobi ODE is
dominated by the cost density of the fronts.

Main results: `rearCostConst_ge_one`, `mge_of_rearCostConst`,
`supA_of_rearCostConst`, `supB_of_rearCostConst`.
-/

noncomputable section

namespace RearCostDensity

open GaugeFlowDerivCost

variable {kh khat kappa2 ell dd : ℝ}

/-- The reciprocal `1/√(1−κ̂²)` of the cosine bound on the selected strip. -/
theorem one_le_invSqrt (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    1 ≤ 1 / Real.sqrt (1 - kh ^ 2) := by
  have hsq : 1 - kh ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 < 1 - kh ^ 2 := by nlinarith
  have h1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := by
    have := Real.sqrt_le_sqrt hsq
    simpa using this
  have h2 : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 hpos
  rw [le_div_iff₀ h2]
  linarith

/-- **The constant of the rear cost density.** -/
def rearCostConst (kh khat kappa2 ell dd : ℝ) : ℝ :=
  max (1 / Real.sqrt (1 - kh ^ 2))
    (max (2 * costP1 ell khat 1 * (1 / Real.sqrt (1 - kh ^ 2)))
      ((dd + 2 * (1 / Real.sqrt (1 - kh ^ 2))) * costP1 ell khat 1 ^ 2
        + 2 * costG1 ell khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2))))

theorem invSqrt_le_rearCostConst :
    1 / Real.sqrt (1 - kh ^ 2) ≤ rearCostConst kh khat kappa2 ell dd :=
  le_max_left _ _

/-- The constant is at least one. -/
theorem rearCostConst_ge_one (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    1 ≤ rearCostConst kh khat kappa2 ell dd :=
  le_trans (one_le_invSqrt hkh0 hkh1) invSqrt_le_rearCostConst

theorem rearCostConst_pos (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 < rearCostConst kh khat kappa2 ell dd :=
  lt_of_lt_of_le zero_lt_one (rearCostConst_ge_one hkh0 hkh1)

/-! ### Monotonicity of the two flow constants -/

theorem costP1_le_one (hell : 0 ≤ ell) (hkhat : 0 ≤ khat) {M : ℝ} (hM : M ≤ 1) :
    costP1 ell khat M ≤ costP1 ell khat 1 := by
  unfold costP1
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hell

theorem costP1_nonneg (hell : 0 ≤ ell) : 0 ≤ costP1 ell khat M := by
  unfold costP1; positivity

theorem costG1_le_one (hell : 0 ≤ ell) (hkhat : 0 ≤ khat) (hk2 : 0 ≤ kappa2)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 1) :
    costG1 ell khat kappa2 M ≤ costG1 ell khat kappa2 1 := by
  unfold costG1
  have h1 : costP1 ell khat M ^ 2 ≤ costP1 ell khat 1 ^ 2 := by
    have := costP1_le_one (khat := khat) hell hkhat hM
    have h0 := costP1_nonneg (khat := khat) (M := M) hell
    nlinarith
  have h2 : kappa2 * M ≤ kappa2 * 1 := by nlinarith
  have h3 : 0 ≤ kappa2 * M := mul_nonneg hk2 hM0
  nlinarith [costP1_nonneg (ell := ell) (khat := khat) (M := 1) hell]

/-! ### The three conditions -/

variable {mF Dd C : ℝ}

/-- The chosen density dominates the normal rate of the rears. -/
theorem mge_of_rearCostConst (hmF : 0 ≤ mF) :
    mF / Real.sqrt (1 - kh ^ 2) ≤ rearCostConst kh khat kappa2 ell dd * mF := by
  have h : 1 / Real.sqrt (1 - kh ^ 2) ≤ rearCostConst kh khat kappa2 ell dd :=
    invSqrt_le_rearCostConst
  have : mF / Real.sqrt (1 - kh ^ 2) = (1 / Real.sqrt (1 - kh ^ 2)) * mF := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right h hmF

/-- The first sup condition. -/
theorem supA_of_rearCostConst (hmF : 0 ≤ mF)
    (hell : 0 ≤ ell) (hkhat : 0 ≤ khat) {M : ℝ} (hM : M ≤ 1) :
    2 * (mF / Real.sqrt (1 - kh ^ 2)) * costP1 ell khat M
      ≤ rearCostConst kh khat kappa2 ell dd * mF := by
  have hr : 0 ≤ 1 / Real.sqrt (1 - kh ^ 2) := by positivity
  have hP := costP1_le_one (ell := ell) (khat := khat) hell hkhat hM
  have hP0 := costP1_nonneg (ell := ell) (khat := khat) (M := M) hell
  have hstep : 2 * (mF / Real.sqrt (1 - kh ^ 2)) * costP1 ell khat M
      ≤ (2 * costP1 ell khat 1 * (1 / Real.sqrt (1 - kh ^ 2))) * mF := by
    have hmr : 0 ≤ mF * (1 / Real.sqrt (1 - kh ^ 2)) := mul_nonneg hmF hr
    have : mF / Real.sqrt (1 - kh ^ 2) = mF * (1 / Real.sqrt (1 - kh ^ 2)) := by ring
    rw [this]
    nlinarith
  refine hstep.trans (mul_le_mul_of_nonneg_right ?_ hmF)
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The second sup condition. -/
theorem supB_of_rearCostConst (hmF : 0 ≤ mF)
    (hell : 0 ≤ ell) (hkhat : 0 ≤ khat) (hk2 : 0 ≤ kappa2)
    (hDd : Dd ≤ dd * mF) (hDd0 : 0 ≤ Dd) {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 1) :
    (Dd + 2 * (mF / Real.sqrt (1 - kh ^ 2))) * costP1 ell khat M ^ 2
        + 2 * (mF / Real.sqrt (1 - kh ^ 2)) * costG1 ell khat kappa2 M
      ≤ rearCostConst kh khat kappa2 ell dd * mF := by
  set r : ℝ := 1 / Real.sqrt (1 - kh ^ 2) with hrdef
  have hr : 0 ≤ r := by rw [hrdef]; positivity
  have hdiv : mF / Real.sqrt (1 - kh ^ 2) = mF * r := by rw [hrdef]; ring
  have hP := costP1_le_one (ell := ell) (khat := khat) hell hkhat hM
  have hP0 := costP1_nonneg (ell := ell) (khat := khat) (M := M) hell
  have hP01 := costP1_nonneg (ell := ell) (khat := khat) (M := 1) hell
  have hPsq : costP1 ell khat M ^ 2 ≤ costP1 ell khat 1 ^ 2 := by nlinarith
  have hG := costG1_le_one (ell := ell) (khat := khat) (kappa2 := kappa2) hell hkhat hk2 hM0 hM
  have hG0 : 0 ≤ costG1 ell khat kappa2 M := by
    unfold costG1
    have : 0 ≤ kappa2 * M := mul_nonneg hk2 hM0
    positivity
  have hmr : 0 ≤ mF * r := mul_nonneg hmF hr
  have hstep : (Dd + 2 * (mF * r)) * costP1 ell khat M ^ 2
      + 2 * (mF * r) * costG1 ell khat kappa2 M
      ≤ ((dd + 2 * r) * costP1 ell khat 1 ^ 2 + 2 * costG1 ell khat kappa2 1 * r) * mF := by
    have h1 : (Dd + 2 * (mF * r)) * costP1 ell khat M ^ 2
        ≤ (dd * mF + 2 * (mF * r)) * costP1 ell khat 1 ^ 2 := by
      have hle : Dd + 2 * (mF * r) ≤ dd * mF + 2 * (mF * r) := by linarith
      have hnn : 0 ≤ Dd + 2 * (mF * r) := by linarith
      nlinarith
    have h2 : 2 * (mF * r) * costG1 ell khat kappa2 M
        ≤ 2 * (mF * r) * costG1 ell khat kappa2 1 := by nlinarith
    nlinarith
  rw [hdiv]
  refine hstep.trans (mul_le_mul_of_nonneg_right ?_ hmF)
  exact le_trans (le_max_right _ _) (le_max_right _ _)

end RearCostDensity
