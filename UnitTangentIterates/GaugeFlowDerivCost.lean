import Mathlib
import UnitTangentIterates.GaugeFlowTimeDerivative

/-!
# The two flow derivatives of a gauge marking, bounded by the cost of the path

The variable-speed assembly of `GaugeFlowVariableSpeedPath.lean` asks for two
uniform bounds on the marking `Φ`, the flow of the field `h`:

`∂_uΦ = flowDeriv ≤ P₁`  and  `|∂²_uΦ| = |flowDeriv2| ≤ G₁` .

Both were assumed there.  They need not be: along a normal path the field of the
gauge flow is bounded together with its first two arclength derivatives by
multiples of the **cost density** `m` of the path
(`RearOwnTangentialCost.lean`, `RearOwnTangentialCostC2.lean`), and `m`
vanishes outside the time window of the path.  Since

`flowDeriv (t,u) = ℓ · exp ∫₀^t ∂ₓh(s, Φ(s,u)) ds` ,
`flowDeriv2 (t,u) = flowDeriv (t,u) · ∫₀^t ∂²ₓh(s, Φ(s,u))·flowDeriv (s,u) ds` ,

a bound `|∂ₓh(t,·)| ≤ C t` with `C` supported in the window gives
`flowDeriv ≤ ℓ e^{∫C}` at *every* time — the primitive cannot grow outside the
window — and a bound `|∂²ₓh(t,·)| ≤ C₂ t` then gives
`|flowDeriv2| ≤ (ℓ e^{∫C})²·∫C₂`.  With `C ≤ κ·m` and `C₂ ≤ κ₂·m` the two
constants are

`costP1 ℓ κ M = ℓ e^{κM}` ,  `costG1 ℓ κ κ₂ M = (ℓ e^{κM})²·κ₂M` ,

functions of the total cost `M = ∫₀^T m` alone.

Main results: `abs_intervalIntegral_le_of_stop`, `flowDeriv_le_of_bound`,
`abs_flowDeriv2_le_of_bound`, `flowDeriv_le_costP1`, `abs_flowDeriv2_le_costG1`.
-/

noncomputable section

open Set Function MeasureTheory

namespace GaugeFlowDerivCost

open FlowDerivative GaugeFlowTimeDerivative

variable {T : ℝ} {g C C2 m : ℝ → ℝ}

/-! ### Integrals of a density supported in the time window -/

/-- A continuous function dominated by a continuous density that vanishes
outside `(0,T)` has all its primitives bounded by the total mass of the
density. -/
theorem abs_intervalIntegral_le_of_stop (hg : Continuous g) (hC : Continuous C)
    (hbd : ∀ s, |g s| ≤ C s) (hstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0) (hT : 0 < T)
    (t : ℝ) : |∫ s in (0 : ℝ)..t, g s| ≤ ∫ s in (0 : ℝ)..T, C s := by
  have hCnn : ∀ s, 0 ≤ C s := fun s => le_trans (abs_nonneg _) (hbd s)
  have hg0 : ∀ s, s ∉ Ioo (0 : ℝ) T → g s = 0 := by
    intro s hs
    have := (hbd s).trans_eq (hstop s hs)
    exact abs_nonpos_iff.mp this
  -- the bound on the window
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ T →
      |∫ s in (0 : ℝ)..c, g s| ≤ ∫ s in (0 : ℝ)..T, C s := by
    intro c hc0 hcT
    have h1 : |∫ s in (0 : ℝ)..c, g s| ≤ ∫ s in (0 : ℝ)..c, |g s| :=
      intervalIntegral.abs_integral_le_integral_abs hc0
    have h2 : ∫ s in (0 : ℝ)..c, |g s| ≤ ∫ s in (0 : ℝ)..c, C s := by
      refine intervalIntegral.integral_mono_on hc0
        ((hg.abs).intervalIntegrable 0 c) (hC.intervalIntegrable 0 c) ?_
      intro s _
      exact hbd s
    have h3 : ∫ s in (0 : ℝ)..c, C s ≤ ∫ s in (0 : ℝ)..T, C s := by
      have hadd : (∫ s in (0 : ℝ)..c, C s) + ∫ s in c..T, C s = ∫ s in (0 : ℝ)..T, C s :=
        intervalIntegral.integral_add_adjacent_intervals
          (hC.intervalIntegrable 0 c) (hC.intervalIntegrable c T)
      have hnn : 0 ≤ ∫ s in c..T, C s :=
        intervalIntegral.integral_nonneg hcT fun s _ => hCnn s
      linarith
    exact h1.trans (h2.trans h3)
  rcases le_or_gt t 0 with ht | ht
  · have hzero : (∫ s in (0 : ℝ)..t, g s) = 0 := by
      have : (∫ s in (0 : ℝ)..t, g s) = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro s hs
        rw [Set.uIcc_of_ge ht] at hs
        exact hg0 s fun hmem => absurd hs.2 (not_le.mpr hmem.1)
      simpa using this
    rw [hzero, abs_zero]
    exact intervalIntegral.integral_nonneg hT.le fun s _ => hCnn s
  · rcases le_or_gt t T with htT | htT
    · exact key t ht.le htT
    · have hzero : (∫ s in T..t, g s) = 0 := by
        have : (∫ s in T..t, g s) = ∫ _s in T..t, (0 : ℝ) := by
          refine intervalIntegral.integral_congr ?_
          intro s hs
          rw [Set.uIcc_of_le htT.le] at hs
          exact hg0 s fun hmem => absurd hs.1 (not_le.mpr hmem.2)
        simpa using this
      have hadd : (∫ s in (0 : ℝ)..T, g s) + ∫ s in T..t, g s = ∫ s in (0 : ℝ)..t, g s :=
        intervalIntegral.integral_add_adjacent_intervals
          (hg.intervalIntegrable 0 T) (hg.intervalIntegrable T t)
      rw [hzero, add_zero] at hadd
      rw [← hadd]
      exact key T hT.le le_rfl

/-- A continuous density dominated by `κ` times another has total mass at most
`κ` times the other's. -/
theorem integral_le_const_mul {kappa : ℝ} (hCc : Continuous C) (hmc : Continuous m)
    (hCm : ∀ t, C t ≤ kappa * m t) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, C s) ≤ kappa * ∫ s in (0 : ℝ)..T, m s := by
  have hi : IntervalIntegrable (fun s => kappa * m s) MeasureTheory.volume 0 T :=
    (show Continuous fun s => kappa * m s from continuous_const.mul hmc).intervalIntegrable 0 T
  have h := intervalIntegral.integral_mono_on hT.le (hCc.intervalIntegrable 0 T) hi
    (fun s _ => hCm s)
  rwa [intervalIntegral.integral_const_mul] at h

/-! ### The two flow derivatives -/

variable {h hx hxx Phi : ℝ → ℝ → ℝ} {ell : ℝ}

section

variable (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)

include hPhid

/-- **The derivative of a gauge marking in its initial condition is bounded by
the total mass of a density dominating the space derivative of the field.** -/
theorem flowDeriv_le_of_bound (hxcont : Continuous (uncurry hx)) (hell : 0 < ell)
    (hC : ∀ t x, |hx t x| ≤ C t) (hCc : Continuous C)
    (hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0) (hT : 0 < T) (t u : ℝ) :
    flowDeriv hx Phi ell t u ≤ ell * Real.exp (∫ s in (0 : ℝ)..T, C s) := by
  have hgc : Continuous fun s => hx s (Phi s u) :=
    continuous_hx_flow hPhid hxcont u
  have hbd : |∫ s in (0 : ℝ)..t, hx s (Phi s u)| ≤ ∫ s in (0 : ℝ)..T, C s :=
    abs_intervalIntegral_le_of_stop hgc hCc (fun s => hC s (Phi s u)) hCstop hT t
  have hle : (∫ s in (0 : ℝ)..t, hx s (Phi s u)) ≤ ∫ s in (0 : ℝ)..T, C s :=
    (le_abs_self _).trans hbd
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hell.le

/-- **The second derivative of a gauge marking in its initial condition is
bounded by the total masses of two densities dominating the first two space
derivatives of the field.** -/
theorem abs_flowDeriv2_le_of_bound (hxcont : Continuous (uncurry hx))
    (hxxcont : Continuous (uncurry hxx)) (hell : 0 < ell)
    (hC : ∀ t x, |hx t x| ≤ C t) (hCc : Continuous C)
    (hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0)
    (hC2 : ∀ t x, |hxx t x| ≤ C2 t) (hC2c : Continuous C2)
    (hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, C2 s = 0) (hT : 0 < T) (t u : ℝ) :
    |flowDeriv2 hx hxx Phi ell t u|
      ≤ (ell * Real.exp (∫ s in (0 : ℝ)..T, C s)) ^ 2 * ∫ s in (0 : ℝ)..T, C2 s := by
  set P1 : ℝ := ell * Real.exp (∫ s in (0 : ℝ)..T, C s) with hP1def
  have hP1nn : 0 ≤ P1 := by positivity
  have hflow : ∀ r, flowDeriv hx Phi ell r u ≤ P1 := fun r =>
    flowDeriv_le_of_bound hPhid hxcont hell hC hCc hCstop hT r u
  have hflowpos : ∀ r, 0 < flowDeriv hx Phi ell r u := fun r => flowDeriv_pos hell r u
  -- the integrand of the second derivative
  have hgc : Continuous fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u :=
    (hxxcont.comp (continuous_id.prodMk (continuous_flow_time hPhid u))).mul
      (FlowDerivative.continuous_flowDeriv_time hPhid hxcont u)
  have hbd : ∀ s, |hxx s (Phi s u) * flowDeriv hx Phi ell s u| ≤ C2 s * P1 := by
    intro s
    rw [abs_mul, abs_of_pos (hflowpos s)]
    exact mul_le_mul (hC2 s (Phi s u)) (hflow s) (hflowpos s).le
      ((abs_nonneg _).trans (hC2 s (Phi s u)))
  have hint : |∫ s in (0 : ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ ∫ s in (0 : ℝ)..T, C2 s * P1 :=
    abs_intervalIntegral_le_of_stop hgc
      (show Continuous fun s => C2 s * P1 from hC2c.mul continuous_const) hbd
      (fun s hs => by simp [hC2stop s hs]) hT t
  have hmul : (∫ s in (0 : ℝ)..T, C2 s * P1) = (∫ s in (0 : ℝ)..T, C2 s) * P1 :=
    intervalIntegral.integral_mul_const _ _
  rw [hmul] at hint
  have hIC2nn : 0 ≤ ∫ s in (0 : ℝ)..T, C2 s :=
    intervalIntegral.integral_nonneg hT.le fun s _ =>
      (abs_nonneg _).trans (hC2 s 0)
  calc |flowDeriv2 hx hxx Phi ell t u|
      = flowDeriv hx Phi ell t u
        * |∫ s in (0 : ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u| := by
        rw [flowDeriv2, abs_mul, abs_of_pos (hflowpos t)]
    _ ≤ P1 * ((∫ s in (0 : ℝ)..T, C2 s) * P1) :=
        mul_le_mul (hflow t) hint (abs_nonneg _) hP1nn
    _ = P1 ^ 2 * ∫ s in (0 : ℝ)..T, C2 s := by ring

end

/-! ### The constants of the cost -/

/-- The bound for the first flow derivative, as a function of the total cost. -/
def costP1 (ell kappa M : ℝ) : ℝ := ell * Real.exp (kappa * M)

/-- The bound for the second flow derivative, as a function of the total cost. -/
def costG1 (ell kappa kappa2 M : ℝ) : ℝ := costP1 ell kappa M ^ 2 * (kappa2 * M)

/-- Uniform first-flow ceiling from a common period and total-cost bound. -/
theorem costP1_le {ell Q kappa M Mtot : ℝ}
    (hell : 0 ≤ ell) (hellQ : ell ≤ Q) (hk : 0 ≤ kappa)
    (hM : 0 ≤ M) (hMM : M ≤ Mtot) :
    costP1 ell kappa M ≤ costP1 Q kappa Mtot := by
  unfold costP1
  have he : Real.exp (kappa * M) ≤ Real.exp (kappa * Mtot) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hMM hk)
  have hQ : 0 ≤ Q := hell.trans hellQ
  exact mul_le_mul hellQ he (Real.exp_pos _).le hQ

/-- Uniform second-flow ceiling from common period and total-cost bounds. -/
theorem costG1_le {ell Q kappa kappa2 M Mtot : ℝ}
    (hell : 0 ≤ ell) (hellQ : ell ≤ Q) (hk : 0 ≤ kappa)
    (hk2 : 0 ≤ kappa2) (hM : 0 ≤ M) (hMM : M ≤ Mtot) :
    costG1 ell kappa kappa2 M ≤ costG1 Q kappa kappa2 Mtot := by
  unfold costG1
  have hp := costP1_le hell hellQ hk hM hMM
  have hp0 : 0 ≤ costP1 ell kappa M := by unfold costP1; positivity
  have hpQ0 : 0 ≤ costP1 Q kappa Mtot := le_trans hp0 hp
  have hsquare : costP1 ell kappa M ^ 2 ≤ costP1 Q kappa Mtot ^ 2 :=
    (sq_le_sq₀ hp0 hpQ0).2 hp
  have hlast : kappa2 * M ≤ kappa2 * Mtot := mul_le_mul_of_nonneg_left hMM hk2
  exact mul_le_mul hsquare hlast (mul_nonneg hk2 hM) (sq_nonneg _)

/-- The mixed variable-speed constant is uniformly bounded by replacing the
rear period and accumulated path cost with their common ceilings. -/
theorem mixedCost_le {ell Q kappa kappa2 M Mtot : ℝ}
    (hell : 0 ≤ ell) (hellQ : ell ≤ Q) (hk : 0 ≤ kappa)
    (hk2 : 0 ≤ kappa2) (hM : 0 ≤ M) (hMM : M ≤ Mtot) :
    kappa * costG1 ell kappa kappa2 M +
        kappa2 * costP1 ell kappa M ^ 2
      ≤ kappa * costG1 Q kappa kappa2 Mtot +
        kappa2 * costP1 Q kappa Mtot ^ 2 := by
  have hg := costG1_le hell hellQ hk hk2 hM hMM
  have hp := costP1_le hell hellQ hk hM hMM
  have hp0 : 0 ≤ costP1 ell kappa M := by unfold costP1; positivity
  have hpQ0 : 0 ≤ costP1 Q kappa Mtot := le_trans hp0 hp
  exact add_le_add (mul_le_mul_of_nonneg_left hg hk)
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hp0 hpQ0).2 hp) hk2)

theorem costP1_pos {ell kappa M : ℝ} (hell : 0 < ell) : 0 < costP1 ell kappa M :=
  mul_pos hell (Real.exp_pos _)

section

variable (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)

include hPhid

/-- **The first flow derivative of the gauge marking of a normal path is bounded
by `costP1`**: the field's space derivative is dominated by `κ` times the cost
density, so the primitive is at most `κ` times the total cost. -/
theorem flowDeriv_le_costP1 {kappa : ℝ} (hxcont : Continuous (uncurry hx)) (hell : 0 < ell)
    (hC : ∀ t x, |hx t x| ≤ C t) (hCc : Continuous C)
    (hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0)
    (hmc : Continuous m) (hCm : ∀ t, C t ≤ kappa * m t) (hT : 0 < T) (t u : ℝ) :
    flowDeriv hx Phi ell t u ≤ costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) := by
  have h1 : flowDeriv hx Phi ell t u ≤ ell * Real.exp (∫ s in (0 : ℝ)..T, C s) :=
    flowDeriv_le_of_bound hPhid hxcont hell hC hCc hCstop hT t u
  have h2 : (∫ s in (0 : ℝ)..T, C s) ≤ kappa * ∫ s in (0 : ℝ)..T, m s :=
    integral_le_const_mul hCc hmc hCm hT
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hell.le

/-- **The second flow derivative of the gauge marking of a normal path is
bounded by `costG1`.** -/
theorem abs_flowDeriv2_le_costG1 {kappa kappa2 : ℝ} (hxcont : Continuous (uncurry hx))
    (hxxcont : Continuous (uncurry hxx)) (hell : 0 < ell)
    (hC : ∀ t x, |hx t x| ≤ C t) (hCc : Continuous C)
    (hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0)
    (hC2 : ∀ t x, |hxx t x| ≤ C2 t) (hC2c : Continuous C2)
    (hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, C2 s = 0)
    (hmc : Continuous m) (hCm : ∀ t, C t ≤ kappa * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    (hT : 0 < T) (t u : ℝ) :
    |flowDeriv2 hx hxx Phi ell t u|
      ≤ costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s) := by
  have h1 : |flowDeriv2 hx hxx Phi ell t u|
      ≤ (ell * Real.exp (∫ s in (0 : ℝ)..T, C s)) ^ 2 * ∫ s in (0 : ℝ)..T, C2 s :=
    abs_flowDeriv2_le_of_bound hPhid hxcont hxxcont hell hC hCc hCstop hC2 hC2c hC2stop hT t u
  have hexp : ell * Real.exp (∫ s in (0 : ℝ)..T, C s)
      ≤ costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) := by
    have h2 : (∫ s in (0 : ℝ)..T, C s) ≤ kappa * ∫ s in (0 : ℝ)..T, m s :=
      integral_le_const_mul hCc hmc hCm hT
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hell.le
  have hIC2 : (∫ s in (0 : ℝ)..T, C2 s) ≤ kappa2 * ∫ s in (0 : ℝ)..T, m s :=
    integral_le_const_mul hC2c hmc hC2m hT
  have hIC2nn : 0 ≤ ∫ s in (0 : ℝ)..T, C2 s :=
    intervalIntegral.integral_nonneg hT.le fun s _ => (abs_nonneg _).trans (hC2 s 0)
  have hPnn : 0 ≤ ell * Real.exp (∫ s in (0 : ℝ)..T, C s) := by positivity
  refine h1.trans ?_
  calc (ell * Real.exp (∫ s in (0 : ℝ)..T, C s)) ^ 2 * ∫ s in (0 : ℝ)..T, C2 s
      ≤ costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) ^ 2 * ∫ s in (0 : ℝ)..T, C2 s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPnn hexp 2) hIC2nn
    _ ≤ costP1 ell kappa (∫ s in (0 : ℝ)..T, m s) ^ 2
          * (kappa2 * ∫ s in (0 : ℝ)..T, m s) :=
        mul_le_mul_of_nonneg_left hIC2 (by positivity)
    _ = costG1 ell kappa kappa2 (∫ s in (0 : ℝ)..T, m s) := rfl

end

/-! ### Global bounds from a density supported in the window -/

/-- A continuous nonnegative density vanishing outside the time window is
globally bounded. -/
theorem exists_bound_of_stop (hCc : Continuous C) (hCnn : ∀ s, 0 ≤ C s)
    (hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, C s ≤ B := by
  obtain ⟨x0, hx0mem, hx0max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hT.le) hCc.continuousOn
  refine ⟨C x0, hCnn x0, fun s => ?_⟩
  by_cases hs : s ∈ Icc (0 : ℝ) T
  · exact hx0max hs
  · rw [hCstop s fun hmem => hs ⟨hmem.1.le, hmem.2.le⟩]
    exact hCnn x0

/-- A field whose space derivative is globally bounded by `B` is `B`-Lipschitz
in the space variable, at every time. -/
theorem lipschitzWith_of_deriv_bound {B : ℝ} (hB : 0 ≤ B)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hb : ∀ s x, |hx s x| ≤ B) (t : ℝ) :
    LipschitzWith (Real.toNNReal B) (h t) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hxd t x).differentiableAt) (fun x => ?_)
  rw [(hxd t x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB,
    Real.norm_eq_abs]
  exact hb t x

end GaugeFlowDerivCost
