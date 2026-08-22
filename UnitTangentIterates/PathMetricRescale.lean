import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.JacobiNormalized
import UnitTangentIterates.PathMetricCircle

/-!
# Rescaling the time of a normal path

The cost `∫₀^T m` of a normal path is a *length*: it does not change when the
time is run faster or slower.  This file makes that precise.

For `a > 0` the path `Γ.rescale ha` runs `Γ` at speed `a`: it is defined on
`[0, T/a]`, its curve is `X(a t)`, its normal velocity is `a η(a t)` — the
chain rule — and its cost density is `a m(a t)`.  All the requirements of a
normal path are preserved (`rescale`), and the cost is unchanged
(`cost_rescale`).

Two consequences:

* `exists_unitTime_normalPath` — every normal path can be run over the unit
  time interval, at the same cost; hence
  `pathDist_eq_sInf_unitTime`, the path pseudodistance is already the infimum
  of the costs of the normal paths of duration one;
* `pathDist_le_mul_of_maps_unitTime_paths` — consequently, in the Lipschitz
  criterion `PathMetric.pathDist_le_mul_of_maps_paths` it is enough to control
  the image of the normal paths **of duration one**.  This is what makes the
  criterion usable with a constant that grows with the duration of the path, as
  the distortion `exp(L T)` of a gauge flow does.
-/

noncomputable section

open Set MeasureTheory MarkedSpace MarkedTopology

namespace PathMetric

namespace NormalPath

variable {p q : Data}

/-- **Running a normal path at speed `a`.**  The reparametrized path is defined
on `[0, T/a]`, moves with the normal velocity `a η(a t)` and has cost density
`a m(a t)`. -/
def rescale (Γ : NormalPath p q) {a : ℝ} (ha : 0 < a) : NormalPath p q where
  T := Γ.T / a
  T_pos := div_pos Γ.T_pos ha
  X := fun t u => Γ.X (a * t) u
  eta := fun t u => a * Γ.eta (a * t) u
  nu := fun t u => Γ.nu (a * t) u
  m := fun t => a * Γ.m (a * t)
  start := fun u => by simpa using Γ.start u
  finish := fun u => by
    rw [mul_div_cancel₀ _ (ne_of_gt ha)]
    exact Γ.finish u
  hasDerivAt_time := fun t u => by
    have hin : HasDerivAt (fun t : ℝ => a * t) a t := by
      simpa using (hasDerivAt_id t).const_mul a
    have h := (Γ.hasDerivAt_time (a * t) u).scomp t hin
    refine h.congr_deriv ?_
    push_cast [Complex.real_smul]
    ring
  cont_vel := fun u => by
    have hc : Continuous fun t : ℝ => a * t := continuous_const.mul continuous_id
    have h : Continuous fun t : ℝ => (a : ℂ) * ((Γ.eta (a * t) u : ℂ) * Γ.nu (a * t) u) :=
      continuous_const.mul ((Γ.cont_vel u).comp hc)
    simpa [Complex.ofReal_mul, mul_assoc] using h
  norm_nu := fun t u => Γ.norm_nu (a * t) u
  cont_m := continuous_const.mul ((Γ.cont_m).comp (continuous_const.mul continuous_id))
  m_nonneg := fun t => mul_nonneg ha.le (Γ.m_nonneg _)
  m_stop := fun t ht => by
    have h : a * t ∉ Ioo (0:ℝ) Γ.T := by
      intro hmem
      refine ht ⟨?_, ?_⟩
      · nlinarith [hmem.1]
      · rw [lt_div_iff₀ ha, mul_comm]
        exact hmem.2
    rw [Γ.m_stop _ h, mul_zero]
  abs_eta_le := fun t u => by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (Γ.abs_eta_le _ u) ha.le
  le_m_L1 := fun t => by
    have h : (∫ u in (0:ℝ)..1, |a * Γ.eta (a * t) u|)
        = a * ∫ u in (0:ℝ)..1, |Γ.eta (a * t) u| := by
      simp only [abs_mul, abs_of_pos ha]
      exact intervalIntegral.integral_const_mul _ _
    rw [h]
    exact mul_le_mul_of_nonneg_left (Γ.le_m_L1 _) ha.le
  le_m_sup := fun t j hj => by
    have h : iteratedDeriv j (fun u => a * Γ.eta (a * t) u)
        = fun u => a * iteratedDeriv j (Γ.eta (a * t)) u := by
      funext u
      exact iteratedDeriv_const_mul_field a (Γ.eta (a * t))
    rw [h, JacobiNormalized.supNorm_const_mul ha.le]
    exact mul_le_mul_of_nonneg_left (Γ.le_m_sup _ j hj) ha.le

@[simp] theorem T_rescale (Γ : NormalPath p q) {a : ℝ} (ha : 0 < a) :
    (Γ.rescale ha).T = Γ.T / a := rfl

/-- **The cost is invariant under a rescaling of the time.** -/
theorem cost_rescale (Γ : NormalPath p q) {a : ℝ} (ha : 0 < a) :
    cost (Γ.rescale ha) = cost Γ := by
  have hane : a ≠ 0 := ne_of_gt ha
  have h1 : cost (Γ.rescale ha) = ∫ t in (0:ℝ)..(Γ.T / a), a * Γ.m (a * t) := rfl
  have h2 : (∫ t in (0:ℝ)..(Γ.T / a), Γ.m (a * t))
      = a⁻¹ • ∫ x in (a * 0)..(a * (Γ.T / a)), Γ.m x :=
    intervalIntegral.integral_comp_mul_left (fun x => Γ.m x) hane
  rw [h1, intervalIntegral.integral_const_mul, h2, mul_zero,
    mul_div_cancel₀ _ hane, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hane, one_mul]
  rfl

/-- **Every normal path can be run over the unit time interval**, at the same
cost. -/
theorem exists_unitTime_normalPath (Γ : NormalPath p q) :
    ∃ Δ : NormalPath p q, Δ.T = 1 ∧ cost Δ = cost Γ := by
  refine ⟨Γ.rescale Γ.T_pos, ?_, cost_rescale Γ Γ.T_pos⟩
  simp [T_rescale, div_self (ne_of_gt Γ.T_pos)]

end NormalPath

open NormalPath

/-- The set of costs of the normal paths of duration one. -/
def unitTimeCostSet (p q : Data) : Set ℝ := {c | ∃ Γ : NormalPath p q, Γ.T = 1 ∧ cost Γ = c}

/-- **The path pseudodistance is the infimum of the costs of the normal paths of
duration one**: rescaling the time changes neither the endpoints nor the cost. -/
theorem pathDist_eq_sInf_unitTime (p q : Data) :
    pathDist p q = sInf (unitTimeCostSet p q) := by
  have hsub : unitTimeCostSet p q ⊆ costSet p q := by
    rintro c ⟨Γ, -, rfl⟩
    exact ⟨Γ, rfl⟩
  have hbdd : BddBelow (unitTimeCostSet p q) := (bddBelow_costSet p q).mono hsub
  by_cases hne : (costSet p q).Nonempty
  · obtain ⟨c₀, Γ₀, rfl⟩ := hne
    have hne' : (unitTimeCostSet p q).Nonempty := by
      obtain ⟨Δ, hT, hc⟩ := Γ₀.exists_unitTime_normalPath
      exact ⟨cost Δ, Δ, hT, rfl⟩
    refine le_antisymm (le_csInf hne' ?_) (le_csInf ⟨cost Γ₀, Γ₀, rfl⟩ ?_)
    · rintro c ⟨Γ, -, rfl⟩
      exact pathDist_le_cost Γ
    · rintro c ⟨Γ, rfl⟩
      obtain ⟨Δ, hT, hc⟩ := Γ.exists_unitTime_normalPath
      exact le_trans (csInf_le hbdd ⟨Δ, hT, rfl⟩) hc.le
  · have h1 : costSet p q = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h2 : unitTimeCostSet p q = ∅ :=
      Set.eq_empty_of_subset_empty (h1 ▸ hsub)
    rw [pathDist, h1, h2]

/-- **The Lipschitz criterion, tested on the paths of duration one.**  A map of
marked curves which takes every normal path from `p` to `q` **of duration one**
to a normal path of cost at most `C` times as large is `C`-Lipschitz for the
path pseudodistance.

This is the form in which a constant that grows with the duration of the path —
such as the distortion `exp(L T)` of a gauge flow — can still be used: it is
enough to bound it at `T = 1`. -/
theorem pathDist_le_mul_of_maps_unitTime_paths {F : Data → Data} {p q : Data} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → ∃ Γ' : NormalPath (F p) (F q), cost Γ' ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ C * pathDist p q := by
  refine pathDist_le_mul_of_maps_paths hC (fun Γ => ?_) hne
  obtain ⟨Δ, hT, hc⟩ := Γ.exists_unitTime_normalPath
  obtain ⟨Γ', hΓ'⟩ := h Δ hT
  exact ⟨Γ', by rw [← hc]; exact hΓ'⟩

/-- **The rescaling is not vacuous.**  The radial dilation of one concentric
circle onto another, run at any speed `a > 0` — hence over the time interval
`[0, 1/a]` — still has cost the difference of the radii. -/
example (r R a : ℝ) (ha : 0 < a) :
    ((PathMetricCircle.dilation r R).rescale ha).T = 1 / a ∧
      cost ((PathMetricCircle.dilation r R).rescale ha) = |R - r| := by
  refine ⟨rfl, ?_⟩
  rw [NormalPath.cost_rescale, PathMetricCircle.cost_dilation]

end PathMetric
