import Mathlib
import UnitTangentIterates.Shadowing
import UnitTangentIterates.MarkedTopology

/-!
# The stopped curvature estimate, assembled

This file assembles the lemma *Stopped curvature estimate* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

> Let `Γ = (C_t)_{0 ≤ t ≤ 1}` be a smooth path in normal gauge, `X_t = ην`.
> If `max κ_{C_0} ≤ κ_b < κ_e` and `S₂(Γ) + κ_e²S₀(Γ) < κ_e − κ_b`, then
> `max κ_{C_t} < κ_e` for every `t`.

The mechanism is the exit-time argument `Shadowing.stopped_curvature`; the
input is the normal-flow identity `κ_t = η_ss + κ²η` of `NormalFlow.lean`,
integrated in time.  Here `m₀` and `m₂` are the sup norms `‖η_t‖_∞` and
`‖∂_s²η_t‖_∞`, so that `S₀ = ∫₀¹ m₀` and `S₂ = ∫₀¹ m₂` are the path
functionals of `MarkedTopology.lean`.

* `curvature_move_le` : as long as the curvature has stayed below the ceiling,
  it has moved by at most `S₂ + κ_e²S₀`;
* `stopped_curvature_path` : the lemma itself.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace StoppedCurvature

variable {kappa eta etass : ℝ → ℝ → ℝ} {m0 m2 : ℝ → ℝ} {ke S0 S2 : ℝ}

/-- **The curvature moves by at most `S₂ + κ_e²S₀` while it stays below the
ceiling.**  Along the normal flow `κ_t = η_ss + κ²η`, if `0 ≤ κ ≤ κ_e` on
`[0, τ)` then `|κ(τ) − κ(0)| ≤ S₂ + κ_e²S₀`. -/
theorem curvature_move_le {u tau : ℝ}
    (hderiv : ∀ t x, HasDerivAt (fun t => kappa t x) (etass t x + (kappa t x) ^ 2 * eta t x) t)
    (hint : ∀ x, IntervalIntegrable
      (fun r => etass r x + (kappa r x) ^ 2 * eta r x) volume 0 1)
    (hm0 : ∀ r x, |eta r x| ≤ m0 r) (hm2 : ∀ r x, |etass r x| ≤ m2 r)
    (hm0int : IntervalIntegrable m0 volume 0 1) (hm2int : IntervalIntegrable m2 volume 0 1)
    (hS0 : S0 = ∫ r in (0:ℝ)..1, m0 r) (hS2 : S2 = ∫ r in (0:ℝ)..1, m2 r)
    (hnonneg : ∀ r x, 0 ≤ kappa r x)
    (htau : tau ∈ Icc (0:ℝ) 1) (hbelow : ∀ r ∈ Ico (0:ℝ) tau, kappa r u ≤ ke) :
    |kappa tau u - kappa 0 u| ≤ S2 + ke ^ 2 * S0 := by
  obtain ⟨htau0, htau1⟩ := htau
  have hsubset : uIcc (0:ℝ) tau ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le htau0, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl htau1
  have hm0nonneg : ∀ r, 0 ≤ m0 r := fun r => le_trans (abs_nonneg _) (hm0 r u)
  have hm2nonneg : ∀ r, 0 ≤ m2 r := fun r => le_trans (abs_nonneg _) (hm2 r u)
  have hintτ : IntervalIntegrable
      (fun r => etass r u + (kappa r u) ^ 2 * eta r u) volume 0 tau :=
    (hint u).mono_set hsubset
  have hsub : (∫ r in (0:ℝ)..tau, (etass r u + (kappa r u) ^ 2 * eta r u))
      = kappa tau u - kappa 0 u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t u) hintτ
  have hbdint1 : IntervalIntegrable (fun r => m2 r + ke ^ 2 * m0 r) volume 0 1 :=
    hm2int.add (hm0int.const_mul (ke ^ 2))
  have hbdint : IntervalIntegrable (fun r => m2 r + ke ^ 2 * m0 r) volume 0 tau :=
    hbdint1.mono_set hsubset
  have hae : ∀ᵐ r : ℝ, r ≠ tau := by
    rw [MeasureTheory.ae_iff]
    simp
  have hbound : ‖∫ r in (0:ℝ)..tau, (etass r u + (kappa r u) ^ 2 * eta r u)‖
      ≤ ∫ r in (0:ℝ)..tau, (m2 r + ke ^ 2 * m0 r) := by
    refine intervalIntegral.norm_integral_le_of_norm_le htau0 ?_ hbdint
    filter_upwards [hae] with r hrne hr
    have hrmem : r ∈ Ico (0:ℝ) tau := ⟨le_of_lt hr.1, lt_of_le_of_ne hr.2 hrne⟩
    have hkle : kappa r u ≤ ke := hbelow r hrmem
    have hk0 : 0 ≤ kappa r u := hnonneg r u
    have hsq : (kappa r u) ^ 2 ≤ ke ^ 2 := by nlinarith
    calc ‖etass r u + (kappa r u) ^ 2 * eta r u‖
        = |etass r u + (kappa r u) ^ 2 * eta r u| := Real.norm_eq_abs _
      _ ≤ |etass r u| + |(kappa r u) ^ 2 * eta r u| :=
          abs_add_le (etass r u) ((kappa r u) ^ 2 * eta r u)
      _ = |etass r u| + (kappa r u) ^ 2 * |eta r u| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (kappa r u))]
      _ ≤ m2 r + ke ^ 2 * m0 r := by
          have h1 := hm2 r u
          have h2 := hm0 r u
          have habs : 0 ≤ |eta r u| := abs_nonneg _
          have h3 : (kappa r u) ^ 2 * |eta r u| ≤ ke ^ 2 * m0 r := by nlinarith
          linarith
  have hmono : (∫ r in (0:ℝ)..tau, (m2 r + ke ^ 2 * m0 r))
      ≤ ∫ r in (0:ℝ)..1, (m2 r + ke ^ 2 * m0 r) := by
    refine intervalIntegral.integral_mono_interval le_rfl htau0 htau1 ?_ hbdint1
    filter_upwards with r
    have h1 := hm0nonneg r
    have h2 := hm2nonneg r
    have h3 : 0 ≤ ke ^ 2 * m0 r := mul_nonneg (sq_nonneg ke) h1
    simpa using by linarith
  have hsplit : (∫ r in (0:ℝ)..1, (m2 r + ke ^ 2 * m0 r)) = S2 + ke ^ 2 * S0 := by
    rw [intervalIntegral.integral_add hm2int (hm0int.const_mul (ke ^ 2)),
      intervalIntegral.integral_const_mul, hS0, hS2]
  rw [hsub] at hbound
  calc |kappa tau u - kappa 0 u| = ‖kappa tau u - kappa 0 u‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ r in (0:ℝ)..tau, (m2 r + ke ^ 2 * m0 r) := hbound
    _ ≤ ∫ r in (0:ℝ)..1, (m2 r + ke ^ 2 * m0 r) := hmono
    _ = S2 + ke ^ 2 * S0 := hsplit

/-- **The stopped curvature estimate.**  Along a normal path with
`κ_t = η_ss + κ²η` and nonnegative curvature, if the initial curvature is at
most `κ_b < κ_e` and `S₂ + κ_e²S₀ < κ_e − κ_b`, then the curvature stays
strictly below `κ_e` for the whole path. -/
theorem stopped_curvature_path {kb : ℝ}
    (hderiv : ∀ t x, HasDerivAt (fun t => kappa t x) (etass t x + (kappa t x) ^ 2 * eta t x) t)
    (hint : ∀ x, IntervalIntegrable
      (fun r => etass r x + (kappa r x) ^ 2 * eta r x) volume 0 1)
    (hm0 : ∀ r x, |eta r x| ≤ m0 r) (hm2 : ∀ r x, |etass r x| ≤ m2 r)
    (hm0int : IntervalIntegrable m0 volume 0 1) (hm2int : IntervalIntegrable m2 volume 0 1)
    (hS0 : S0 = ∫ r in (0:ℝ)..1, m0 r) (hS2 : S2 = ∫ r in (0:ℝ)..1, m2 r)
    (hnonneg : ∀ r x, 0 ≤ kappa r x)
    (hinit : ∀ x, kappa 0 x ≤ kb)
    (hsmall : S2 + ke ^ 2 * S0 < ke - kb) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ u, kappa t u < ke := by
  intro t ht u
  have hcontk : Continuous fun s => kappa s u :=
    continuous_iff_continuousAt.2 (fun s => (hderiv s u).differentiableAt.continuousAt)
  -- the path stopped at time `1`
  set g : ℝ → ℝ := fun s => kappa (min s 1) u with hg
  have hgcont : Continuous g := hcontk.comp (continuous_id.min continuous_const)
  have hg0 : g 0 ≤ kb := by simpa [hg] using hinit u
  have hmove : ∀ s, 0 ≤ s → (∀ r ∈ Ico (0:ℝ) s, g r ≤ ke) →
      |g s - g 0| ≤ S2 + ke ^ 2 * S0 := by
    intro s hs hbelow
    have hmin : min s 1 ∈ Icc (0:ℝ) 1 := ⟨le_min hs zero_le_one, min_le_right _ _⟩
    have hbelow' : ∀ r ∈ Ico (0:ℝ) (min s 1), kappa r u ≤ ke := by
      intro r hr
      have hrs : r < s := lt_of_lt_of_le hr.2 (min_le_left _ _)
      have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hr.2 (min_le_right _ _))
      have := hbelow r ⟨hr.1, hrs⟩
      simpa [hg, min_eq_left hr1] using this
    have hkey := curvature_move_le (u := u) (tau := min s 1) hderiv hint hm0 hm2
      hm0int hm2int hS0 hS2 hnonneg hmin hbelow'
    have hg0' : g 0 = kappa 0 u := by simp [hg]
    rw [show g s = kappa (min s 1) u from rfl, hg0']
    exact hkey
  have hall := Shadowing.stopped_curvature hgcont hg0 hsmall hmove
  have hlt := hall t ht.1
  simpa [hg, min_eq_left ht.2] using hlt

end StoppedCurvature
