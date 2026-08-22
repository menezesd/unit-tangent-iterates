import Mathlib
import UnitTangentIterates.GlobalODE

/-!
# Global solutions of a globally Lipschitz ODE, without a bound on the field

`GlobalODE.lean` produces global solutions of `φ' = h(t, φ)` for a field which
is globally Lipschitz in the state **and globally bounded**.  The boundedness is
not needed: a field which is globally Lipschitz in the state and continuous in
the time has, for every initial condition, a solution on the whole line.

This is what the normal gauge of a family of *closed* curves whose length
changes requires.  The tangential rate of such a family is not periodic in the
arclength — the closing relation makes it drift by `Q'(t)` over each period — so
it is unbounded, while its arclength derivatives stay periodic and hence
bounded, which is exactly a globally Lipschitz, unbounded field.

The proof is the usual one.  On a compact window of times the solution cannot
leave an explicit interval, by Grönwall: from `|φ'| ≤ M + K|φ − x₀|` and
`φ(t₀) = x₀`,

`|φ(t) − x₀| ≤ M |t − t₀| e^{K|t − t₀|}`.

Truncating the field outside that interval (and outside the window in the time)
makes it bounded, so `GlobalODE.exists_global_solution_real` applies; the
resulting solution stays where the truncation is inactive, hence solves the
original equation on the window.  `GlobalODE.exists_global_solution_of_windows`
glues the windows.

Main results:

* `abs_sub_le_of_deriv_bound` — the Grönwall a priori bound;
* `exists_global_solution_real_of_lipschitz` — global existence.
-/

noncomputable section

open Set

namespace GlobalODEGrowth

/-! ### The a priori bound -/

/-- The Grönwall a priori bound, forward in time: a solution whose derivative
grows at most affinely in its distance to `x₀` stays within
`M s e^{Ks}` of `x₀` after a time `s`. -/
theorem abs_sub_le_of_deriv_bound_right {x0 M K t0 : ℝ} {φ φ' : ℝ → ℝ} (hK : 0 ≤ K)
    (hd : ∀ t, HasDerivAt φ (φ' t) t) (hφ0 : φ t0 = x0)
    (hb : ∀ t, |φ' t| ≤ M + K * |φ t - x0|) {s : ℝ} (hs : 0 ≤ s) :
    |φ (t0 + s) - x0| ≤ M * s * Real.exp (K * s) := by
  set f : ℝ → ℝ := fun r => φ (t0 + r) - x0 with hf
  set f' : ℝ → ℝ := fun r => φ' (t0 + r) with hf'
  have hfd : ∀ r, HasDerivAt f (f' r) r := by
    intro r
    have := (hd (t0 + r)).comp r ((hasDerivAt_id r).const_add t0)
    simpa [hf, hf'] using this.sub_const x0
  have hdiff : Differentiable ℝ f := fun r => (hfd r).differentiableAt
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f') (δ := 0)
    (K := K) (ε := M) (a := 0) (b := s) hdiff.continuous.continuousOn
    (fun r _ => (hfd r).hasDerivWithinAt) (by simp [hf, hφ0]) ?_ s (right_mem_Icc.mpr hs)
  · simp only [sub_zero] at key
    have hgb : gronwallBound 0 K M s ≤ M * s * Real.exp (K * s) := by
      rcases eq_or_ne K 0 with hK0 | hK0
      · subst hK0; simp [gronwallBound_K0]
      · rw [gronwallBound_of_K_ne_0 hK0]
        have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
        have h1 : Real.exp (K * s) - 1 ≤ K * s * Real.exp (K * s) := by
          have h2 := Real.add_one_le_exp (-(K * s))
          have hexp : Real.exp (-(K * s)) = 1 / Real.exp (K * s) := by
            rw [Real.exp_neg]; ring
          rw [hexp] at h2
          have hpos : 0 < Real.exp (K * s) := Real.exp_pos _
          rw [le_div_iff₀ hpos] at h2
          nlinarith
        have hM : 0 ≤ M := by
          have h6 := hb t0
          have h0 : |φ t0 - x0| = 0 := by rw [hφ0]; simp
          rw [h0] at h6
          have := le_trans (abs_nonneg (φ' t0)) h6
          simpa using this
        have h3 : M / K * (Real.exp (K * s) - 1) ≤ M / K * (K * s * Real.exp (K * s)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h4 : M / K * (K * s * Real.exp (K * s)) = M * s * Real.exp (K * s) := by
          field_simp
        calc 0 * Real.exp (K * s) + M / K * (Real.exp (K * s) - 1)
            ≤ M / K * (K * s * Real.exp (K * s)) := by linarith
          _ = M * s * Real.exp (K * s) := h4
    calc |f s| = ‖f s‖ := rfl
      _ ≤ gronwallBound 0 K M s := key
      _ ≤ M * s * Real.exp (K * s) := hgb
  · intro r _
    have h5 := hb (t0 + r)
    simp only [hf, hf', Real.norm_eq_abs]
    linarith [h5]

/-- **The Grönwall a priori bound**, on both sides of the initial time. -/
theorem abs_sub_le_of_deriv_bound {x0 M K t0 : ℝ} {φ φ' : ℝ → ℝ} (hK : 0 ≤ K)
    (hd : ∀ t, HasDerivAt φ (φ' t) t) (hφ0 : φ t0 = x0)
    (hb : ∀ t, |φ' t| ≤ M + K * |φ t - x0|) (t : ℝ) :
    |φ t - x0| ≤ M * |t - t0| * Real.exp (K * |t - t0|) := by
  rcases le_total t0 t with hle | hle
  · have hs : 0 ≤ t - t0 := by linarith
    have := abs_sub_le_of_deriv_bound_right hK hd hφ0 hb hs
    rw [abs_of_nonneg hs]
    simpa using this
  · -- reflect the time
    set ψ : ℝ → ℝ := fun r => φ (2 * t0 - r) with hψ
    set ψ' : ℝ → ℝ := fun r => -φ' (2 * t0 - r) with hψ'
    have hψd : ∀ r, HasDerivAt ψ (ψ' r) r := by
      intro r
      have hin : HasDerivAt (fun r : ℝ => 2 * t0 - r) (-1) r := by
        simpa using (hasDerivAt_const r (2 * t0)).sub (hasDerivAt_id r)
      have := (hd (2 * t0 - r)).comp r hin
      simpa [hψ, hψ', mul_comm] using this
    have hψ0 : ψ t0 = x0 := by simp [hψ, show 2 * t0 - t0 = t0 by ring, hφ0]
    have hψb : ∀ r, |ψ' r| ≤ M + K * |ψ r - x0| := by
      intro r
      have := hb (2 * t0 - r)
      simpa [hψ, hψ'] using this
    have hs : 0 ≤ t0 - t := by linarith
    have hmain := abs_sub_le_of_deriv_bound_right hK hψd hψ0 hψb hs
    have heq : ψ (t0 + (t0 - t)) = φ t := by
      simp [hψ, show 2 * t0 - (t0 + (t0 - t)) = t by ring]
    rw [heq] at hmain
    rw [abs_of_nonpos (by linarith : t - t0 ≤ 0), show -(t - t0) = t0 - t by ring]
    exact hmain

/-! ### The truncation -/

/-- The projection of the line onto the interval `[c − R, c + R]`. -/
def clampAt (c R x : ℝ) : ℝ := max (c - R) (min x (c + R))

theorem lipschitzWith_clampAt (c R : ℝ) : LipschitzWith 1 (clampAt c R) := by
  have h1 : LipschitzWith 1 (fun x : ℝ => min x (c + R)) := LipschitzWith.id.min_const _
  simpa [clampAt] using h1.const_max (c - R)

theorem abs_clampAt_sub_le (c R x : ℝ) (hR : 0 ≤ R) : |clampAt c R x - c| ≤ R := by
  rcases le_total x (c - R) with h | h
  · rw [clampAt, min_eq_left (by linarith), max_eq_left h, abs_le]
    constructor <;> linarith
  · rcases le_total x (c + R) with h2 | h2
    · rw [clampAt, min_eq_left h2, max_eq_right (by linarith), abs_le]
      constructor <;> linarith
    · rw [clampAt, min_eq_right h2, max_eq_right (by linarith), abs_le]
      constructor <;> linarith

theorem abs_clampAt_sub_le_abs (c R x : ℝ) (hR : 0 ≤ R) : |clampAt c R x - c| ≤ |x - c| := by
  rcases le_total x (c - R) with h | h
  · rw [clampAt, min_eq_left (by linarith), max_eq_left h, abs_le]
    have hb : R ≤ |x - c| := by rw [le_abs]; right; linarith
    constructor <;> linarith
  · rcases le_total x (c + R) with h2 | h2
    · rw [clampAt, min_eq_left h2, max_eq_right (by linarith)]
    · rw [clampAt, min_eq_right h2, max_eq_right (by linarith), abs_le]
      have hb : R ≤ |x - c| := by rw [le_abs]; left; linarith
      constructor <;> linarith

theorem clampAt_of_abs_le {c R x : ℝ} (h : |x - c| ≤ R) : clampAt c R x = x := by
  rw [abs_le] at h
  rw [clampAt, min_eq_left (by linarith), max_eq_right (by linarith)]

/-! ### Global existence -/

/-- **Global existence for a globally Lipschitz field.**  A scalar field which
is globally Lipschitz in the state and continuous in the time — but not
necessarily bounded — has, for every initial condition, a solution defined on
the whole line. -/
theorem exists_global_solution_real_of_lipschitz {h : ℝ → ℝ → ℝ} {K : NNReal}
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : ∀ x, Continuous fun t => h t x)
    (t₀ x₀ : ℝ) :
    ∃ φ : ℝ → ℝ, φ t₀ = x₀ ∧ ∀ t, HasDerivAt φ (h t (φ t)) t := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  refine GlobalODE.exists_global_solution_of_windows hlip t₀ x₀ (fun n => ?_)
  set tmin : ℝ := t₀ - ((n : ℝ) + 1) with htmin
  set tmax : ℝ := t₀ + ((n : ℝ) + 1) with htmax
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmem : t₀ ∈ Icc tmin tmax := ⟨by rw [htmin]; linarith, by rw [htmax]; linarith⟩
  set T : ℝ := (n : ℝ) + 1 with hT
  have hTpos : 0 < T := by rw [hT]; linarith
  -- the bound for the field along the constant `x₀`, on the window
  obtain ⟨τ, hτ, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc tmin tmax) ⟨t₀, hmem⟩
    ((hcont x₀).abs.continuousOn)
  set M : ℝ := |h τ x₀| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hMbd : ∀ t ∈ Icc tmin tmax, |h t x₀| ≤ M := fun t ht => hmax ht
  -- the radius the solution cannot leave
  set R : ℝ := M * T * Real.exp ((K : ℝ) * T) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  -- the truncated field
  set g : ℝ → ℝ → ℝ := fun t x => h (clampAt t₀ T t) (clampAt x₀ R x) with hg
  have hclampT : ∀ t, clampAt t₀ T t ∈ Icc tmin tmax := by
    intro t
    have := abs_clampAt_sub_le t₀ T t hTpos.le
    rw [abs_le] at this
    exact ⟨by rw [htmin, hT]; linarith [this.1], by rw [htmax, hT]; linarith [this.2]⟩
  have hglip : ∀ t, LipschitzWith K (g t) := by
    intro t
    simpa [hg] using (hlip (clampAt t₀ T t)).comp (lipschitzWith_clampAt x₀ R)
  have hgcont : ∀ x, Continuous fun t => g t x := fun x =>
    (hcont (clampAt x₀ R x)).comp (lipschitzWith_clampAt t₀ T).continuous
  -- the affine bound on the truncated field
  have hgaff0 : ∀ t x, |g t x| ≤ M + (K : ℝ) * |clampAt x₀ R x - x₀| := by
    intro t x
    set c : ℝ := h (clampAt t₀ T t) x₀ with hc
    have hlipx : |g t x - c| ≤ (K : ℝ) * |clampAt x₀ R x - x₀| := by
      have := (hlip (clampAt t₀ T t)).dist_le_mul (clampAt x₀ R x) x₀
      simpa [hg, hc, Real.dist_eq] using this
    have h1 : |c| ≤ M := hMbd _ (hclampT t)
    have h3 : |g t x| ≤ |g t x - c| + |c| := by
      have := abs_add_le (g t x - c) c
      simpa using this
    linarith
  have hgaff : ∀ t x, |g t x| ≤ M + (K : ℝ) * |x - x₀| := by
    intro t x
    have h2 : (K : ℝ) * |clampAt x₀ R x - x₀| ≤ (K : ℝ) * |x - x₀| :=
      mul_le_mul_of_nonneg_left (abs_clampAt_sub_le_abs x₀ R x hR0) hK
    linarith [hgaff0 t x]
  -- the truncated field is bounded, so it has a global solution
  obtain ⟨φ, hφ0, hφd⟩ := GlobalODE.exists_global_solution_real (h := g)
    (K := K) (L := Real.toNNReal (M + (K : ℝ) * R)) hglip hgcont
    (fun t x => by
      rw [Real.coe_toNNReal _ (by positivity)]
      have h2 : (K : ℝ) * |clampAt x₀ R x - x₀| ≤ (K : ℝ) * R :=
        mul_le_mul_of_nonneg_left (abs_clampAt_sub_le x₀ R x hR0) hK
      linarith [hgaff0 t x])
    t₀ x₀
  -- the solution never leaves the interval where the truncation is inactive
  have hbound : ∀ t, |φ t - x₀| ≤ M * |t - t₀| * Real.exp ((K : ℝ) * |t - t₀|) := by
    refine abs_sub_le_of_deriv_bound (φ' := fun t => g t (φ t)) hK hφd hφ0 (fun t => ?_)
    exact hgaff t (φ t)
  refine ⟨φ, hφ0, fun t ht => ?_⟩
  have hwin : |t - t₀| ≤ T := by
    rw [abs_le]
    rw [htmin, htmax] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hin : |φ t - x₀| ≤ R := by
    refine (hbound t).trans ?_
    rw [hR]
    have hexp : Real.exp ((K : ℝ) * |t - t₀|) ≤ Real.exp ((K : ℝ) * T) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hwin hK
    have h1 : M * |t - t₀| ≤ M * T := mul_le_mul_of_nonneg_left hwin hM0
    have h2 : (0 : ℝ) ≤ M * |t - t₀| := by positivity
    nlinarith [Real.exp_pos ((K : ℝ) * |t - t₀|), Real.exp_pos ((K : ℝ) * T)]
  have hgt : g t (φ t) = h t (φ t) := by
    rw [hg]
    simp only
    rw [clampAt_of_abs_le hin, clampAt_of_abs_le (by rw [abs_sub_comm] at hwin ⊢; exact hwin)]
  have := hφd t
  rw [hgt] at this
  exact this.hasDerivWithinAt

end GlobalODEGrowth
