import Mathlib

/-!
# The monotone iteration producing the translating hairpin

This file formalizes the limit argument in the proof of the theorem
*Translating hairpin* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*.

There, one starts from the lower barrier `f₀ = f_ε^-` and iterates the
order-preserving operator `𝒫`, obtaining an increasing sequence of profiles
trapped under the upper barrier `f_ε^+`.  The proof then

1. takes the pointwise monotone limit `f = lim f_n` (`tendsto_iterates`);
2. upgrades this to *uniform* convergence of the primitives
   `A_n(t) = ∫₀ᵗ f_n`, with the explicit bound
   `sup_t |A_n(t) - A(t)| ≤ ∫₀^π (f - f_n) → 0`
   (`abs_primitive_sub_le`, `tendsto_integral_sub_zero`,
   `primitives_tendstoUniformly`);
3. deduces convergence of the inverse functions from the uniform convergence
   of the primitives and a common positive lower bound for their slopes
   (`tendsto_inverse_points`);
4. passes to the limit in `f_{n+1}(θ) = sin θ · cot D_{f_n}(θ)`
   (`limit_fixed_point`).

The statements below are the general forms of these four steps.
-/

noncomputable section

open MeasureTheory Filter Topology intervalIntegral

namespace HairpinLimit

variable {fseq : ℕ → ℝ → ℝ} {F M : ℝ → ℝ} {a b : ℝ}

/-! ### The pointwise monotone limit -/

/-- **The monotone iterates converge pointwise** to their pointwise supremum,
as soon as they are increasing and trapped under the upper barrier. -/
theorem tendsto_iterates (hmono : ∀ n θ, fseq n θ ≤ fseq (n + 1) θ)
    (hbdd : ∀ n θ, fseq n θ ≤ M θ) (θ : ℝ) :
    Tendsto (fun n => fseq n θ) atTop (𝓝 (⨆ n, fseq n θ)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ (fun n => hmono n θ)) ⟨M θ, ?_⟩
  rintro y ⟨n, rfl⟩
  exact hbdd n θ

/-- The pointwise limit dominates every iterate. -/
theorem le_iSup_iterates (hbdd : ∀ n θ, fseq n θ ≤ M θ) (n : ℕ) (θ : ℝ) : fseq n θ ≤ ⨆ k, fseq k θ :=
  le_ciSup (f := fun k => fseq k θ) ⟨M θ, by rintro y ⟨k, rfl⟩; exact hbdd k θ⟩ n

/-! ### Uniform convergence of the primitives -/

/-- **The primitive error is controlled by the total mass of the defect**:
for every `t` in `[a, b]`,
`|∫ₐᵗ f_n - ∫ₐᵗ f| ≤ ∫ₐᵇ (f - f_n)`. -/
theorem abs_primitive_sub_le (hab : a ≤ b) (n : ℕ)
    (hfi : IntervalIntegrable (fseq n) volume a b) (hFi : IntervalIntegrable F volume a b)
    (hle : ∀ θ, fseq n θ ≤ F θ) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    |(∫ u in a..t, fseq n u) - ∫ u in a..t, F u| ≤ ∫ u in a..b, (F u - fseq n u) := by
  have hfit : IntervalIntegrable (fseq n) volume a t :=
    hfi.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2)
  have hFit : IntervalIntegrable F volume a t :=
    hFi.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2)
  have hdiff : (∫ u in a..t, F u) - ∫ u in a..t, fseq n u = ∫ u in a..t, (F u - fseq n u) := by
    rw [intervalIntegral.integral_sub hFit hfit]
  have hnonneg : 0 ≤ ∫ u in a..t, (F u - fseq n u) :=
    intervalIntegral.integral_nonneg ht.1 (fun u _ => by linarith [hle u])
  have hmono : (∫ u in a..t, (F u - fseq n u)) ≤ ∫ u in a..b, (F u - fseq n u) := by
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun u => by
        have := hle u
        simpa using sub_nonneg.mpr this)) (hFi.sub hfi)
  rw [abs_sub_comm, abs_of_nonneg (by linarith [hdiff ▸ hnonneg]), hdiff]
  exact hmono

/-- **The total mass of the defect tends to zero** (monotone convergence). -/
theorem tendsto_integral_sub_zero (hab : a ≤ b)
    (hfi : ∀ n, IntervalIntegrable (fseq n) volume a b)
    (hFi : IntervalIntegrable F volume a b)
    (hmono : ∀ θ, Monotone fun n => fseq n θ)
    (hpt : ∀ θ, Tendsto (fun n => fseq n θ) atTop (𝓝 (F θ))) :
    Tendsto (fun n => ∫ u in a..b, (F u - fseq n u)) atTop (𝓝 0) := by
  have hconv : Tendsto (fun n => ∫ u in a..b, fseq n u) atTop (𝓝 (∫ u in a..b, F u)) := by
    simp only [intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (fun n => (hfi n).1) hFi.1 ?_ ?_
    · exact Filter.Eventually.of_forall (fun θ => hmono θ)
    · exact Filter.Eventually.of_forall (fun θ => hpt θ)
  have hsplit : ∀ n, (∫ u in a..b, (F u - fseq n u))
      = (∫ u in a..b, F u) - ∫ u in a..b, fseq n u := fun n => by
    rw [intervalIntegral.integral_sub hFi (hfi n)]
  simp only [hsplit]
  simpa using (tendsto_const_nhds (x := ∫ u in a..b, F u) (f := atTop (α := ℕ))).sub hconv

/-- **Uniform convergence of the primitives on `[a, b]`.** -/
theorem primitives_tendstoUniformly (hab : a ≤ b)
    (hfi : ∀ n, IntervalIntegrable (fseq n) volume a b)
    (hFi : IntervalIntegrable F volume a b)
    (hmono : ∀ θ, Monotone fun n => fseq n θ)
    (hle : ∀ n θ, fseq n θ ≤ F θ)
    (hpt : ∀ θ, Tendsto (fun n => fseq n θ) atTop (𝓝 (F θ))) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t ∈ Set.Icc a b,
      |(∫ u in a..t, fseq n u) - ∫ u in a..t, F u| ≤ ε := by
  intro ε hε
  have h := tendsto_integral_sub_zero hab hfi hFi hmono hpt
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn t ht => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1
  refine (abs_primitive_sub_le hab n (hfi n) hFi (fun θ => hle n θ) ht).trans ?_
  exact le_of_abs_le h1.le

/-! ### Convergence of the inverse functions -/

/-- **The inverse functions converge.**  If the primitives converge uniformly
(here: with error `e n` at the relevant points) and the limiting primitive has
slope at least `m > 0`, then the solutions `t_n` of `A_n(t_n) = A(t) + c`
converge to the solution `t` of the limiting equation. -/
theorem tendsto_inverse_points {A : ℝ → ℝ} {An : ℕ → ℝ → ℝ} {tn : ℕ → ℝ} {t m : ℝ}
    {e : ℕ → ℝ} (hm : 0 < m)
    (hslope : ∀ x y, x ≤ y → m * (y - x) ≤ A y - A x)
    (hAe : ∀ n, |An n (tn n) - A (tn n)| ≤ e n)
    (hAd : ∀ n, |An n (tn n) - A t| ≤ e n)
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto tn atTop (𝓝 t) := by
  have hkey : ∀ n, |tn n - t| ≤ 2 * e n / m := by
    intro n
    have h1 : |A (tn n) - A t| ≤ 2 * e n := by
      calc |A (tn n) - A t| = |(A (tn n) - An n (tn n)) + (An n (tn n) - A t)| := by ring_nf
        _ ≤ |A (tn n) - An n (tn n)| + |An n (tn n) - A t| := abs_add_le _ _
        _ ≤ e n + e n := by
            refine add_le_add ?_ (hAd n)
            rw [abs_sub_comm]; exact hAe n
        _ = 2 * e n := by ring
    have h2 : m * |tn n - t| ≤ |A (tn n) - A t| := by
      rcases le_total (tn n) t with h | h
      · have hsl := hslope (tn n) t h
        have hs1 : A (tn n) - A t ≤ 0 := by nlinarith
        rw [abs_of_nonpos (by linarith : tn n - t ≤ 0), abs_of_nonpos hs1]
        nlinarith
      · have hsl := hslope t (tn n) h
        have hs1 : 0 ≤ A (tn n) - A t := by nlinarith
        rw [abs_of_nonneg (by linarith : 0 ≤ tn n - t), abs_of_nonneg hs1]
        nlinarith
    rw [le_div_iff₀ hm, mul_comm]
    linarith
  have hzero : Tendsto (fun n => 2 * e n / m) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (2:ℝ)) (f := atTop (α := ℕ))).mul he).div_const m
  have : Tendsto (fun n => tn n - t) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hkey n) hzero
  simpa using this.add (tendsto_const_nhds (x := t) (f := atTop (α := ℕ)))

/-! ### Passing to the limit in the fixed-point equation -/

/-- **The limit is a fixed point.**  If the steering widths `D_n` converge to
`D` with `sin D ≠ 0`, and `sin θ · cot D_n` converges to `v`, then
`v = sin θ · cot D`. -/
theorem limit_fixed_point {c v D : ℝ} {Dn : ℕ → ℝ}
    (hD : Tendsto Dn atTop (𝓝 D)) (hsin : Real.sin D ≠ 0)
    (hf : Tendsto (fun n => c * (Real.cos (Dn n) / Real.sin (Dn n))) atTop (𝓝 v)) :
    v = c * (Real.cos D / Real.sin D) := by
  have hcos : Tendsto (fun n => Real.cos (Dn n)) atTop (𝓝 (Real.cos D)) :=
    (Real.continuous_cos.tendsto D).comp hD
  have hsn : Tendsto (fun n => Real.sin (Dn n)) atTop (𝓝 (Real.sin D)) :=
    (Real.continuous_sin.tendsto D).comp hD
  have hlim : Tendsto (fun n => c * (Real.cos (Dn n) / Real.sin (Dn n))) atTop
      (𝓝 (c * (Real.cos D / Real.sin D))) :=
    (hcos.div hsn hsin).const_mul c
  exact tendsto_nhds_unique hf hlim

end HairpinLimit
