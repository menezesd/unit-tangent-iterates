module

public import UnitTangentIterates.ShadowContinuity

/-!
# Tools for the limiting argument of Theorem 6.4

* limits along ultrafilters of eventually compact-valued families (`Ovals.limUnder_spec`);
* pointwise convergence of equi-Lipschitz `1`-periodic functions is uniform
  (`Ovals.unif_of_pointwise`);
* continuity of the closed curve `curveOfCurvature θ κ L` in `(κ, L)` for locally uniform
  convergence of `κ` (`Ovals.curve_tendsto`).
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- Limits along an ultrafilter of families that are eventually in a compact set. -/
lemma limUnder_spec {X : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X] {ι : Type*}
    (U : Ultrafilter ι) {s : Set X} (hs : IsCompact s) {g : ι → X}
    (h : ∀ᶠ j in (U : Filter ι), g j ∈ s) :
    Tendsto g U (𝓝 (limUnder (U : Filter ι) g)) ∧ limUnder (U : Filter ι) g ∈ s := by
  obtain ⟨x, -, hle⟩ := hs.ultrafilter_le_nhds (U.map g) (Filter.le_principal_iff.2 h)
  have ht : Tendsto g U (𝓝 (limUnder (U : Filter ι) g)) := tendsto_nhds_limUnder ⟨x, hle⟩
  exact ⟨ht, hs.isClosed.mem_of_tendsto ht h⟩

/-- `|x| ≤ |t|` for `x` between `0` and `t`. -/
lemma abs_le_of_mem_uIoc {x t : ℝ} (hx : x ∈ Set.uIoc 0 t) : |x| ≤ |t| := by
  rcases le_total 0 t with h | h
  · rw [Set.uIoc_of_le h] at hx
    rw [abs_of_pos hx.1, abs_of_nonneg h]; exact hx.2
  · rw [Set.uIoc_of_ge h] at hx
    rw [abs_of_nonpos hx.2, abs_of_nonpos h]; linarith [hx.1]

/-- **Pointwise convergence of equi-Lipschitz periodic functions is uniform.** -/
lemma unif_of_pointwise {ι : Type*} {F : Filter ι} {fj : ι → ℝ → ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ᶠ j in F, ∀ σ σ', |fj j σ - fj j σ'| ≤ C * |σ - σ'|)
    (hflip : ∀ σ σ', |f σ - f σ'| ≤ C * |σ - σ'|)
    (hper : ∀ᶠ j in F, Function.Periodic (fj j) 1) (hfper : Function.Periodic f 1)
    (hpt : ∀ σ, Tendsto (fun j => fj j σ) F (𝓝 (f σ))) :
    ∀ ε > 0, ∀ᶠ j in F, ∀ σ, |fj j σ - f σ| ≤ ε := by
  intro ε hε
  set M : ℕ := ⌈3 * C / ε⌉₊ + 1
  have hM : (0 : ℝ) < M := by positivity
  have hCM : C / M ≤ ε / 3 := by
    rw [div_le_iff₀ hM]
    have : 3 * C / ε ≤ M := by
      have := Nat.le_ceil (3 * C / ε)
      simp only [M]; push_cast; linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have hgrid : ∀ᶠ j in F, ∀ i ∈ Finset.range (M + 1),
      |fj j (i / M) - f (i / M)| ≤ ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro i _
    have := (Metric.tendsto_nhds.1 (hpt (i / M))) (ε / 3) (by positivity)
    filter_upwards [this] with j hj
    rw [← Real.dist_eq]; exact hj.le
  filter_upwards [hgrid, hlip, hper] with j hg hl hp σ
  set σ₀ := Int.fract σ
  have h1 : fj j σ = fj j σ₀ := by
    rw [show σ₀ = σ - (⌊σ⌋ : ℤ) * 1 by rw [mul_one]; rfl]; exact (hp.sub_int_mul_eq _).symm
  have h2 : f σ = f σ₀ := by
    rw [show σ₀ = σ - (⌊σ⌋ : ℤ) * 1 by rw [mul_one]; rfl]; exact (hfper.sub_int_mul_eq _).symm
  rw [h1, h2]
  have hσ0 := Int.fract_nonneg σ
  have hσ1 := Int.fract_lt_one σ
  set i : ℕ := ⌊σ₀ * M⌋₊
  have hi1 : (i : ℝ) ≤ σ₀ * M := Nat.floor_le (by positivity)
  have hi2 : σ₀ * M < i + 1 := Nat.lt_floor_add_one _
  have hiM : i ∈ Finset.range (M + 1) := by
    rw [Finset.mem_range]
    have : (i : ℝ) < M + 1 := by nlinarith
    exact_mod_cast this
  have hd : |σ₀ - i / M| ≤ 1 / M := by
    rw [show σ₀ - i / M = (σ₀ * M - i) / M by field_simp, abs_div, abs_of_pos hM]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have e1 := hl σ₀ (i / M)
  have e2 := hflip σ₀ (i / M)
  have e3 := hg i hiM
  have hCd : C * |σ₀ - i / M| ≤ ε / 3 := by
    calc C * |σ₀ - i / M| ≤ C * (1 / M) := by gcongr
      _ = C / M := by ring
      _ ≤ ε / 3 := hCM
  calc |fj j σ₀ - f σ₀| = |(fj j σ₀ - fj j (i / M)) + (fj j (i / M) - f (i / M)) +
        (f (i / M) - f σ₀)| := by ring_nf
    _ ≤ |fj j σ₀ - fj j (i / M)| + |fj j (i / M) - f (i / M)| + |f (i / M) - f σ₀| :=
        abs_add_three _ _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [abs_sub_comm (f _) (f σ₀)]
        linarith
    _ = ε := by ring

/-- The difference of the tangent integrals of two curvature functions. -/
lemma norm_tangentIntegral_sub_le {κ₁ κ₂ : ℝ → ℝ} (h₁ : Continuous κ₁) (h₂ : Continuous κ₂)
    {θ t ε : ℝ} (hε : ∀ r, |r| ≤ |t| → |κ₁ r - κ₂ r| ≤ ε) :
    ‖(∫ r in (0 : ℝ)..t, tau (angleOfCurvature θ κ₁ r)) -
      ∫ r in (0 : ℝ)..t, tau (angleOfCurvature θ κ₂ r)‖ ≤ ε * |t| * |t| := by
  rw [← intervalIntegral.integral_sub ((continuous_tau_angle h₁).intervalIntegrable _ _)
    ((continuous_tau_angle h₂).intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun r => tau (angleOfCurvature θ κ₁ r) - tau (angleOfCurvature θ κ₂ r))
    (C := ε * |t|) (fun r hr => by
      have hr' := abs_le_of_mem_uIoc hr
      refine (norm_tau_sub_le _ _).trans ?_
      simp only [angleOfCurvature, add_sub_add_left_eq_sub]
      rw [← intervalIntegral.integral_sub (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
        (f := fun x => κ₁ x - κ₂ x) (C := ε) (fun x hx => by
          rw [Real.norm_eq_abs]; exact hε x ((abs_le_of_mem_uIoc hx).trans hr'))
      rw [Real.norm_eq_abs, sub_zero] at this
      refine this.trans ?_
      have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 (by simp))
      exact mul_le_mul_of_nonneg_left hr' hε0)
  simpa using this

/-- **Continuity of closed curves in their curvature and half-perimeter.** -/
lemma curve_tendsto {ι : Type*} {F : Filter ι} {κj : ι → ℝ → ℝ} {κ : ℝ → ℝ} {Lj : ι → ℝ}
    {L : ℝ} (hκ : Continuous κ) (hκj : ∀ᶠ j in F, Continuous (κj j))
    (hloc : ∀ R ε, 0 < ε → ∀ᶠ j in F, ∀ r, |r| ≤ R → |κj j r - κ r| ≤ ε)
    (hL : Tendsto Lj F (𝓝 L)) (θ s : ℝ) :
    Tendsto (fun j => curveOfCurvature θ (κj j) (Lj j) s) F
      (𝓝 (curveOfCurvature θ κ L s)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  set A : ℝ → ℂ := fun t => ∫ r in (0 : ℝ)..t, tau (angleOfCurvature θ κ r)
  have hAc : Continuous A := by
    have hc := continuous_tau_angle (θ₀ := θ) hκ
    exact continuous_iff_continuousAt.2 fun t =>
      (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).continuousAt
  have hAL : Tendsto (fun j => A (Lj j)) F (𝓝 (A L)) := (hAc.tendsto L).comp hL
  set R := max |s| (|L| + 1)
  have hR : 0 ≤ R := le_max_of_le_left (abs_nonneg _)
  set ε := e / (4 * (R * R + 1))
  have hε : 0 < ε := by positivity
  have hRε : R * R * ε ≤ e / 4 := by
    simp only [ε]; rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hLR : ∀ᶠ j in F, |Lj j| ≤ R := by
    have := (Metric.tendsto_nhds.1 hL) 1 one_pos
    filter_upwards [this] with j hj
    rw [Real.dist_eq] at hj
    have : |Lj j| ≤ |L| + 1 := by
      have := abs_sub_abs_le_abs_sub (Lj j) L; linarith
    exact this.trans (le_max_right _ _)
  filter_upwards [hκj, hloc R ε hε, hLR, (Metric.tendsto_nhds.1 hAL) (e / 2) (by positivity)]
    with j hcj hj hjR hjA
  rw [dist_eq_norm] at hjA ⊢
  have e1 := norm_tangentIntegral_sub_le (θ := θ) (t := s) hcj hκ fun r hr =>
    hj r (hr.trans (le_max_left _ _))
  have e2 := norm_tangentIntegral_sub_le (θ := θ) (t := Lj j) hcj hκ fun r hr =>
    hj r (hr.trans hjR)
  have hs : |s| ≤ R := le_max_left _ _
  have e1' : ε * |s| * |s| ≤ e / 4 := by
    calc ε * |s| * |s| ≤ ε * R * R := by gcongr
      _ = R * R * ε := by ring
      _ ≤ e / 4 := hRε
  have e2' : ε * |Lj j| * |Lj j| ≤ e / 4 := by
    calc ε * |Lj j| * |Lj j| ≤ ε * R * R := by gcongr
      _ = R * R * ε := by ring
      _ ≤ e / 4 := hRε
  unfold curveOfCurvature
  set B := ∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ (κj j) r)
  set Bj := ∫ r in (0 : ℝ)..Lj j, tau (angleOfCurvature θ (κj j) r)
  have hsplit : B - (1 / 2 : ℂ) * Bj - (A s - (1 / 2 : ℂ) * A L) =
      (B - A s) - (1 / 2 : ℂ) * ((Bj - A (Lj j)) + (A (Lj j) - A L)) := by ring
  rw [show (∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ κ r)) = A s from rfl,
    show (∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ κ r)) = A L from rfl, hsplit]
  calc ‖(B - A s) - (1 / 2 : ℂ) * ((Bj - A (Lj j)) + (A (Lj j) - A L))‖
      ≤ ‖B - A s‖ + ‖(1 / 2 : ℂ)‖ * (‖Bj - A (Lj j)‖ + ‖A (Lj j) - A L‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ e / 4 + 1 / 2 * (e / 4 + e / 2) := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [this]
        gcongr
        · exact e1.trans e1'
        · exact e2.trans e2'
    _ < e := by linarith

end Ovals

end
