module

public import UnitTangentIterates.Barriers

/-!
# Existence of the translating hairpin profile (Theorem 3.4, fixed point part)

Starting from the lower barrier `f₀ = f_ε^-` we iterate `f_{n+1} = 𝒫 f_n`.  By Lemma 3.3 and
monotonicity, `f_ε^- ≤ f₀ ≤ f₁ ≤ ⋯ ≤ f_ε^+`; the pointwise limit `f` is a fixed point of `𝒫`
(using the estimate `0 ≤ D_{f_n} - D_f ≤ m⁻¹ ∫₀^π (f - f_n)` and dominated convergence),
hence solves the translator equation.
-/

@[expose] public section

namespace Ovals

open Real Set MeasureTheory Filter Topology
open scoped Interval

theorem intervalIntegrable_of_aestronglyMeasurable_Ioo {g : ℝ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioo 0 π)))
    (hb : ∀ θ ∈ Ioo 0 π, |g θ| ≤ C) :
    IntervalIntegrable g volume 0 π := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le,
    integrableOn_Icc_iff_integrableOn_Ioo]
  refine Integrable.of_bound hg C ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun θ hθ => by rw [Real.norm_eq_abs]; exact hb θ hθ

theorem intervalIntegrable_of_continuousOn_Ioo {g : ℝ → ℝ} {C : ℝ}
    (hg : ContinuousOn g (Ioo 0 π)) (hb : ∀ θ ∈ Ioo 0 π, |g θ| ≤ C) :
    IntervalIntegrable g volume 0 π :=
  intervalIntegrable_of_aestronglyMeasurable_Ioo (hg.aestronglyMeasurable measurableSet_Ioo) hb
noncomputable def hairpinIter (ε : ℝ) : ℕ → ℝ → ℝ
  | 0 => fMinus ε
  | n + 1 => profP (hairpinIter ε n)

theorem bound_abs_of_barriers (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {g : ℝ → ℝ}
    (hg : ∀ θ ∈ Ioo 0 π, fMinus ε θ ≤ g θ ∧ g θ ≤ fPlus ε θ) :
    ∀ θ ∈ Ioo 0 π, |g θ| ≤ ε⁻¹ + 2 := by
  intro θ hθ
  have h1 := fMinus_ge hε0 θ
  have h2 := fPlus_le hε0 hε θ
  have h3 := one_lt_inv_sub hε0 hε
  rw [abs_le]; constructor <;> linarith [(hg θ hθ).1, (hg θ hθ).2]

theorem admissible_of_barriers (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {g : ℝ → ℝ}
    (hg : ∀ θ ∈ Ioo 0 π, fMinus ε θ ≤ g θ ∧ g θ ≤ fPlus ε θ)
    (hgi : IntervalIntegrable g volume 0 π) :
    AdmissibleProfile g (ε⁻¹ - ε) (ε⁻¹ + 2) where
  one_lt := one_lt_inv_sub hε0 hε
  lower := fun θ hθ => (fMinus_ge hε0 θ).trans (hg θ hθ).1
  upper := fun θ hθ => (hg θ hθ).2.trans (fPlus_le hε0 hε θ)
  integrable := hgi

theorem hairpinIter_spec (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (n : ℕ) :
    AdmissibleProfile (hairpinIter ε n) (ε⁻¹ - ε) (ε⁻¹ + 2) ∧
      ∀ θ ∈ Ioo 0 π, fMinus ε θ ≤ hairpinIter ε n θ ∧ hairpinIter ε n θ ≤ fPlus ε θ := by
  induction n with
  | zero => exact ⟨admissible_fMinus hε0 hε, fun θ _ => ⟨le_rfl, fMinus_le_fPlus hε0 θ⟩⟩
  | succ n ih =>
    obtain ⟨hadm, hb⟩ := ih
    have hbounds : ∀ θ ∈ Ioo 0 π,
        fMinus ε θ ≤ hairpinIter ε (n + 1) θ ∧ hairpinIter ε (n + 1) θ ≤ fPlus ε θ := by
      intro θ hθ
      obtain ⟨b1, -, b3⟩ := barrier_ineq hε0 hε hθ
      have m1 := profP_mono (admissible_fMinus hε0 hε) hadm (fun t ht => (hb t ht).1) hθ
      have m2 := profP_mono hadm (admissible_fPlus hε0 hε) (fun t ht => (hb t ht).2) hθ
      exact ⟨b1.trans m1, m2.trans b3⟩
    refine ⟨admissible_of_barriers hε0 hε hbounds ?_, hbounds⟩
    exact intervalIntegrable_of_continuousOn_Ioo (continuousOn_profP hadm)
      (bound_abs_of_barriers hε0 hε hbounds)

theorem hairpinIter_mono (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) : hairpinIter ε n θ ≤ hairpinIter ε (n + 1) θ := by
  induction n generalizing θ with
  | zero => exact (barrier_ineq hε0 hε hθ).1
  | succ n ih =>
    exact profP_mono (hairpinIter_spec hε0 hε n).1 (hairpinIter_spec hε0 hε (n + 1)).1
      (fun t ht => ih ht) hθ

noncomputable def hairpinProfile (ε : ℝ) (θ : ℝ) : ℝ := ⨆ n, hairpinIter ε n θ

theorem bddAbove_hairpinIter (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    BddAbove (Set.range fun n => hairpinIter ε n θ) :=
  ⟨fPlus ε θ, by rintro _ ⟨n, rfl⟩; exact ((hairpinIter_spec hε0 hε n).2 θ hθ).2⟩

theorem tendsto_hairpinIter (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Tendsto (fun n => hairpinIter ε n θ) atTop (𝓝 (hairpinProfile ε θ)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hairpinIter_mono hε0 hε n hθ)
    (bddAbove_hairpinIter hε0 hε hθ)

theorem hairpinIter_le_profile (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) : hairpinIter ε n θ ≤ hairpinProfile ε θ :=
  le_ciSup (bddAbove_hairpinIter hε0 hε hθ) n

theorem hairpinProfile_bounds (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    fMinus ε θ ≤ hairpinProfile ε θ ∧ hairpinProfile ε θ ≤ fPlus ε θ :=
  ⟨((hairpinIter_spec hε0 hε 0).2 θ hθ).1.trans (hairpinIter_le_profile hε0 hε 0 hθ),
    ciSup_le fun n => ((hairpinIter_spec hε0 hε n).2 θ hθ).2⟩

theorem admissible_hairpinProfile (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) :
    AdmissibleProfile (hairpinProfile ε) (ε⁻¹ - ε) (ε⁻¹ + 2) := by
  refine admissible_of_barriers hε0 hε (fun θ hθ => hairpinProfile_bounds hε0 hε hθ) ?_
  refine intervalIntegrable_of_aestronglyMeasurable_Ioo ?_
    (bound_abs_of_barriers hε0 hε fun θ hθ => hairpinProfile_bounds hε0 hε hθ)
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => hairpinIter ε n) ?_ ?_
  · intro n
    rcases n with _ | n
    · simp only [hairpinIter]
      rw [fMinus_eq]
      exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).aestronglyMeasurable
    · exact (continuousOn_profP (hairpinIter_spec hε0 hε n).1).aestronglyMeasurable
        measurableSet_Ioo
  · rw [ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun θ hθ => tendsto_hairpinIter hε0 hε hθ

theorem nonneg_ae_Ioc {u : ℝ → ℝ} (hu : ∀ t ∈ Ioo 0 π, 0 ≤ u t) :
    0 ≤ᵐ[volume.restrict (Ioc 0 π)] u := by
  rw [EventuallyLE, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun t ht => hu t ht

theorem profD_sub_le {f g : ℝ → ℝ} {m M : ℝ} (hf : AdmissibleProfile f m M)
    (hg : AdmissibleProfile g m M) (hgf : ∀ θ ∈ Ioo 0 π, g θ ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    profD g θ - profD f θ ≤ m⁻¹ * ∫ t in (0:ℝ)..π, (f t - g t) := by
  have hm := hf.one_lt
  obtain ⟨hDf0, -, hIf⟩ := profD_spec hf hθ
  obtain ⟨hDg0, -, hIg⟩ := profD_spec hg hθ
  have hlf := (profD_lt hf hθ).1
  have hlg := (profD_lt hg hθ).1
  have hanti := profD_anti hg hf hgf hθ
  set x := θ + profD f θ with hx
  set xn := θ + profD g θ with hxn
  have mθ : θ ∈ Icc 0 π := ⟨hθ.1.le, hθ.2.le⟩
  have mx : x ∈ Icc 0 π := ⟨by linarith [hθ.1], by linarith⟩
  have mxn : xn ∈ Icc 0 π := ⟨by linarith [hθ.1], by linarith⟩
  have h1 : ∫ t in x..xn, g t = ∫ t in θ..x, (f t - g t) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable mθ mx) (hg.intervalIntegrable mx mxn)
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable mθ mx)
      (hg.intervalIntegrable mθ mx)]
    linarith
  have h2 : m * (xn - x) ≤ ∫ t in x..xn, g t :=
    integral_ge_of_admissible hg mx.1 (by linarith) mxn.2
  have h3 : ∫ t in θ..x, (f t - g t) ≤ ∫ t in (0:ℝ)..π, (f t - g t) := by
    apply intervalIntegral.integral_mono_interval hθ.1.le (by linarith) mx.2
    · exact nonneg_ae_Ioc fun t ht => by linarith [hgf t ht]
    · exact hf.integrable.sub hg.integrable
  rw [le_inv_mul_iff₀ (by linarith)]
  have : xn - x = profD g θ - profD f θ := by rw [hx, hxn]; ring
  rw [this] at h2
  linarith

theorem ae_uIoc_of_Ioo {p : ℝ → Prop} (h : ∀ x ∈ Ioo 0 π, p x) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι 0 π → p x := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ π := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hxI
  rw [uIoc_of_le Real.pi_pos.le] at hxI
  exact h x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

theorem tendsto_integral_hairpinIter (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) :
    Tendsto (fun n => ∫ t in (0:ℝ)..π, (hairpinProfile ε t - hairpinIter ε n t)) atTop
      (𝓝 0) := by
  have hf := admissible_hairpinProfile hε0 hε
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := π) (l := atTop)
    (F := fun n t => hairpinProfile ε t - hairpinIter ε n t) (f := fun _ => (0:ℝ))
    (fun _ => 2 * (ε⁻¹ + 2))
    (Eventually.of_forall fun n => by
      rw [uIoc_of_le Real.pi_pos.le]
      exact (hf.integrable.sub (hairpinIter_spec hε0 hε n).1.integrable).1.aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_uIoc_of_Ioo fun x hx => by
      have h1 := bound_abs_of_barriers hε0 hε (fun θ hθ => hairpinProfile_bounds hε0 hε hθ) x hx
      have h2 := bound_abs_of_barriers hε0 hε (hairpinIter_spec hε0 hε n).2 x hx
      rw [Real.norm_eq_abs]
      calc |hairpinProfile ε x - hairpinIter ε n x|
          ≤ |hairpinProfile ε x| + |hairpinIter ε n x| := abs_sub _ _
        _ ≤ 2 * (ε⁻¹ + 2) := by linarith)
    intervalIntegrable_const
    (ae_uIoc_of_Ioo fun x hx => by
      have := tendsto_hairpinIter hε0 hε hx
      simpa using (tendsto_const_nhds (x := hairpinProfile ε x)).sub this)
  simpa using key

theorem profP_hairpinProfile (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    profP (hairpinProfile ε) θ = hairpinProfile ε θ := by
  have hf := admissible_hairpinProfile hε0 hε
  have hm := one_lt_inv_sub hε0 hε
  -- D_{f_n} θ → D_f θ
  have hD : Tendsto (fun n => profD (hairpinIter ε n) θ) atTop (𝓝 (profD (hairpinProfile ε) θ)) := by
    have hup : Tendsto (fun n => profD (hairpinProfile ε) θ +
        (ε⁻¹ - ε)⁻¹ * ∫ t in (0:ℝ)..π, (hairpinProfile ε t - hairpinIter ε n t)) atTop
        (𝓝 (profD (hairpinProfile ε) θ)) := by
      simpa using tendsto_const_nhds.add ((tendsto_integral_hairpinIter hε0 hε).const_mul _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
      (fun n => ?_)
    · exact profD_anti (hairpinIter_spec hε0 hε n).1 hf
        (fun t ht => hairpinIter_le_profile hε0 hε n ht) hθ
    · have := profD_sub_le hf (hairpinIter_spec hε0 hε n).1
        (fun t ht => hairpinIter_le_profile hε0 hε n ht) hθ
      simp only; linarith
  have hcot : ContinuousAt Real.cot (profD (hairpinProfile ε) θ) := by
    have hx0 := (profD_spec hf hθ).1
    have hx1 := (profD_lt hf hθ).2
    have hpi := Real.pi_pos
    have : Real.cot = fun x => Real.cos x / Real.sin x := funext Real.cot_eq_cos_div_sin
    rw [this]
    exact Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt
      (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)).ne'
  have hP : Tendsto (fun n => profP (hairpinIter ε n) θ) atTop
      (𝓝 (profP (hairpinProfile ε) θ)) :=
    tendsto_const_nhds.mul (hcot.tendsto.comp hD)
  have hP' : Tendsto (fun n => profP (hairpinIter ε n) θ) atTop (𝓝 (hairpinProfile ε θ)) :=
    (tendsto_hairpinIter hε0 hε hθ).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hP hP'

/-- The limit profile solves the translator equation (3.3). -/
theorem translatorEq_hairpinProfile (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) :
    TranslatorEq (hairpinProfile ε) :=
  (profP_fixed_iff (admissible_hairpinProfile hε0 hε)).1
    (fun _ hθ => profP_hairpinProfile hε0 hε hθ)

end Ovals

end
