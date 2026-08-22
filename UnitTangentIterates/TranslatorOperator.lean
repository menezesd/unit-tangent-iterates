import Mathlib
import UnitTangentIterates.Translator
import UnitTangentIterates.TranslatorFixedPoint
import UnitTangentIterates.TranslatorRegularity
import UnitTangentIterates.HairpinLimit

/-!
# The translator operator and its fixed point

This file assembles the analytic core of the theorem *Translating hairpin* of
the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*: the
translator operator

`(𝒫f)(θ) = sin θ · cot D_f(θ)`,   `∫_θ^{θ + D_f(θ)} f = sin θ`,

is here **defined** as a function of profiles (`Pop`), rather than appearing
only through its defining relations, and the monotone iteration started at a
subsolution is shown to converge to a genuine fixed point.

A *profile* is a measurable function `f : ℝ → ℝ` with `m ≤ f ≤ M`; for
`1 < m` the defining equation of the shift has a unique solution
`massTime f θ ∈ (θ, π)` for every `θ ∈ (0, π)` (`massTime_mem`,
`massTime_integral`, `massTime_unique`), the shift `D_f = massTime f − θ`
satisfies `0 < D_f < π/2` (`shift_pos`, `shift_lt_pi_div_two`) and `𝒫f` is
positive (`Pop_pos`) and order preserving in `f` (`Pop_mono`).

Given barriers `low ≤ up`, a subsolution and a supersolution of `𝒫`, the
iterates `f_{n+1} = 𝒫 f_n` started at `low` increase and stay below `up`, and
their pointwise limit is a fixed point of `𝒫`:

`exists_translator_profile` — there is a profile `f` with `low ≤ f ≤ up`,
continuous on `(0, π)`, satisfying `f = sin θ · cot D_f` and, equivalently, the
translator equation `D_f(θ) = arctan (sin θ / f(θ))` there.

The explicit barriers of the paper (the inequalities `low ≤ 𝒫 low` and
`𝒫 up ≤ up` for the profiles of `Barriers.lean`) are hypotheses here.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace TranslatorOperator

/-- A **profile**: a measurable function with values in `[m, M]`.  The
translator operator is defined on profiles with `1 < m`. -/
structure Profile (m M : ℝ) (f : ℝ → ℝ) : Prop where
  /-- profiles are measurable. -/
  meas : Measurable f
  /-- profiles are bounded below by `m`. -/
  lower : ∀ t, m ≤ f t
  /-- profiles are bounded above by `M`. -/
  upper : ∀ t, f t ≤ M

namespace Profile

variable {m M : ℝ} {f : ℝ → ℝ}

theorem abs_le_bound (hf : Profile m M f) (t : ℝ) : |f t| ≤ |m| + |M| := by
  have h1 := hf.lower t
  have h2 := hf.upper t
  have h3 := neg_abs_le m
  have h4 := le_abs_self M
  have h5 := abs_nonneg m
  have h6 := abs_nonneg M
  rw [_root_.abs_le]
  constructor <;> linarith

/-- A profile is interval integrable. -/
theorem int (hf : Profile m M f) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;>
    exact MeasureTheory.Measure.integrableOn_of_bounded
      (by simp) hf.meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        simpa [Real.norm_eq_abs] using hf.abs_le_bound t)

end Profile

variable {m M : ℝ} {f g : ℝ → ℝ}

/-- Strict monotonicity of the accumulated mass of a profile. -/
theorem integral_strictMono (hf : Profile m M f) (hm0 : 0 < m) (θ : ℝ) :
    StrictMono fun u => ∫ t in θ..u, f t := by
  intro a b hab
  have hadd : (∫ t in θ..a, f t) + (∫ t in a..b, f t) = ∫ t in θ..b, f t :=
    intervalIntegral.integral_add_adjacent_intervals (hf.int _ _) (hf.int _ _)
  have hlow : m * (b - a) ≤ ∫ t in a..b, f t := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (a := a) (b := b)
      (f := fun _ => m) (g := f) hab.le
      (_root_.intervalIntegrable_const) (hf.int _ _) (fun t _ => hf.lower t)
    simpa [mul_comm] using h
  have : 0 < m * (b - a) := mul_pos hm0 (by linarith)
  linarith

open Classical in
/-- The solution `u` of the defining equation `∫_θ^u f = sin θ` of the
translator shift; the junk value `θ` is used off `(0, π)`. -/
def massTime (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if h : 0 < θ ∧ ∃ u, u ∈ Ioo θ π ∧ (∫ t in θ..u, f t) = Real.sin θ then h.2.choose else θ

/-- The translator shift `D_f(θ)`. -/
def shift (f : ℝ → ℝ) (θ : ℝ) : ℝ := massTime f θ - θ

/-- The **translator operator** `(𝒫f)(θ) = sin θ · cot D_f(θ)`. -/
def Pop (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.sin θ * (Real.cos (shift f θ) / Real.sin (shift f θ))

/-- **The defining equation of the shift is solvable.** -/
theorem exists_massTime (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ∃ u, u ∈ Ioo θ π ∧ (∫ t in θ..u, f t) = Real.sin θ := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  set G : ℝ → ℝ := fun u => ∫ t in θ..u, f t with hG
  have hcont : Continuous G := intervalIntegral.continuous_primitive (hf.int) θ
  have hGθ : G θ = 0 := by simp [hG]
  have hGπ : Real.sin θ < G π := by
    have hlow : m * (π - θ) ≤ G π := by
      have h := intervalIntegral.integral_mono_on (μ := volume) (a := θ) (b := π)
        (f := fun _ => m) (g := f) hθ.2.le
        (_root_.intervalIntegrable_const) (hf.int _ _) (fun t _ => hf.lower t)
      simpa [hG, mul_comm] using h
    exact lt_of_lt_of_le (TranslatorFixedPoint.sin_lt_mul_pi_sub hθ.2 hm.le) hlow
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsub : Ioo (G θ) (G π) ⊆ G '' Ioo θ π :=
    intermediate_value_Ioo hθ.2.le hcont.continuousOn
  obtain ⟨u, hu, hGu⟩ := hsub ⟨by rw [hGθ]; exact hsin, hGπ⟩
  exact ⟨u, hu, hGu⟩

theorem massTime_mem (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    massTime f θ ∈ Ioo θ π := by
  have hex := exists_massTime hf hm hθ
  have h : 0 < θ ∧ ∃ u, u ∈ Ioo θ π ∧ (∫ t in θ..u, f t) = Real.sin θ := ⟨hθ.1, hex⟩
  rw [massTime, dif_pos h]
  exact h.2.choose_spec.1

theorem massTime_integral (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    (∫ t in θ..massTime f θ, f t) = Real.sin θ := by
  have hex := exists_massTime hf hm hθ
  have h : 0 < θ ∧ ∃ u, u ∈ Ioo θ π ∧ (∫ t in θ..u, f t) = Real.sin θ := ⟨hθ.1, hex⟩
  rw [massTime, dif_pos h]
  exact h.2.choose_spec.2

/-- **Uniqueness** of the solution of the defining equation. -/
theorem massTime_unique (hf : Profile m M f) (hm : 1 < m) {θ u : ℝ} (hθ : θ ∈ Ioo 0 π)
    (hval : (∫ t in θ..u, f t) = Real.sin θ) : u = massTime f θ := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hmono := integral_strictMono hf hm0 θ
  exact hmono.injective (by rw [hval, massTime_integral hf hm hθ])

theorem shift_integral (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    (∫ t in θ..(θ + shift f θ), f t) = Real.sin θ := by
  have := massTime_integral hf hm hθ
  simpa [shift] using this

theorem shift_bounds (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < shift f θ ∧ shift f θ < π / 2 := by
  have hlt : θ < massTime f θ := (massTime_mem hf hm hθ).1
  obtain ⟨h1, -, h3⟩ :=
    TranslatorRegularity.shift_lt_pi_div_two (f := f) (m := m) (hf.int) hm hf.lower hlt
      (massTime_integral hf hm hθ)
  exact ⟨h1, h3⟩

theorem sin_shift_pos (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < Real.sin (shift f θ) := by
  obtain ⟨h1, h2⟩ := shift_bounds hf hm hθ
  exact Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])

theorem cos_shift_pos (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < Real.cos (shift f θ) := by
  obtain ⟨h1, h2⟩ := shift_bounds hf hm hθ
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩

/-- The operator produces positive values on `(0, π)`. -/
theorem Pop_pos (hf : Profile m M f) (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < Pop f θ := by
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 := sin_shift_pos hf hm hθ
  have h2 := cos_shift_pos hf hm hθ
  exact mul_pos hsθ (div_pos h2 h1)

/-- **The translator operator is order preserving.** -/
theorem Pop_mono {M' : ℝ} (hf : Profile m M f) (hg : Profile m M' g) (hm : 1 < m)
    (hle : ∀ t, f t ≤ g t) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : Pop f θ ≤ Pop g θ := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hDf := shift_bounds hf hm hθ
  have hDg := shift_bounds hg hm hθ
  have hanti : shift g θ ≤ shift f θ :=
    Translator.translator_shift_antitone (f := f) (h := g) (θ := θ)
      hle (fun t => lt_of_lt_of_le hm0 (hf.lower t)) hDf.1
      (shift_integral hf hm hθ) (shift_integral hg hm hθ) (hf.int) (hg.int)
  exact Translator.translator_operator_mono hθ hDg.1 hDf.2 hanti

/-- The operator is continuous on `(0, π)`. -/
theorem Pop_continuousOn (hf : Profile m M f) (hm : 1 < m) :
    ContinuousOn (Pop f) (Ioo 0 π) := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hUc : ContinuousOn (massTime f) (Ioo 0 π) :=
    TranslatorRegularity.shift_continuousOn (f := f) (m := m) (M := M) (hf.int) hm0 hf.lower
      hf.upper (U := massTime f) (fun θ hθ => massTime_integral hf hm hθ)
  have hD : ContinuousOn (shift f) (Ioo 0 π) := hUc.sub continuousOn_id
  refine (Real.continuous_sin.continuousOn).mul ?_
  refine (Real.continuous_cos.comp_continuousOn hD).div
    (Real.continuous_sin.comp_continuousOn hD) ?_
  intro θ hθ
  exact ne_of_gt (sin_shift_pos hf hm hθ)

/-- The junk value of the operator off `(0, π)`. -/
theorem Pop_of_notMem {θ : ℝ} (hθ : θ ∉ Ioo 0 π) : Pop f θ = 0 := by
  have hm : massTime f θ = θ := by
    rw [massTime, dif_neg]
    rintro ⟨hpos, u, hu, -⟩
    exact hθ ⟨hpos, lt_trans hu.1 hu.2⟩
  simp [Pop, shift, hm]

/-! ### The monotone iteration -/

section Iteration

variable {low up : ℝ → ℝ}

open Classical in
/-- One step of the iteration: the translator operator on `(0, π)`, and the
lower barrier off `(0, π)` (where the operator is not defined). -/
def step (low f : ℝ → ℝ) : ℝ → ℝ := (Ioo 0 π).piecewise (Pop f) low

theorem step_of_mem {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : step low f θ = Pop f θ := by
  simp [step, Set.piecewise, hθ]

theorem step_of_notMem {θ : ℝ} (hθ : θ ∉ Ioo 0 π) : step low f θ = low θ := by
  simp [step, Set.piecewise, hθ]

/-- One step of the iteration is measurable. -/
theorem step_measurable (hlowc : Continuous low) (hf : Profile m M f) (hm : 1 < m) :
    Measurable (step low f) := by
  refine measurable_of_measurable_union_cover (Ioo (0:ℝ) π) ((Ioo (0:ℝ) π)ᶜ)
    measurableSet_Ioo (measurableSet_Ioo (a := (0:ℝ)) (b := π)).compl (by simp) ?_ ?_
  · have h : (fun a : Ioo (0:ℝ) π => step low f a) = (Ioo (0:ℝ) π).restrict (Pop f) := by
      funext a
      exact step_of_mem a.2
    rw [h]
    exact ((Pop_continuousOn hf hm).restrict).measurable
  · have h : (fun a : ((Ioo (0:ℝ) π)ᶜ : Set ℝ) => step low f a)
        = ((Ioo (0:ℝ) π)ᶜ).restrict low := by
      funext a
      exact step_of_notMem a.2
    rw [h]
    exact (hlowc.comp continuous_subtype_val).measurable

/-- One step preserves the order interval between the barriers. -/
theorem step_bounds (hm : 1 < m) (hlow : Profile m M low) (hup : Profile m M up)
    (hle : ∀ t, low t ≤ up t)
    (hsub : ∀ θ ∈ Ioo 0 π, low θ ≤ Pop low θ)
    (hsuper : ∀ θ ∈ Ioo 0 π, Pop up θ ≤ up θ)
    (hf : Profile m M f) (hfl : ∀ t, low t ≤ f t) (hfu : ∀ t, f t ≤ up t) :
    (∀ t, low t ≤ step low f t) ∧ (∀ t, step low f t ≤ up t) := by
  constructor
  · intro θ
    by_cases hθ : θ ∈ Ioo 0 π
    · rw [step_of_mem hθ]
      exact le_trans (hsub θ hθ) (Pop_mono hlow hf hm hfl hθ)
    · rw [step_of_notMem hθ]
  · intro θ
    by_cases hθ : θ ∈ Ioo 0 π
    · rw [step_of_mem hθ]
      exact le_trans (Pop_mono hf hup hm hfu hθ) (hsuper θ hθ)
    · rw [step_of_notMem hθ]
      exact hle θ

/-- One step preserves the order. -/
theorem step_mono (hm : 1 < m) (hf : Profile m M f) (hg : Profile m M g)
    (hle : ∀ t, f t ≤ g t) (θ : ℝ) : step low f θ ≤ step low g θ := by
  by_cases hθ : θ ∈ Ioo 0 π
  · rw [step_of_mem hθ, step_of_mem hθ]
    exact Pop_mono hf hg hm hle hθ
  · rw [step_of_notMem hθ, step_of_notMem hθ]

/-- The iterates `f_{n+1} = 𝒫 f_n` of the translator operator, started at the
lower barrier. -/
def iter (low : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => low
  | (n + 1) => step low (iter low n)

theorem iter_zero : iter low 0 = low := rfl

theorem iter_succ (n : ℕ) : iter low (n + 1) = step low (iter low n) := rfl

/-- The iterates are profiles trapped between the barriers. -/
theorem iter_spec (hm : 1 < m) (hlowc : Continuous low) (hlow : Profile m M low)
    (hup : Profile m M up) (hle : ∀ t, low t ≤ up t)
    (hsub : ∀ θ ∈ Ioo 0 π, low θ ≤ Pop low θ)
    (hsuper : ∀ θ ∈ Ioo 0 π, Pop up θ ≤ up θ) (n : ℕ) :
    Profile m M (iter low n) ∧ (∀ t, low t ≤ iter low n t) ∧ (∀ t, iter low n t ≤ up t) := by
  induction n with
  | zero => exact ⟨hlow, fun t => le_refl _, hle⟩
  | succ n ih =>
    obtain ⟨hprof, hl, hu⟩ := ih
    obtain ⟨hl', hu'⟩ := step_bounds hm hlow hup hle hsub hsuper hprof hl hu
    refine ⟨⟨step_measurable hlowc hprof hm, ?_, ?_⟩, hl', hu'⟩
    · exact fun t => le_trans (hlow.lower t) (hl' t)
    · exact fun t => le_trans (hu' t) (hup.upper t)

/-- The iterates increase. -/
theorem iter_le_succ (hm : 1 < m) (hlowc : Continuous low) (hlow : Profile m M low)
    (hup : Profile m M up) (hle : ∀ t, low t ≤ up t)
    (hsub : ∀ θ ∈ Ioo 0 π, low θ ≤ Pop low θ)
    (hsuper : ∀ θ ∈ Ioo 0 π, Pop up θ ≤ up θ) (n : ℕ) (t : ℝ) :
    iter low n t ≤ iter low (n + 1) t := by
  induction n generalizing t with
  | zero =>
    exact (step_bounds hm hlow hup hle hsub hsuper hlow (fun t => le_refl _) hle).1 t
  | succ n ih =>
    have h1 := (iter_spec hm hlowc hlow hup hle hsub hsuper n).1
    have h2 := (iter_spec hm hlowc hlow hup hle hsub hsuper (n + 1)).1
    exact step_mono hm h1 h2 (fun t => ih t) t

end Iteration

/-! ### The fixed point -/

section FixedPoint

variable {low up : ℝ → ℝ}

/-- **The monotone iteration converges to a fixed point of the translator
operator.**  Given barriers `low ≤ up`, a subsolution and a supersolution of
`𝒫` bounded between `1 < m` and `M`, there is a profile `f` with
`low ≤ f ≤ up`, continuous on `(0, π)`, which is a fixed point of `𝒫` there;
equivalently, its shift satisfies the translator equation
`D_f(θ) = arctan (sin θ / f(θ))`. -/
theorem exists_translator_profile (hm : 1 < m) (hlowc : Continuous low)
    (hlow : Profile m M low) (hup : Profile m M up) (hle : ∀ t, low t ≤ up t)
    (hsub : ∀ θ ∈ Ioo 0 π, low θ ≤ Pop low θ)
    (hsuper : ∀ θ ∈ Ioo 0 π, Pop up θ ≤ up θ) :
    ∃ f : ℝ → ℝ, Profile m M f ∧ (∀ t, low t ≤ f t) ∧ (∀ t, f t ≤ up t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo 0 π, f θ = Pop f θ) ∧
      (∀ θ ∈ Ioo 0 π, (∫ t in θ..(θ + shift f θ), f t) = Real.sin θ) ∧
      (∀ θ ∈ Ioo 0 π, shift f θ = Real.arctan (Real.sin θ / f θ)) := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hpi := Real.pi_pos
  set fs : ℕ → ℝ → ℝ := fun n => iter low n with hfs
  have hspec : ∀ n, Profile m M (fs n) ∧ (∀ t, low t ≤ fs n t) ∧ (∀ t, fs n t ≤ up t) :=
    fun n => iter_spec hm hlowc hlow hup hle hsub hsuper n
  have hmono : ∀ n t, fs n t ≤ fs (n + 1) t :=
    fun n t => iter_le_succ hm hlowc hlow hup hle hsub hsuper n t
  set F : ℝ → ℝ := fun θ => ⨆ n, fs n θ with hF
  have htend : ∀ θ, Tendsto (fun n => fs n θ) atTop (𝓝 (F θ)) := fun θ =>
    HairpinLimit.tendsto_iterates (fseq := fs) (M := up) hmono (fun n t => (hspec n).2.2 t) θ
  have hFlow : ∀ t, low t ≤ F t := by
    intro t
    exact le_trans ((hspec 0).2.1 t)
      (HairpinLimit.le_iSup_iterates (fseq := fs) (M := up) (fun n t => (hspec n).2.2 t) 0 t)
  have hFup : ∀ t, F t ≤ up t := by
    intro t
    exact ciSup_le fun n => (hspec n).2.2 t
  have hFprof : Profile m M F := by
    refine ⟨Measurable.iSup fun n => (hspec n).1.meas, fun t => ?_, fun t => ?_⟩
    · exact le_trans (hlow.lower t) (hFlow t)
    · exact le_trans (hFup t) (hup.upper t)
  have hmono' : ∀ t, Monotone fun n => fs n t := by
    intro t
    exact monotone_nat_of_le_succ fun n => hmono n t
  have hfsle : ∀ n t, fs n t ≤ F t := fun n t =>
    HairpinLimit.le_iSup_iterates (fseq := fs) (M := up) (fun k t => (hspec k).2.2 t) n t
  -- the defect masses tend to zero
  set e : ℕ → ℝ := fun n => ∫ u in (0:ℝ)..π, (F u - fs n u) with he
  have hetend : Tendsto e atTop (𝓝 0) :=
    HairpinLimit.tendsto_integral_sub_zero (fseq := fs) (F := F) hpi.le
      (fun n => (hspec n).1.int 0 π) (hFprof.int 0 π) hmono' htend
  -- the fixed-point equation
  have hfix : ∀ θ ∈ Ioo (0:ℝ) π, F θ = Pop F θ := by
    intro θ hθ
    have hu : ∀ n, massTime (fs n) θ ∈ Ioo θ π := fun n => massTime_mem (hspec n).1 hm hθ
    have huF : massTime F θ ∈ Ioo θ π := massTime_mem hFprof hm hθ
    have hmemIcc : ∀ x, x ∈ Ioo θ π → x ∈ Icc (0:ℝ) π := by
      intro x hx
      exact ⟨le_of_lt (lt_trans hθ.1 hx.1), hx.2.le⟩
    have hAe : ∀ n, |TranslatorRegularity.mass (fs n) (massTime (fs n) θ)
        - TranslatorRegularity.mass F (massTime (fs n) θ)| ≤ e n := by
      intro n
      exact HairpinLimit.abs_primitive_sub_le (fseq := fs) (F := F) hpi.le n
        ((hspec n).1.int 0 π) (hFprof.int 0 π) (fun t => hfsle n t) (hmemIcc _ (hu n))
    have hAd : ∀ n, |TranslatorRegularity.mass (fs n) (massTime (fs n) θ)
        - TranslatorRegularity.mass F (massTime F θ)| ≤ e n := by
      intro n
      have h1 : TranslatorRegularity.mass (fs n) (massTime (fs n) θ)
          - TranslatorRegularity.mass (fs n) θ = Real.sin θ := by
        rw [TranslatorRegularity.mass_sub_mass ((hspec n).1.int)]
        exact massTime_integral (hspec n).1 hm hθ
      have h2 : TranslatorRegularity.mass F (massTime F θ)
          - TranslatorRegularity.mass F θ = Real.sin θ := by
        rw [TranslatorRegularity.mass_sub_mass (hFprof.int)]
        exact massTime_integral hFprof hm hθ
      have h3 : TranslatorRegularity.mass (fs n) (massTime (fs n) θ)
          - TranslatorRegularity.mass F (massTime F θ)
          = TranslatorRegularity.mass (fs n) θ - TranslatorRegularity.mass F θ := by
        linarith
      rw [h3]
      exact HairpinLimit.abs_primitive_sub_le (fseq := fs) (F := F) hpi.le n
        ((hspec n).1.int 0 π) (hFprof.int 0 π) (fun t => hfsle n t) ⟨hθ.1.le, hθ.2.le⟩
    have hconv : Tendsto (fun n => massTime (fs n) θ) atTop (𝓝 (massTime F θ)) :=
      HairpinLimit.tendsto_inverse_points (m := m) hm0
        (fun x y hxy => TranslatorRegularity.mass_lower_bound (hFprof.int) hFprof.lower hxy)
        hAe hAd hetend
    have hDconv : Tendsto (fun n => shift (fs n) θ) atTop (𝓝 (shift F θ)) := by
      simpa [shift] using hconv.sub (tendsto_const_nhds (x := θ) (f := atTop (α := ℕ)))
    have hvals : Tendsto (fun n => Real.sin θ
        * (Real.cos (shift (fs n) θ) / Real.sin (shift (fs n) θ))) atTop (𝓝 (F θ)) := by
      have hshift : ∀ n, Real.sin θ
          * (Real.cos (shift (fs n) θ) / Real.sin (shift (fs n) θ)) = fs (n + 1) θ := by
        intro n
        rw [hfs]
        simp only [iter_succ]
        rw [step_of_mem hθ, Pop]
      simp only [hshift]
      exact (htend θ).comp (Filter.tendsto_add_atTop_nat 1)
    have := HairpinLimit.limit_fixed_point (c := Real.sin θ) (v := F θ)
      (D := shift F θ) (Dn := fun n => shift (fs n) θ) hDconv
      (ne_of_gt (sin_shift_pos hFprof hm hθ)) hvals
    rw [Pop]
    exact this
  have hcont : ContinuousOn F (Ioo 0 π) := by
    refine TranslatorRegularity.fixedPoint_continuousOn (f := F) (m := m) (M := M)
      (hFprof.int) hm hFprof.lower hFprof.upper (U := massTime F)
      (fun θ hθ => (massTime_mem hFprof hm hθ).1)
      (fun θ hθ => massTime_integral hFprof hm hθ) ?_
    intro θ hθ
    have := hfix θ hθ
    rw [Pop, shift] at this
    exact this
  refine ⟨F, hFprof, hFlow, hFup, hcont, hfix, fun θ hθ => shift_integral hFprof hm hθ, ?_⟩
  intro θ hθ
  obtain ⟨hD0, hD2⟩ := shift_bounds hFprof hm hθ
  have hFpos : 0 < F θ := lt_of_lt_of_le (lt_trans zero_lt_one hm) (hFprof.lower θ)
  exact (TranslatorFixedPoint.fixed_point_iff_arctan (θ := θ) hD0 hD2 hFpos).1
    (by rw [← Pop]; exact hfix θ hθ)

end FixedPoint

end TranslatorOperator
