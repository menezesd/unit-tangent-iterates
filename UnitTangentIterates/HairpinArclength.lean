import Mathlib
import UnitTangentIterates.HairpinTails

/-!
# The arclength parametrization of the hairpin

Section 3 of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*
parametrizes the hairpin by its tangent angle `θ ∈ (0, π)`; Section 4 uses it
as a *track*, parametrized by arclength `u ∈ ℝ`.  This file builds the passage
between the two.

For a profile continuous on `(0, π)` with `0 < m ≤ f`, the arclength

`S(θ) = ∫_{π/2}^θ f/sin`

is a strictly increasing `C¹` bijection of `(0, π)` onto `ℝ`: strict
monotonicity is `S' = f/sin > 0`, and surjectivity comes from the comparison
`m L(θ) ≤ S(θ)` (`θ ≥ π/2`), `S(θ) ≤ m L(θ)` (`θ ≤ π/2`) of `HairpinTails.lean`
with the explicit model arclength `L(θ) = log tan(θ/2)`, whose inverse is
`θ = 2 arctan e^L`.

Main results:

* `hasDerivAt_arclength`, `strictMonoOn_arclength` : `S' = f/sin > 0`;
* `surjective_arclength` : `S` maps `(0, π)` onto `ℝ`;
* `exists_angle` : the inverse `θ(u)`, a strictly increasing differentiable
  bijection `ℝ → (0, π)` with `θ'(u) = sin θ(u)/f(θ(u)) = κ(u)`, the curvature
  of the hairpin in arclength;
* `curvature_decay_arclength` : `κ(u) ≤ (2/m) e^{-|u|/M}`, the tail bound of
  the lemma *Hairpin pulse estimates* in its arclength form.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace HairpinArclength

open HairpinTails

variable {f : ℝ → ℝ} {m M : ℝ}

/-! ### The arclength is an increasing bijection onto the line -/

theorem hasDerivAt_arclength (hcont : ContinuousOn f (Ioo 0 π)) {θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (Hairpin.hairpinArclength f (π/2)) (f θ / Real.sin θ) θ := by
  have hcf : ContinuousOn (fun t => f t / Real.sin t) (Ioo 0 π) := continuousOn_div_sin hcont
  have hsub : uIcc (π/2) θ ⊆ Ioo (0:ℝ) π := uIcc_subset_Ioo_pi hθ
  have hint : IntervalIntegrable (fun t => f t / Real.sin t) volume (π/2) θ :=
    (hcf.mono hsub).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hcf.stronglyMeasurableAtFilter isOpen_Ioo θ hθ)
    (hcf.continuousAt (isOpen_Ioo.mem_nhds hθ))

theorem continuousOn_arclength (hcont : ContinuousOn f (Ioo 0 π)) :
    ContinuousOn (Hairpin.hairpinArclength f (π/2)) (Ioo 0 π) := fun _ hθ =>
  ((hasDerivAt_arclength hcont hθ).continuousAt).continuousWithinAt

theorem strictMonoOn_arclength (hcont : ContinuousOn f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) :
    StrictMonoOn (Hairpin.hairpinArclength f (π/2)) (Ioo 0 π) := by
  intro a ha b hb hab
  have hsub : Icc a b ⊆ Ioo (0:ℝ) π := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩
  have hpos : ∀ t ∈ Ioo a b, 0 < f t / Real.sin t := by
    intro t ht
    have htm : t ∈ Ioo (0:ℝ) π := hsub ⟨ht.1.le, ht.2.le⟩
    have hs := Real.sin_pos_of_pos_of_lt_pi htm.1 htm.2
    have hf := lt_of_lt_of_le hm (hlow t htm)
    positivity
  have hint : IntervalIntegrable (fun t => f t / Real.sin t) volume a b :=
    (((continuousOn_div_sin hcont).mono hsub).mono
      (by rw [uIcc_of_le hab.le])).intervalIntegrable
  have hgap : 0 < ∫ t in a..b, f t / Real.sin t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos hab
  have hadd : Hairpin.hairpinArclength f (π/2) a + (∫ t in a..b, f t / Real.sin t)
      = Hairpin.hairpinArclength f (π/2) b := by
    refine intervalIntegral.integral_add_adjacent_intervals ?_ hint
    have hsub' : uIcc (π/2) a ⊆ Ioo (0:ℝ) π := uIcc_subset_Ioo_pi ha
    exact (((continuousOn_div_sin hcont).mono hsub')).intervalIntegrable
  linarith [hgap, hadd]

/-! ### Surjectivity -/

theorem angle_of_logHalf_mem {x : ℝ} : 2 * Real.arctan (Real.exp x) ∈ Ioo (0:ℝ) π := by
  have h1 : 0 < Real.arctan (Real.exp x) := Real.arctan_pos.mpr (Real.exp_pos x)
  have h2 : Real.arctan (Real.exp x) < π/2 := Real.arctan_lt_pi_div_two _
  exact ⟨by linarith, by linarith⟩

theorem logHalf_angle {x : ℝ} : logHalf (2 * Real.arctan (Real.exp x)) = x := by
  have h : (2 * Real.arctan (Real.exp x)) / 2 = Real.arctan (Real.exp x) := by ring
  rw [logHalf, h, Real.tan_arctan, Real.log_exp]

/-- **The arclength maps `(0, π)` onto the line.** -/
theorem surjective_arclength (hcont : ContinuousOn f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (u : ℝ) :
    ∃ θ ∈ Ioo (0:ℝ) π, Hairpin.hairpinArclength f (π/2) θ = u := by
  set x : ℝ := (|u| + m) / m with hx
  have hxpos : 0 < x := by
    have : 0 ≤ |u| := abs_nonneg u
    positivity
  have hmx : m * x = |u| + m := by rw [hx]; field_simp
  set θb : ℝ := 2 * Real.arctan (Real.exp x) with hθb
  set θa : ℝ := 2 * Real.arctan (Real.exp (-x)) with hθa
  have hbmem : θb ∈ Ioo (0:ℝ) π := angle_of_logHalf_mem
  have hamem : θa ∈ Ioo (0:ℝ) π := angle_of_logHalf_mem
  have hLb : logHalf θb = x := logHalf_angle
  have hLa : logHalf θa = -x := logHalf_angle
  -- `θb` is to the right of `π/2` and `θa` to the left
  have hbhalf : π/2 ≤ θb := by
    have h1 : Real.arctan 1 ≤ Real.arctan (Real.exp x) :=
      Real.arctan_mono (by simpa using (Real.one_le_exp hxpos.le))
    rw [Real.arctan_one] at h1
    rw [hθb]; linarith
  have hahalf : θa ≤ π/2 := by
    have h1 : Real.arctan (Real.exp (-x)) ≤ Real.arctan 1 :=
      Real.arctan_mono (by simpa using (Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)))
    rw [Real.arctan_one] at h1
    rw [hθa]; linarith
  have hub : u ≤ Hairpin.hairpinArclength f (π/2) θb := by
    have h := m_mul_logHalf_le hcont hlow hbmem hbhalf
    rw [hLb, hmx] at h
    have : u ≤ |u| + m := by
      have := le_abs_self u
      linarith
    linarith
  have hlb : Hairpin.hairpinArclength f (π/2) θa ≤ u := by
    have h := le_m_mul_logHalf hcont hlow hamem hahalf
    rw [hLa] at h
    have hval : m * -x = -(|u| + m) := by rw [← hmx]; ring
    rw [hval] at h
    have : -(|u| + m) ≤ u := by
      have := neg_abs_le u
      linarith
    linarith
  have hab : θa ≤ θb := by
    have h1 : Real.arctan (Real.exp (-x)) ≤ Real.arctan (Real.exp x) :=
      Real.arctan_mono (Real.exp_le_exp.mpr (by linarith))
    rw [hθa, hθb]; linarith
  have hIcc : Icc θa θb ⊆ Ioo (0:ℝ) π := by
    intro t ht
    exact ⟨lt_of_lt_of_le hamem.1 ht.1, lt_of_le_of_lt ht.2 hbmem.2⟩
  have hc : ContinuousOn (Hairpin.hairpinArclength f (π/2)) (Icc θa θb) :=
    (continuousOn_arclength hcont).mono hIcc
  have hmem := intermediate_value_Icc hab hc (by exact ⟨hlb, hub⟩)
  obtain ⟨θ, hθIcc, hθval⟩ := hmem
  exact ⟨θ, hIcc hθIcc, hθval⟩

/-! ### The inverse: the tangent angle as a function of arclength -/

/-- **The hairpin in arclength.**  The arclength `S` has a differentiable
inverse `θ : ℝ → (0, π)`, the tangent angle at the point of arclength `u`; its
derivative is the curvature `κ(u) = sin θ(u)/f(θ(u))`. -/
theorem exists_angle (hcont : ContinuousOn f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) :
    ∃ theta : ℝ → ℝ, (∀ u, theta u ∈ Ioo (0:ℝ) π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, theta (Hairpin.hairpinArclength f (π/2) θ) = θ) ∧
      StrictMono theta ∧ Continuous theta ∧
      (∀ u, HasDerivAt theta (Real.sin (theta u) / f (theta u)) u) := by
  have hmono := strictMonoOn_arclength hcont hm hlow
  choose theta hmem hval using surjective_arclength hcont hm hlow
  -- left inverse
  have hleft : ∀ θ ∈ Ioo (0:ℝ) π, theta (Hairpin.hairpinArclength f (π/2) θ) = θ := by
    intro θ hθ
    refine hmono.injOn (hmem _) hθ ?_
    rw [hval]
  -- strict monotonicity of the inverse
  have hsm : StrictMono theta := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · have : a = b := by
        have h1 := hval a
        have h2 := hval b
        rw [heq] at h2
        rw [← h1, ← h2]
      exact absurd this (ne_of_lt hab)
    · have := hmono (hmem b) (hmem a) hlt
      rw [hval, hval] at this
      linarith
  -- continuity of the inverse
  have hcontθ : Continuous theta := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    refine Metric.continuousAt_iff.mpr ?_
    intro ε hε
    set a : ℝ := theta u with ha
    have hamem : a ∈ Ioo (0:ℝ) π := hmem u
    set θ1 : ℝ := max (a - ε/2) (a/2) with hθ1
    set θ2 : ℝ := min (a + ε/2) ((a + π)/2) with hθ2
    have h1lt : θ1 < a := by
      refine max_lt (by linarith) (by linarith [hamem.1])
    have h2gt : a < θ2 := by
      refine lt_min (by linarith) (by linarith [hamem.2])
    have h1mem : θ1 ∈ Ioo (0:ℝ) π := by
      constructor
      · exact lt_of_lt_of_le (by linarith [hamem.1] : (0:ℝ) < a/2) (le_max_right _ _)
      · exact lt_trans h1lt hamem.2
    have h2mem : θ2 ∈ Ioo (0:ℝ) π := by
      constructor
      · exact lt_trans hamem.1 h2gt
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hamem.2])
    have hd1 : u - Hairpin.hairpinArclength f (π/2) θ1 > 0 := by
      have := hmono h1mem hamem h1lt
      rw [ha, hval] at this
      linarith
    have hd2 : Hairpin.hairpinArclength f (π/2) θ2 - u > 0 := by
      have := hmono hamem h2mem h2gt
      rw [ha, hval] at this
      linarith
    refine ⟨min (u - Hairpin.hairpinArclength f (π/2) θ1)
      (Hairpin.hairpinArclength f (π/2) θ2 - u), lt_min hd1 hd2, ?_⟩
    intro y hy
    rw [Real.dist_eq] at hy ⊢
    have hy1 : Hairpin.hairpinArclength f (π/2) θ1 < y := by
      have := abs_lt.mp hy
      have hmin := min_le_left (u - Hairpin.hairpinArclength f (π/2) θ1)
        (Hairpin.hairpinArclength f (π/2) θ2 - u)
      linarith [this.1]
    have hy2 : y < Hairpin.hairpinArclength f (π/2) θ2 := by
      have := abs_lt.mp hy
      have hmin := min_le_right (u - Hairpin.hairpinArclength f (π/2) θ1)
        (Hairpin.hairpinArclength f (π/2) θ2 - u)
      linarith [this.2]
    have hlow1 : θ1 < theta y := by
      have := hsm hy1
      rwa [hleft θ1 h1mem] at this
    have hhigh : theta y < θ2 := by
      have := hsm hy2
      rwa [hleft θ2 h2mem] at this
    have hb1 : a - ε/2 ≤ θ1 := le_max_left _ _
    have hb2 : θ2 ≤ a + ε/2 := min_le_left _ _
    rw [abs_lt]
    constructor <;> [linarith; linarith]
  refine ⟨theta, hmem, hval, hleft, hsm, hcontθ, ?_⟩
  intro u
  have hθu : theta u ∈ Ioo (0:ℝ) π := hmem u
  have hs : 0 < Real.sin (theta u) := Real.sin_pos_of_pos_of_lt_pi hθu.1 hθu.2
  have hf : 0 < f (theta u) := lt_of_lt_of_le hm (hlow _ hθu)
  have hne : f (theta u) / Real.sin (theta u) ≠ 0 := by positivity
  have hderiv := hasDerivAt_arclength hcont hθu
  have hloc : HasDerivAt theta (f (theta u) / Real.sin (theta u))⁻¹ u := by
    refine HasDerivAt.of_local_left_inverse hcontθ.continuousAt hderiv hne ?_
    filter_upwards with y using hval y
  rwa [inv_div] at hloc

/-- **The tail bound in arclength.**  `κ(u) ≤ (2/m) e^{-|u|/M}`. -/
theorem curvature_decay_arclength (hcont : ContinuousOn f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ M)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) (u : ℝ) :
    Real.sin (theta u) / f (theta u) ≤ (2 / m) * Real.exp (-|u| / M) := by
  have h := curvature_decay hcont hm hlow hup (hmem u)
  rwa [hval u] at h

end HairpinArclength
