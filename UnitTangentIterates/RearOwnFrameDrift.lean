import Mathlib
import UnitTangentIterates.RearOwnFrameData

/-!
# The gauge frame bundle of a unit-speed family whose length changes

`RearOwnFrameData.lean` builds the bundle `UniformFrameBounds.GaugeFrameData` of
a unit-speed family from *periodicity* of its tangential component in the
arclength.  That is available only when the arclength period is the same at
every time: the closing relation of a family of closed curves written in its own
arclength makes the tangential component drift,

`ξ(t, x + Q t) = ξ(t, x) − Q'(t)`,

so `ξ` is genuinely periodic exactly when the length does not move
(`GaugePeriodRigidity.lean`).

This file removes that restriction.  The bundle asks only for bounds on the two
arclength derivatives of the tangential *rate* `−ξ/v`, which for a unit-speed
family are `−ξ'` and `−ξ''`; and differentiating the drift relation shows that
those two **are** periodic, with the current period `Q t`, however the length
moves.  Since the period varies continuously with the time, it stays below a
finite ceiling over a compact window of times, and a jointly continuous function
which is `Q a`-periodic in the arclength is bounded there
(`exists_bound_of_periodic_var`).  Clamping the time makes the bounds global, as
before.

Main results:

* `exists_bound_of_periodic_var` — boundedness with a variable period;
* `periodic_partialX_drift` — the arclength derivative of a drifting function is
  periodic;
* `exists_gaugeFrameData_unitSpeed_drift`,
  `exists_gaugeFrameData_unitSpeed_drift_frozen`,
  `exists_gaugeFrameData_frameTangential_drift` — the bundle.
-/

noncomputable section

open Set Function

namespace RearOwnFrameDrift

open UniformFrameBounds RearFamilyFrame

/-! ### Boundedness with a variable period -/

/-- **A jointly continuous function which is periodic in the arclength with a
period depending on the time is bounded on a compact window of times**, as soon
as the period stays below a ceiling there. -/
theorem exists_bound_of_periodic_var {f : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {t0 t1 Pmax : ℝ}
    (hP : ∀ a, 0 < P a) (hPmax : ∀ a ∈ Icc t0 t1, P a ≤ Pmax)
    (hc : Continuous (uncurry f)) (hper : ∀ a, Function.Periodic (f a) (P a)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Icc t0 t1, ∀ x, |f a x| ≤ M := by
  rcases le_or_gt t0 t1 with ht | ht
  · have hPmax0 : 0 ≤ Pmax := le_trans (hP t0).le (hPmax t0 (left_mem_Icc.mpr ht))
    have hK : IsCompact (Icc t0 t1 ×ˢ Icc (0 : ℝ) Pmax) := isCompact_Icc.prod isCompact_Icc
    have hne : (Icc t0 t1 ×ˢ Icc (0 : ℝ) Pmax).Nonempty :=
      ⟨(t0, 0), ⟨left_mem_Icc.mpr ht, left_mem_Icc.mpr hPmax0⟩⟩
    obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne hc.abs.continuousOn
    refine ⟨|uncurry f p|, abs_nonneg _, ?_⟩
    intro a ha x
    obtain ⟨y, hy, hxy⟩ := (hper a).exists_mem_Ico₀ (hP a) x
    have hmem : (a, y) ∈ Icc t0 t1 ×ˢ Icc (0 : ℝ) Pmax :=
      ⟨ha, ⟨hy.1, le_trans hy.2.le (hPmax a ha)⟩⟩
    have := hmax hmem
    simpa [hxy, uncurry] using this
  · exact ⟨0, le_rfl, fun a ha => absurd (ha.1.trans ha.2) (not_le.mpr ht)⟩

/-- A continuous period has a ceiling on a compact window of times. -/
theorem exists_period_ceiling {P : ℝ → ℝ} (hP : Continuous P) (t0 t1 : ℝ) :
    ∃ Pmax : ℝ, ∀ a ∈ Icc t0 t1, P a ≤ Pmax := by
  rcases le_or_gt t0 t1 with ht | ht
  · obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc t0 t1)
      ⟨t0, left_mem_Icc.mpr ht⟩ hP.continuousOn
    exact ⟨P a, fun b hb => hmax hb⟩
  · exact ⟨0, fun a ha => absurd (ha.1.trans ha.2) (not_le.mpr ht)⟩

/-! ### The derivatives of a drifting function are periodic -/

/-- **The arclength derivative of a function which drifts by a constant over
each period is periodic.** -/
theorem periodic_partialX_drift {f : ℝ → ℝ → ℝ} {P c : ℝ → ℝ}
    (hf : ContDiff ℝ 1 (uncurry f))
    (hqp : ∀ a x, f a (x + P a) = f a x - c a) (a : ℝ) :
    Function.Periodic (partialX f a) (P a) := by
  intro x
  have h1 : HasDerivAt (f a) (partialX f a (x + P a)) (x + P a) :=
    hasDerivAt_partialX hf a _
  have h2 : HasDerivAt (fun y => f a (y + P a)) (partialX f a (x + P a)) x := by
    simpa using h1.comp x ((hasDerivAt_id x).add_const (P a))
  have hfun : (fun y => f a (y + P a)) = fun y => f a y - c a := funext fun y => hqp a y
  rw [hfun] at h2
  have h3 : HasDerivAt (fun y => f a y - c a) (partialX f a x) x :=
    (hasDerivAt_partialX hf a x).sub_const _
  exact h2.unique h3

/-! ### The bundle -/

/-- **The gauge frame bundle of a unit-speed family whose length changes.**  A
tangential component which is `C³` in the pair and drifts by `c a` over the
current period `P a` produces a bundle whose speed is `1` and whose tangential
component is the given one with the time clamped to the window `[t₀, t₁]`.  No
bound on the tangential component itself is used — only on its two arclength
derivatives, which are periodic. -/
theorem exists_gaugeFrameData_unitSpeed_drift {xi : ℝ → ℝ → ℝ} {P c : ℝ → ℝ} {t0 t1 : ℝ}
    (ht : t0 ≤ t1) (hPpos : ∀ a, 0 < P a) (hPc : Continuous P)
    (hxi : ContDiff ℝ (3 : ℕ) (uncurry xi))
    (hqp : ∀ a x, xi a (x + P a) = xi a x - c a) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧
      (∀ a x, D.xi a x = xi (clampT t0 t1 a) x) := by
  have h3le2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)
  have h3le1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)
  have hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi) := hxi.of_le h3le2
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) := hxi.of_le h3le1
  set xiD := partialX xi with hxiDdef
  have hxiD2 : ContDiff ℝ (2 : ℕ) (uncurry xiD) := by
    have : ContDiff ℝ ((2 : ℕ) + 1) (uncurry xi) := by exact_mod_cast hxi
    exact contDiff_partialX this
  have hxiD1 : ContDiff ℝ (1 : ℕ) (uncurry xiD) :=
    hxiD2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  set xiDD := partialX xiD with hxiDDdef
  have hxiDD0 : ContDiff ℝ (1 : ℕ) (uncurry xiDD) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xiD) := by exact_mod_cast hxiD2
    exact contDiff_partialX this
  -- the first derivative is periodic because the drift is constant in the arclength
  have hxiDper : ∀ a, Function.Periodic (xiD a) (P a) := periodic_partialX_drift hxi1 hqp
  -- the second derivative is periodic because the first one is
  have hxiDDper : ∀ a, Function.Periodic (xiDD a) (P a) := by
    intro a
    exact periodic_partialX_drift (c := fun _ => 0) hxiD1
      (fun b y => by simpa using (hxiDper b y)) a
  obtain ⟨Pmax, hPmax⟩ := exists_period_ceiling hPc t0 t1
  obtain ⟨A1, hA1nn, hA1⟩ := exists_bound_of_periodic_var (t0 := t0) (t1 := t1)
    hPpos hPmax hxiD1.continuous hxiDper
  obtain ⟨A2, hA2nn, hA2⟩ := exists_bound_of_periodic_var (t0 := t0) (t1 := t1)
    hPpos hPmax hxiDD0.continuous hxiDDper
  refine ⟨{
      xi := timeClamp t0 t1 xi
      xi1 := timeClamp t0 t1 xiD
      xi2 := timeClamp t0 t1 xiDD
      v := fun _ _ => 1
      v1 := fun _ _ => 0
      v2 := fun _ _ => 0
      rateLip := A1
      rateBound2 := A2
      hxi := hasDerivAt_timeClamp (hasDerivAt_partialX hxi1)
      hxi1 := hasDerivAt_timeClamp (hasDerivAt_partialX hxiD1)
      hv := fun _ x => hasDerivAt_const x (1 : ℝ)
      hv1 := fun _ x => hasDerivAt_const x (0 : ℝ)
      hvne := fun _ _ => one_ne_zero
      hxic := continuous_timeClamp hxi1.continuous
      hxi1c := continuous_timeClamp hxiD1.continuous
      hxi2c := continuous_timeClamp hxiDD0.continuous
      hvc := continuous_const
      hv1c := continuous_const
      hv2c := continuous_const
      hrate1 := fun a x => by
        simpa [GaugeRate.gaugeRate1] using timeClamp_bound ht hA1 a x
      hrate2 := fun a x => by
        simpa [GaugeRate.gaugeRate2] using timeClamp_bound ht hA2 a x },
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The bundle of a unit-speed family whose length changes, at rest outside
the time window.**  The bundle's tangential component is then the given one at
*every* time. -/
theorem exists_gaugeFrameData_unitSpeed_drift_frozen {xi : ℝ → ℝ → ℝ} {P c : ℝ → ℝ}
    {t0 t1 : ℝ} (ht : t0 ≤ t1) (hPpos : ∀ a, 0 < P a) (hPc : Continuous P)
    (hxi : ContDiff ℝ (3 : ℕ) (uncurry xi))
    (hqp : ∀ a x, xi a (x + P a) = xi a x - c a)
    (hfrozen : ∀ a x, xi a x = xi (clampT t0 t1 a) x) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧ (∀ a x, D.xi a x = xi a x) := by
  obtain ⟨D, hv, hxiD⟩ := exists_gaugeFrameData_unitSpeed_drift ht hPpos hPc hxi hqp
  exact ⟨D, hv, fun a x => by rw [hxiD a x, ← hfrozen a x]⟩

/-- **The gauge frame bundle of the family of rear tracks written in its own
arclength, when the length of the rear moves.**

The family has unit speed, and its tangential component `ξ = ⟨Ẏ, e^{iΨ}⟩` drifts
by the rate of change of the arclength period over each period — which is the
closing relation of the family, `GaugeClosingRelations.closing_relations`.  The
bundle produced has speed `1` and tangential component exactly `ξ`, so it can be
fed to the variable-period assembly of the path metric. -/
theorem exists_gaugeFrameData_frameTangential_drift {Ydot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    {P c : ℝ → ℝ} {t0 t1 : ℝ} (ht : t0 ≤ t1) (hPpos : ∀ a, 0 < P a) (hPc : Continuous P)
    (hY : ContDiff ℝ (3 : ℕ) (uncurry Ydot)) (hpsi : ContDiff ℝ (3 : ℕ) (uncurry psi))
    (hqp : ∀ a x, frameTangential Ydot psi a (x + P a) = frameTangential Ydot psi a x - c a)
    (hfrozen : ∀ a x, Ydot a x = Ydot (clampT t0 t1 a) x)
    (hpsifrozen : ∀ a x, psi a x = psi (clampT t0 t1 a) x) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧
      (∀ a x, D.xi a x = frameTangential Ydot psi a x) :=
  exists_gaugeFrameData_unitSpeed_drift_frozen ht hPpos hPc
    (RearOwnFrameData.contDiff_frameTangential hY hpsi) hqp
    (fun a x => by simp only [frameTangential, hfrozen a x, hpsifrozen a x])

/-! ### The bundle with prescribed constants -/

/-- **The gauge frame bundle of a unit-speed family, with the two constants
prescribed.**

When bounds for the two arclength derivatives of the tangential component are
already available, no compactness argument and no clamping of the time are
needed: the bundle can be built with exactly those two constants, and its
tangential component is the given one at every time.  This is what a bound with
constants *uniform over a family of paths* requires, the constants produced by
`exists_gaugeFrameData_unitSpeed_drift` depending on the path through the
compact window of times. -/
theorem exists_gaugeFrameData_unitSpeed_of_bounds {xi : ℝ → ℝ → ℝ} {rL rB : ℝ}
    (hxi : ContDiff ℝ (3 : ℕ) (uncurry xi))
    (h1 : ∀ a x, |partialX xi a x| ≤ rL)
    (h2 : ∀ a x, |partialX (partialX xi) a x| ≤ rB) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧ (∀ a x, D.xi a x = xi a x) ∧
      D.rateLip = rL ∧ D.rateBound2 = rB := by
  have h3le1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) := hxi.of_le h3le1
  set xiD := partialX xi with hxiDdef
  have hxiD2 : ContDiff ℝ (2 : ℕ) (uncurry xiD) := by
    have : ContDiff ℝ ((2 : ℕ) + 1) (uncurry xi) := by exact_mod_cast hxi
    exact contDiff_partialX this
  have hxiD1 : ContDiff ℝ (1 : ℕ) (uncurry xiD) :=
    hxiD2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  set xiDD := partialX xiD with hxiDDdef
  have hxiDD0 : ContDiff ℝ (1 : ℕ) (uncurry xiDD) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xiD) := by exact_mod_cast hxiD2
    exact contDiff_partialX this
  exact ⟨{
      xi := xi
      xi1 := xiD
      xi2 := xiDD
      v := fun _ _ => 1
      v1 := fun _ _ => 0
      v2 := fun _ _ => 0
      rateLip := rL
      rateBound2 := rB
      hxi := hasDerivAt_partialX hxi1
      hxi1 := hasDerivAt_partialX hxiD1
      hv := fun _ x => hasDerivAt_const x (1 : ℝ)
      hv1 := fun _ x => hasDerivAt_const x (0 : ℝ)
      hvne := fun _ _ => one_ne_zero
      hxic := hxi1.continuous
      hxi1c := hxiD1.continuous
      hxi2c := hxiDD0.continuous
      hvc := continuous_const
      hv1c := continuous_const
      hv2c := continuous_const
      hrate1 := fun a x => by simpa [GaugeRate.gaugeRate1] using h1 a x
      hrate2 := fun a x => by simpa [GaugeRate.gaugeRate2] using h2 a x },
    fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- **The gauge frame bundle of the family of rear tracks written in its own
arclength, with the two constants prescribed.**  The variant of
`exists_gaugeFrameData_frameTangential_drift` whose constants are given in
advance: the family is not asked to be at rest outside any window, nor its
tangential component to drift in any particular way, only its two arclength
derivatives to be bounded. -/
theorem exists_gaugeFrameData_frameTangential_of_bounds {Ydot : ℝ → ℝ → ℂ}
    {psi : ℝ → ℝ → ℝ} {rL rB : ℝ}
    (hY : ContDiff ℝ (3 : ℕ) (uncurry Ydot)) (hpsi : ContDiff ℝ (3 : ℕ) (uncurry psi))
    (h1 : ∀ a x, |partialX (frameTangential Ydot psi) a x| ≤ rL)
    (h2 : ∀ a x, |partialX (partialX (frameTangential Ydot psi)) a x| ≤ rB) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧
      (∀ a x, D.xi a x = frameTangential Ydot psi a x) ∧
      D.rateLip = rL ∧ D.rateBound2 = rB :=
  exists_gaugeFrameData_unitSpeed_of_bounds
    (RearOwnFrameData.contDiff_frameTangential hY hpsi) h1 h2

end RearOwnFrameDrift
