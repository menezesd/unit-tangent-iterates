import Mathlib
import UnitTangentIterates.RelativeDerivatives
import UnitTangentIterates.HairpinArclength
import UnitTangentIterates.ArclengthInverse

/-!
# Relative derivative bounds for the hairpin curvature and the steering pulse

This file discharges the two families of *relative derivative bounds* of the
lemma **Hairpin pulse estimates** of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*:

```
  |K_*^{(j)}(u)| ≤ C_j K_*(u)          (relative curvature derivatives)
  |y^{(j)}(s)|   ≤ D_j y(s)            (relative pulse derivatives)
```

where `K_*` is the curvature of the hairpin in its own arclength `u` and
`y = sin δ` is the steering pulse in the front arclength `s`.

The paper proves them by an induction on the order using Faà di Bruno's formula
and a bounded-shift Harnack inequality.  Here they are obtained from the
observation formalized in `RelativeDerivatives.lean`: both quantities are
values of a smooth field along an autonomous flow.  Indeed, with the tangent
angle `θ` of the hairpin as state variable and

```
  G(t) = sin t / f(t)        (the curvature field),
  G₂(t) = G(t)/√(1 + G(t)²)  (the pulse field, `= sin arctan G`),
```

one has `θ' = G(θ)` in rear arclength and `K_* = G ∘ θ`, while in front
arclength the same state `w = θ ∘ x` obeys `w' = G₂(w)` and `y = G₂ ∘ w`
(because `ds/du = √(1 + K_*²)` and `tan δ = K_*`).  Since the state stays in
the compact interval `[0, π]`, the general theorem
`RelativeDerivatives.abs_iteratedDeriv_le` applies to both.

Main results:

* `HairpinRelative.pulseField_eq_sin_arctan` : `G₂ = sin ∘ arctan ∘ G`, i.e. the
  pulse field really is `sin δ` for the steering angle `δ` with `tan δ = K_*`;
* `HairpinRelative.abs_iteratedDeriv_curv_le` : `|K_*^{(j)}| ≤ C_j K_*`;
* `HairpinRelative.exists_pulseState` : the front arclength has an inverse `x`,
  and the state `w = θ ∘ x` obeys the autonomous equation `w' = G₂(w)`, so the
  steering pulse is `y = G₂ ∘ w`;
* `HairpinRelative.abs_iteratedDeriv_pulse_le` : `|y^{(j)}| ≤ D_j y`;
* `HairpinRelative.hairpin_relative_derivative_bounds` : both families of
  bounds for the hairpin of `HairpinArclength.exists_angle`.

The profile `f` is assumed here to be smooth and positive on the whole line
(the hairpin profile of Section 3 extended beyond `[0, π]`); only its values on
`[0, π]` matter for the conclusions.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ}

/-! ### The two fields -/

/-- The **curvature field** `G(t) = sin t / f(t)`: the curvature of the hairpin
as a function of its tangent angle. -/
def curvField (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.sin t / f t

/-- The **pulse field** `G₂ = G/√(1+G²)`: the steering pulse `sin δ` as a
function of the tangent angle of the rear track. -/
def pulseField (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  curvField f t / Real.sqrt (1 + curvField f t ^ 2)

theorem contDiff_curvField (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ContDiff ℝ ∞ (curvField f) :=
  Real.contDiff_sin.div hf fun t => (hfpos t).ne'

theorem sqrt_one_add_sq_pos (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) := by
  have : (0:ℝ) < 1 + x ^ 2 := by positivity
  exact Real.sqrt_pos.2 this

theorem contDiff_pulseField (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ContDiff ℝ ∞ (pulseField f) := by
  have hG := contDiff_curvField hf hfpos
  have hsq : ContDiff ℝ ∞ fun t => 1 + curvField f t ^ 2 :=
    contDiff_const.add (hG.pow 2)
  have hs : ContDiff ℝ ∞ fun t => Real.sqrt (1 + curvField f t ^ 2) :=
    hsq.sqrt fun t => by positivity
  exact hG.div hs fun t => (sqrt_one_add_sq_pos _).ne'

/-- The pulse field is `sin δ` for the steering angle `δ = arctan K_*`. -/
theorem pulseField_eq_sin_arctan (t : ℝ) :
    pulseField f t = Real.sin (Real.arctan (curvField f t)) :=
  (Real.sin_arctan _).symm

theorem curvField_nonneg (hfpos : ∀ t, 0 < f t) {t : ℝ} (ht : t ∈ Icc 0 π) :
    0 ≤ curvField f t := by
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ht
  exact div_nonneg hs (hfpos t).le

theorem pulseField_nonneg (hfpos : ∀ t, 0 < f t) {t : ℝ} (ht : t ∈ Icc 0 π) :
    0 ≤ pulseField f t :=
  div_nonneg (curvField_nonneg hfpos ht) (Real.sqrt_nonneg _)

/-! ### Relative derivative bounds for the curvature -/

/-- **Relative derivative bounds for the hairpin curvature.**  If the tangent
angle `θ` solves `θ' = G(θ)` — that is, if `u` is the arclength of the hairpin
— then the curvature `K_* = G ∘ θ` satisfies `|K_*^{(j)}| ≤ C_j K_*` for every
order `j`, with a constant independent of the point. -/
theorem abs_iteratedDeriv_curv_le (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
      |iteratedDeriv j (fun u => curvField f (theta u)) u| ≤ C * curvField f (theta u) :=
  RelativeDerivatives.abs_iteratedDeriv_le (contDiff_curvField hf hfpos) hderiv hmem
    (fun u => curvField_nonneg hfpos (hmem u)) j

/-! ### The front arclength and the pulse state -/

/-- The **front arclength** as a function of the rear arclength:
`σ(u) = ∫₀^u √(1 + K_*²)`. -/
def frontArclength (f : ℝ → ℝ) (theta : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..u, Real.sqrt (1 + curvField f (theta t) ^ 2)

/-- **The pulse state.**  The front arclength is a bijection of the line, and
along its inverse `x` the tangent angle `w = θ ∘ x` obeys the autonomous
equation `w' = G₂(w)`, whose field is precisely the steering pulse
`y = sin δ`. -/
theorem exists_pulseState (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) :
    ∃ x : ℝ → ℝ, (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, theta (x s) ∈ Icc 0 π) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) := by
  have hGc : Continuous (curvField f) := (contDiff_curvField hf hfpos).continuous
  have hthetac : Continuous theta :=
    Differentiable.continuous fun u => (hderiv u).differentiableAt
  set g : ℝ → ℝ := fun u => Real.sqrt (1 + curvField f (theta u) ^ 2) with hg
  have hgc : Continuous g := by
    have : Continuous fun u => 1 + curvField f (theta u) ^ 2 :=
      continuous_const.add ((hGc.comp hthetac).pow 2)
    exact this.sqrt
  have hg1 : ∀ u, (1:ℝ) ≤ g u := by
    intro u
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta u) ^ 2 := by nlinarith [sq_nonneg (curvField f (theta u))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ g u := Real.sqrt_le_sqrt h1
  have hsigma : ∀ u, HasDerivAt (frontArclength f theta) (g u) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  obtain ⟨x, hxinv⟩ :=
    ArclengthInverse.exists_rightInverse (c := 1) one_pos hsigma hg1
  have hxderiv : ∀ s, HasDerivAt x (1 / g (x s)) s :=
    ArclengthInverse.hasDerivAt_of_rightInverse one_pos hsigma hg1 hxinv
  refine ⟨x, hxinv, fun s => hmem _, fun s => ?_⟩
  have hcomp := (hderiv (x s)).comp s (hxderiv s)
  have hval : curvField f (theta (x s)) * (1 / g (x s)) = pulseField f (theta (x s)) := by
    rw [pulseField, hg]
    field_simp
  simpa [Function.comp, hval] using hcomp

/-! ### Relative derivative bounds for the steering pulse -/

/-- **Relative derivative bounds for the steering pulse.**  Along the pulse
state `w` — the tangent angle of the rear track read in the *front* arclength —
the pulse `y = G₂ ∘ w = sin δ` satisfies `|y^{(j)}| ≤ D_j y` for every order
`j`. -/
theorem abs_iteratedDeriv_pulse_le (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {w : ℝ → ℝ} (hmem : ∀ s, w s ∈ Icc 0 π)
    (hderiv : ∀ s, HasDerivAt w (pulseField f (w s)) s) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s,
      |iteratedDeriv j (fun s => pulseField f (w s)) s| ≤ D * pulseField f (w s) :=
  RelativeDerivatives.abs_iteratedDeriv_le (contDiff_pulseField hf hfpos) hderiv hmem
    (fun s => pulseField_nonneg hfpos (hmem s)) j

/-! ### The bounds for the hairpin -/

/-- **The relative derivative bounds of the lemma *Hairpin pulse estimates*.**
For a profile `f` smooth and positive on the line, the hairpin has an arclength
parametrization whose curvature `K_*` satisfies `|K_*^{(j)}| ≤ C_j K_*`, and the
associated steering pulse `y = sin δ`, read in the front arclength, satisfies
`|y^{(j)}| ≤ D_j y`, for every order `j`. -/
theorem hairpin_relative_derivative_bounds (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta : ℝ → ℝ, (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
        |iteratedDeriv j (fun u => curvField f (theta u)) u| ≤ C * curvField f (theta u)) ∧
      ∃ x : ℝ → ℝ, (∀ s, frontArclength f theta (x s) = s) ∧
        (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
        (∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ s,
          |iteratedDeriv j (fun s => pulseField f (theta (x s))) s|
            ≤ D * pulseField f (theta (x s))) := by
  have hcontf : Continuous f := hf.continuous
  -- a positive lower bound for `f` on the compact interval `[0, π]`
  obtain ⟨t₀, ht₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π)
      ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩ hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht =>
    hmin ⟨ht.1.le, ht.2.le⟩
  obtain ⟨theta, hmem, hval, -, -, -, hderiv⟩ :=
    HairpinArclength.exists_angle hcontf.continuousOn hm hlow
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  obtain ⟨x, hxinv, hxmem, hxderiv⟩ := exists_pulseState hf hfpos hmem' hderiv'
  exact ⟨theta, hmem, hval, hderiv', fun j =>
    abs_iteratedDeriv_curv_le hf hfpos hmem' hderiv' j,
    x, hxinv, hxderiv, fun j =>
      abs_iteratedDeriv_pulse_le hf hfpos hxmem hxderiv j⟩


/-! ### A worked instance

The hypotheses of `hairpin_relative_derivative_bounds` are consistent: the
constant profile `f ≡ 2` (a circle of radius `2`, viewed as a "profile") is
smooth and positive on the line. -/

example : ∃ theta : ℝ → ℝ, ∀ u, theta u ∈ Ioo 0 π := by
  obtain ⟨theta, hmem, -⟩ :=
    hairpin_relative_derivative_bounds (f := fun _ => 2) contDiff_const (fun _ => two_pos)
  exact ⟨theta, hmem⟩

end HairpinRelative
