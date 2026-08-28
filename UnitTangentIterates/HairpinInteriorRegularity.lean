import Mathlib
import UnitTangentIterates.HairpinRelativeDerivatives
import UnitTangentIterates.HairpinPulseSmooth

/-!
# Interior regularity of the hairpin fields

The theorem *Translating hairpin* of *A Noncircular Oval with Convex Unit-Tangent
Iterates* produces the profile with

  `f_ε ∈ C^∞(0, π)`,

and its proof closes with: *"No endpoint values are assigned; the construction
uses only the profile on `(0,π)` and the uniform barrier bounds."*

`HairpinRelativeDerivatives.contDiff_curvField` and `contDiff_pulseField`
nevertheless ask for `ContDiff ℝ ∞ f` on all of `ℝ`, and that requirement
propagates through the whole hairpin chain.  It is not what the paper proves,
and it is not needed: both fields are **pointwise** in `f`,

  `curvField f t = sin t / f t`,   `pulseField f t = G/√(1+G²)`,

so their regularity at an angle `t` depends only on the regularity of `f` at `t`.

This file records the localized statements, and the one bridge that makes them
enough: everything downstream evaluates the fields at angles `θ(u)` which lie in
the *open* interval `(0,π)` for every `u`, and a `C^∞` map on an open set
composed with a globally `C^∞` map into that set is globally `C^∞`.  So interior
regularity of the profile still yields the *global* smoothness in the arclength
parameter that the quantitative packages consume.

Main results:

* `contDiffOn_curvField`, `contDiffOn_pulseField` — the two fields are `C^∞` on
  `(0,π)` when the profile is;
* `contDiff_comp_of_mapsTo` — the composition bridge;
* `contDiff_curvField_comp`, `contDiff_pulseField_comp` — the conclusion in the
  shape the quantitative packages ask for, from interior data only;
* `contDiff_nat_hairpin_coordinates` — the regularity half of
  `HairpinPulseSmooth.exists_smooth_hairpin_pulse` with the global profile
  hypothesis removed;
* `exists_pulseState_of_continuous_comp`, `exists_hairpin_coordinates_interior`
  — the hairpin coordinates and all their finite smoothness orders, from
  `ContDiffOn ℝ ∞ f (Ioo 0 π)` and a barrier lower bound alone.
-/

noncomputable section

open Set
open scoped ContDiff

namespace HairpinInteriorRegularity

open HairpinRelative

variable {f : ℝ → ℝ}

/-- **The curvature field is `C^∞` on the open angle interval** when the profile
is.  `curvField f t = sin t / f t` is pointwise in `f`, so no regularity of `f`
beyond `(0,π)` is used. -/
theorem contDiffOn_curvField (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t) :
    ContDiffOn ℝ ∞ (curvField f) (Ioo 0 Real.pi) :=
  Real.contDiff_sin.contDiffOn.div hf fun t ht => (hfpos t ht).ne'

/-- **The pulse field is `C^∞` on the open angle interval** when the profile
is. -/
theorem contDiffOn_pulseField (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t) :
    ContDiffOn ℝ ∞ (pulseField f) (Ioo 0 Real.pi) := by
  have hG := contDiffOn_curvField hf hfpos
  have hsq : ContDiffOn ℝ ∞ (fun t => 1 + curvField f t ^ 2) (Ioo 0 Real.pi) :=
    contDiffOn_const.add (hG.pow 2)
  have hs : ContDiffOn ℝ ∞ (fun t => Real.sqrt (1 + curvField f t ^ 2))
      (Ioo 0 Real.pi) := hsq.sqrt fun t _ => by positivity
  exact hG.div hs fun t _ => (sqrt_one_add_sq_pos _).ne'

/-- **The composition bridge.**  A map that is `C^∞` on the *open* interval
`(0,π)`, precomposed with a globally `C^∞` map taking values in `(0,π)`, is
globally `C^∞`.  This is what turns interior regularity of the profile into the
global smoothness in the arclength parameter that the quantitative hairpin
packages consume: every angle they use lies in the open interval. -/
theorem contDiff_comp_of_mapsTo {G g : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioo 0 Real.pi)) (hg : ContDiff ℝ ∞ g)
    (hmaps : ∀ s, g s ∈ Ioo (0:ℝ) Real.pi) :
    ContDiff ℝ ∞ fun s => G (g s) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  exact (hG.contDiffAt (isOpen_Ioo.mem_nhds (hmaps s))).comp s hg.contDiffAt

/-- The curvature field along an angle map into the open interval is globally
`C^∞`, from interior regularity of the profile alone. -/
theorem contDiff_curvField_comp {g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t)
    (hg : ContDiff ℝ ∞ g) (hmaps : ∀ s, g s ∈ Ioo (0:ℝ) Real.pi) :
    ContDiff ℝ ∞ fun s => curvField f (g s) :=
  contDiff_comp_of_mapsTo (contDiffOn_curvField hf hfpos) hg hmaps

/-- The pulse field along an angle map into the open interval is globally
`C^∞`, from interior regularity of the profile alone.  This is the shape of the
`smooth_pulse` field of `PaperHairpinQuantitativeData.Data`. -/
theorem contDiff_pulseField_comp {g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t)
    (hg : ContDiff ℝ ∞ g) (hmaps : ∀ s, g s ∈ Ioo (0:ℝ) Real.pi) :
    ContDiff ℝ ∞ fun s => pulseField f (g s) :=
  contDiff_comp_of_mapsTo (contDiffOn_pulseField hf hfpos) hg hmaps

/-- Every finite order, from the infinite-order interior hypothesis. -/
theorem contDiffOn_pulseField_nat (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (pulseField f) (Ioo 0 Real.pi) :=
  (contDiffOn_pulseField hf hfpos).of_le (by exact_mod_cast le_top)

/-- Every finite order, from the infinite-order interior hypothesis. -/
theorem contDiffOn_curvField_nat (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (curvField f) (Ioo 0 Real.pi) :=
  (contDiffOn_curvField hf hfpos).of_le (by exact_mod_cast le_top)

/-- **The regularity half of `HairpinPulseSmooth.exists_smooth_hairpin_pulse`,
from interior data only.**  Given the hairpin coordinates — the angle `θ` with
values in the open interval and its autonomous equation `θ' = G ∘ θ`, and the
state `w = θ ∘ x` with `w' = G₂ ∘ w` — the angle, the state and the pulse have
every finite smoothness order, using the profile only on `(0, π)`.

This is the step at which the global `ContDiff ℝ ∞ f` hypothesis entered the
hairpin chain; the paper provides only `f ∈ C^∞(0,π)`, and that is enough,
because `θ` and `w` never leave the open interval. -/
theorem contDiff_nat_hairpin_coordinates
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t)
    {theta x : ℝ → ℝ}
    (hmem : ∀ u, theta u ∈ Ioo 0 Real.pi)
    (htheta : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s) :
    (∀ n : ℕ, ContDiff ℝ (n : ℕ) theta) ∧
    (∀ n : ℕ, ContDiff ℝ (n : ℕ) fun s => theta (x s)) ∧
    (∀ n : ℕ, ContDiff ℝ (n : ℕ) fun s => pulseField f (theta (x s))) := by
  have hthetaC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) theta :=
    HairpinPulseSmooth.contDiff_nat_of_autonomousOn isOpen_Ioo hmem
      (contDiffOn_curvField_nat hf hfpos) htheta
  have hwmem : ∀ s, theta (x s) ∈ Ioo 0 Real.pi := fun s => hmem (x s)
  have hwC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) fun s => theta (x s) :=
    HairpinPulseSmooth.contDiff_nat_of_autonomousOn isOpen_Ioo hwmem
      (contDiffOn_pulseField_nat hf hfpos) hw
  exact ⟨hthetaC, hwC,
    HairpinPulseSmooth.contDiff_nat_compOn isOpen_Ioo hwmem
      (contDiffOn_pulseField_nat hf hfpos) hwC⟩

/-! ### The hairpin coordinates from interior data -/

/-- **`exists_pulseState` with the global profile hypothesis removed.**  The
original uses `ContDiff ℝ ∞ f` and global positivity for one thing only:
continuity of `curvField f ∘ θ`.  Taking that as the hypothesis makes the
statement strictly more general, and it is supplied by interior data through
`contDiffOn_curvField` because `θ` never leaves `(0,π)`. -/
theorem exists_pulseState_of_continuous_comp {theta : ℝ → ℝ}
    (hGc : Continuous fun u => curvField f (theta u))
    (hmem : ∀ u, theta u ∈ Icc 0 Real.pi)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) :
    ∃ x : ℝ → ℝ, (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, theta (x s) ∈ Icc 0 Real.pi) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) := by
  set g : ℝ → ℝ := fun u => Real.sqrt (1 + curvField f (theta u) ^ 2) with hg
  have hgc : Continuous g := by
    have h : Continuous fun u => 1 + curvField f (theta u) ^ 2 :=
      continuous_const.add (hGc.pow 2)
    exact h.sqrt
  have hg1 : ∀ u, (1:ℝ) ≤ g u := by
    intro u
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta u) ^ 2 := by
      nlinarith [sq_nonneg (curvField f (theta u))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ g u := Real.sqrt_le_sqrt h1
  have hsigma : ∀ u, HasDerivAt (frontArclength f theta) (g u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  obtain ⟨x, hxinv⟩ :=
    ArclengthInverse.exists_rightInverse (c := 1) one_pos hsigma hg1
  have hxderiv : ∀ s, HasDerivAt x (1 / g (x s)) s :=
    ArclengthInverse.hasDerivAt_of_rightInverse one_pos hsigma hg1 hxinv
  refine ⟨x, hxinv, fun s => hmem _, fun s => ?_⟩
  have hcomp := (hderiv (x s)).comp s (hxderiv s)
  have hval : curvField f (theta (x s)) * (1 / g (x s))
      = pulseField f (theta (x s)) := by
    rw [pulseField, hg]
    field_simp
  simpa [Function.comp, hval] using hcomp

/-- **The hairpin coordinates and their regularity, from interior data alone.**
The angle `θ` with values in `(0,π)`, the inverse front arclength `x`, their
autonomous equations, and every finite smoothness order of `θ`, of the state
`w = θ ∘ x` and of the pulse `y = G₂ ∘ w` — all from

* `ContDiffOn ℝ ∞ f (Ioo 0 π)`, the regularity the paper proves, and
* a uniform positive lower bound for `f` on `(0,π)`, the paper's barrier bound,

with no hypothesis at, or beyond, the endpoints.  Compare
`HairpinRelativeDerivatives.hairpin_relative_derivative_bounds` and
`HairpinPulseSmooth.exists_smooth_hairpin_pulse`, which ask for
`ContDiff ℝ ∞ f` and positivity on the whole line.

What is deliberately *not* included is the relative-derivative constants
`|y^{(j)}| ≤ D_j y`: those do not follow from interior regularity (see
`RelativeDerivatives.abs_iteratedDeriv_le`, whose constant comes from
compactness of `Icc 0 π`), and the paper obtains them from the translator
equation instead. -/
theorem exists_hairpin_coordinates_interior {m : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) Real.pi, m ≤ f t) :
    ∃ theta x : ℝ → ℝ,
      (∀ u, theta u ∈ Ioo 0 Real.pi) ∧
      (∀ u, Hairpin.hairpinArclength f (Real.pi / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ) theta) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ) fun s => theta (x s)) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ) fun s => pulseField f (theta (x s))) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) Real.pi, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  obtain ⟨theta, hmem, hval, -, -, hthetac, hderiv⟩ :=
    HairpinArclength.exists_angle hf.continuousOn hm hlow
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  have hGc : Continuous fun u => curvField f (theta u) :=
    (contDiffOn_curvField hf hfpos).continuousOn.comp_continuous hthetac hmem
  obtain ⟨x, hxinv, -, hw⟩ :=
    exists_pulseState_of_continuous_comp hGc
      (fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩) hderiv'
  obtain ⟨hthetaC, hwC, hyC⟩ :=
    contDiff_nat_hairpin_coordinates hf hfpos hmem hderiv' hw
  exact ⟨theta, x, hmem, hval, hderiv', hxinv, hw, hthetaC, hwC, hyC⟩

/-- Global regularity of the profile is a special case: this recovers
`HairpinRelativeDerivatives.contDiff_curvField` restricted to the interval, so
nothing is lost by stating the hypotheses locally. -/
theorem contDiffOn_curvField_of_contDiff (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ContDiffOn ℝ ∞ (curvField f) (Ioo 0 Real.pi) :=
  contDiffOn_curvField hf.contDiffOn fun t _ => hfpos t

end HairpinInteriorRegularity
