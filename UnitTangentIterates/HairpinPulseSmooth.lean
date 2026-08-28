import Mathlib
import UnitTangentIterates.HairpinPulseIdentity

/-!
# Smoothness of the hairpin angle and pulse coordinates

The hairpin estimates use two autonomous scalar flows.  In rear arclength the
tangent angle satisfies `theta' = G(theta)`, while in front arclength
`w = theta ∘ x` satisfies `w' = G₂(w)`.  Since both fields are smooth, the
solutions, the steering pulse `G₂ ∘ w`, and the inverse arclength `x` have every
finite `ContDiff` order.  This file records the regularity bootstrap explicitly.
-/

noncomputable section

open Real Set
open scoped ContDiff

namespace HairpinPulseSmooth

/-- A global solution of a smooth scalar autonomous ODE has every finite
`ContDiff` order. -/
theorem contDiff_nat_of_autonomous {F u : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hu : ∀ x, HasDerivAt u (F (u x)) x) : ∀ n : ℕ, ContDiff ℝ (n : ℕ) u := by
  intro n
  induction n with
  | zero =>
      simpa [contDiff_zero] using
        (Differentiable.continuous fun x => (hu x).differentiableAt)
  | succ n ih =>
      have hdiff : Differentiable ℝ u := fun x => (hu x).differentiableAt
      have hderiv : deriv u = fun x => F (u x) := funext fun x => (hu x).deriv
      have hFn : ContDiff ℝ (n : ℕ) F := hF.of_le (by exact_mod_cast le_top)
      have hrhs : ContDiff ℝ (n : ℕ) (fun x => F (u x)) := hFn.comp ih
      have key : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) u := by
        rw [contDiff_succ_iff_deriv]
        refine ⟨hdiff, by simp, ?_⟩
        rw [hderiv]
        exact hrhs
      exact_mod_cast key

/-- Composition with a smooth scalar field preserves every finite smoothness
order. -/
theorem contDiff_nat_comp {F u : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hu : ∀ n : ℕ, ContDiff ℝ (n : ℕ) u) :
    ∀ n : ℕ, ContDiff ℝ (n : ℕ) (fun x => F (u x)) := by
  intro n
  exact (hF.of_le (by exact_mod_cast le_top)).comp (hu n)

/-- Localized autonomous bootstrap.  Global smoothness of the vector field is
unnecessary when the whole solution remains in an open state domain. -/
theorem contDiff_nat_of_autonomousOn {F u : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hmem : ∀ x, u x ∈ U)
    (hF : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ) F U)
    (hu : ∀ x, HasDerivAt u (F (u x)) x) :
    ∀ n : ℕ, ContDiff ℝ (n : ℕ) u := by
  intro n
  induction n with
  | zero =>
      simpa [contDiff_zero] using
        (Differentiable.continuous fun x => (hu x).differentiableAt)
  | succ n ih =>
      have hdiff : Differentiable ℝ u := fun x => (hu x).differentiableAt
      have hderiv : deriv u = fun x => F (u x) := funext fun x => (hu x).deriv
      have hrhs : ContDiff ℝ (n : ℕ) (fun x => F (u x)) := by
        rw [contDiff_iff_contDiffAt]
        intro x
        have hFat : ContDiffAt ℝ (n : ℕ) F (u x) :=
          (hF n (u x) (hmem x)).contDiffAt (hU.mem_nhds (hmem x))
        exact hFat.comp x ih.contDiffAt
      have key : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) u := by
        rw [contDiff_succ_iff_deriv]
        refine ⟨hdiff, by simp, ?_⟩
        rw [hderiv]
        exact hrhs
      exact_mod_cast key

/-- Composition with a field smooth only on the open image domain. -/
theorem contDiff_nat_compOn {F u : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hmem : ∀ x, u x ∈ U)
    (hF : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ) F U)
    (hu : ∀ n : ℕ, ContDiff ℝ (n : ℕ) u) :
    ∀ n : ℕ, ContDiff ℝ (n : ℕ) (fun x => F (u x)) := by
  intro n
  rw [contDiff_iff_contDiffAt]
  intro x
  have hFat : ContDiffAt ℝ (n : ℕ) F (u x) :=
    (hF n (u x) (hmem x)).contDiffAt (hU.mem_nhds (hmem x))
  exact hFat.comp x (hu n).contDiffAt

open HairpinRelative

/-- **Smooth hairpin pulse coordinates.**  A smooth positive profile admits
the rear-arclength angle `theta`, inverse front arclength `x`, state
`w = theta ∘ x`, and pulse `y = G₂ ∘ w`; all four functions have every
finite `ContDiff` order.  The derivative identities retained in the conclusion
are the exact autonomous equations used in the bootstrap. -/
theorem exists_smooth_hairpin_pulse (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta x : ℝ → ℝ,
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s) ∧
      (∀ s, HasDerivAt x (Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)) s) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ) theta) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ) x) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ) (fun s => theta (x s))) ∧
      (∀ n : ℕ, ContDiff ℝ (n : ℕ)
        (fun s => pulseField f (theta (x s)))) := by
  obtain ⟨theta, hmem, hval, htheta, -, x, hxinv, hw, -⟩ :=
    hairpin_relative_derivative_bounds hf hfpos
  let w : ℝ → ℝ := fun s => theta (x s)
  have hthetaC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) theta :=
    contDiff_nat_of_autonomous (contDiff_curvField hf hfpos) htheta
  have hw' : ∀ s, HasDerivAt w (pulseField f (w s)) s := by
    simpa [w] using hw
  have hwC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) w :=
    contDiff_nat_of_autonomous (contDiff_pulseField hf hfpos) hw'
  have hyC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) (fun s => pulseField f (w s)) :=
    contDiff_nat_comp (contDiff_pulseField hf hfpos) hwC
  have hx : ∀ s, HasDerivAt x (Real.sqrt (1 - pulseField f (w s) ^ 2)) s := by
    simpa [w] using
      (HairpinPulseIdentity.hasDerivAt_pulseInverse hf hfpos htheta hxinv)
  have hxC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) x := by
    intro n
    induction n with
    | zero =>
        simpa [contDiff_zero] using
          (Differentiable.continuous fun s => (hx s).differentiableAt)
    | succ n ih =>
        have hdiff : Differentiable ℝ x := fun s => (hx s).differentiableAt
        have hderiv : deriv x = fun s => Real.sqrt (1 - pulseField f (w s) ^ 2) :=
          funext fun s => (hx s).deriv
        have harg : ContDiff ℝ (n : ℕ) (fun s => 1 - pulseField f (w s) ^ 2) :=
          contDiff_const.sub ((hyC n).pow 2)
        have hpos : ∀ s, 0 < 1 - pulseField f (w s) ^ 2 := by
          intro s
          rw [HairpinPulseIdentity.one_sub_pulseField_sq]
          positivity
        have hrhs : ContDiff ℝ (n : ℕ)
            (fun s => Real.sqrt (1 - pulseField f (w s) ^ 2)) :=
          harg.sqrt (fun s => (hpos s).ne')
        have key : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) x := by
          rw [contDiff_succ_iff_deriv]
          refine ⟨hdiff, by simp, ?_⟩
          rw [hderiv]
          exact hrhs
        exact_mod_cast key
  refine ⟨theta, x, hmem, hval, htheta, hxinv, hw, ?_, hthetaC, hxC, ?_, ?_⟩
  · simpa [w] using hx
  · simpa [w] using hwC
  · simpa [w] using hyC

end HairpinPulseSmooth
