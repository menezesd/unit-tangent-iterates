import Mathlib
import UnitTangentIterates.SteeringArclengthJointC1
import UnitTangentIterates.SelectedChangeOfVariable

/-!
# The change of variable of the selected inverse, from the front curvature

`SelectedChangeOfVariable.lean` builds, along a path of fronts, the change of
variable `sf(t, ·)` from the rear to the front arclength, and proves it jointly
`C¹` — but it *assumes* the family of steering angles to be jointly `C¹`, in
the shape of a jointly continuous parameter derivative `dt`.

`SteeringArclengthJointC1.lean` now produces exactly that regularity from the
front curvature.  This file joins the two: **for a path of fronts whose
curvature is jointly continuous, Lipschitz and once differentiable in the path
parameter (with a uniform quadratic Taylor bound), the selected steering angle
is jointly `C¹` and so is the change of variable it induces**, whose existence
is produced rather than assumed.

Main results:

* `contDiff_one_sf_of_curvature` — joint `C¹` regularity of a given change of
  variable;
* `exists_sf_of_curvature` — existence of the change of variable together with
  its joint `C¹` regularity and that of the steering angle.
-/

noncomputable section

open Function Set Real

namespace SelectedSteeringChangeOfVariable

open SteeringArclengthJointC1 RearTrack

variable {K Kd delta : ℝ → ℝ → ℝ} {P kap Klip CK : ℝ}

/-- **The change of variable of the selected inverse is jointly `C¹`**, on
hypotheses bearing on the front curvature alone. -/
theorem contDiff_one_sf_of_curvature (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) {sf : ℝ → ℝ → ℝ} (hsf : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    ContDiff ℝ 1 (uncurry sf) := by
  have hdc : Continuous (uncurry delta) :=
    continuous_uncurry_delta_arc hP hkap0 hkap1 hsol hper hstrip hKlip
  have hdt : ∀ t s, HasDerivAt (fun r => delta r s) (arcVariation Kd delta P t s) t :=
    fun t s => hasDerivAt_param_arc hP hkap0 hkap1 hKdcont hsol hper hstrip hKdper hKlip
      hKtaylor hCK t s
  have hcosC : Continuous (uncurry fun a s => Real.cos (delta a s)) :=
    Real.continuous_cos.comp hdc
  have hdtc : Continuous (uncurry (arcVariation Kd delta P)) := by
    have hpos : ∀ a, 0 < PeriodicGreen.prim (fun s => Real.cos (delta a s)) P := fun a =>
      prim_cos_pos hP hkap0 hkap1 hsol hstrip a
    exact PeriodicGreenJoint.continuous_periodicGreen_param
      (A := fun a s => Real.cos (delta a s)) (F := Kd) (l := P) hcosC hKdcont hpos
  exact SelectedChangeOfVariable.contDiff_one_sf hkap0 hkap1 hdc hdt hdtc
    (fun t s => (hstrip t s).1) (fun t s => (hstrip t s).2) hsf

/-- **The change of variable of the selected inverse exists and is jointly
`C¹`**, together with the joint `C¹` regularity of the selected steering angle
itself — everything on hypotheses bearing on the front curvature alone. -/
theorem exists_sf_of_curvature (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) :
    ContDiff ℝ 1 (uncurry delta) ∧
      ∃ sf : ℝ → ℝ → ℝ, (∀ t x, rearArclength (delta t) (sf t x) = x) ∧
        ContDiff ℝ 1 (uncurry sf) := by
  have hdc : Continuous (uncurry delta) :=
    continuous_uncurry_delta_arc hP hkap0 hkap1 hsol hper hstrip hKlip
  obtain ⟨sf, hsf⟩ := SelectedChangeOfVariable.exists_sf_family hkap0 hkap1 hdc
    (fun t s => (hstrip t s).1) (fun t s => (hstrip t s).2)
  refine ⟨contDiff_one_uncurry_delta_arc hP hkap0 hkap1 hKcont hKdcont hsol hper hstrip hKdper
      hKlip hKtaylor hCK, sf, hsf, ?_⟩
  exact contDiff_one_sf_of_curvature (K := K) hP hkap0 hkap1 hKdcont hsol hper hstrip hKdper
    hKlip hKtaylor hCK hsf

end SelectedSteeringChangeOfVariable
