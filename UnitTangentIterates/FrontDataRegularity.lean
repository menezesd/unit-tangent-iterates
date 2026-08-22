import Mathlib
import UnitTangentIterates.ParametricPrimitiveSmooth
import UnitTangentIterates.FrontFromPath

/-!
# Regularity of the front data of a path, from the regularity of the path

The rear path-distance bounds ask the front family `F(t,s) = X(t, s/P t)` of a
normal path and its tangent angle `Θ(t,s)` to be jointly `C⁴`.  Both are built
from the path: the front is the slice reparametrized by its own arclength, and
the tangent angle is the primitive of the curvature normalized at the marked
point.  This file derives their regularity from that of the data of the path.

* `contDiff_rescale` — the change of parameter `(t,s) ↦ (t, s/P t)` is as
  regular as the period `P`, which is positive;
* `contDiff_frontOfPath`, `contDiff_tangentOfPath`, `contDiff_curvOfPath` — the
  front, its unit tangent and its curvature are as regular as the data of the
  path;
* `contDiff_angleOfPath` — the tangent angle is jointly `C^{n+1}` as soon as the
  curvature is (by `ParametricPrimitiveSmooth.contDiff_primitive`) and the
  argument of the tangent at the marked point is `C^{n+1}` in the time.  The
  last is a genuine hypothesis: the argument is a branch of the angle, and a
  path whose marked tangent crosses the negative real axis has no continuous one
  of this form;
* `contDiffAt_arg`, `contDiff_arg_comp`, `contDiff_arg_tangentOfPath` — off the
  cut the argument is the imaginary part of the principal logarithm, hence
  smooth, so the last hypothesis does hold for every path whose marked tangent
  never points in the negative real direction.
-/

noncomputable section

open Function Set MeasureTheory FrontFromPath

namespace FrontDataRegularity

variable {X V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ} {n : ℕ}

/-- **The change of parameter to the arclength of the slice.**  `(t,s) ↦
(t, s / P t)` is as regular as `P`. -/
theorem contDiff_rescale (hP : ContDiff ℝ (n : ℕ) P) (hPne : ∀ t, P t ≠ 0) :
    ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => (p.1, p.2 / P p.1) :=
  contDiff_fst.prodMk (contDiff_snd.div (hP.comp contDiff_fst) fun p => hPne p.1)

/-- **The front family is as regular as the path.** -/
theorem contDiff_frontOfPath (hX : ContDiff ℝ (n : ℕ) (uncurry X))
    (hP : ContDiff ℝ (n : ℕ) P) (hPne : ∀ t, P t ≠ 0) :
    ContDiff ℝ (n : ℕ) (uncurry (frontOfPath X P)) := by
  have h : uncurry (frontOfPath X P)
      = (uncurry X) ∘ fun p : ℝ × ℝ => (p.1, p.2 / P p.1) := rfl
  rw [h]
  exact hX.comp (contDiff_rescale hP hPne)

/-- **The unit tangent of the slices is as regular as the velocity.** -/
theorem contDiff_tangentOfPath (hV : ContDiff ℝ (n : ℕ) (uncurry V))
    (hP : ContDiff ℝ (n : ℕ) P) (hPne : ∀ t, P t ≠ 0) :
    ContDiff ℝ (n : ℕ) (uncurry (tangentOfPath V P)) := by
  have h : uncurry (tangentOfPath V P)
      = fun p : ℝ × ℝ =>
        ((uncurry V) (p.1, p.2 / P p.1)) * (((P p.1 : ℝ) : ℂ))⁻¹ := by
    funext p; simp [uncurry, tangentOfPath, div_eq_mul_inv]
  rw [h]
  have hnum : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => (uncurry V) (p.1, p.2 / P p.1) :=
    hV.comp (contDiff_rescale hP hPne)
  have hden : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => (((P p.1 : ℝ) : ℂ))⁻¹ := by
    refine ContDiff.inv (𝕜' := ℂ) ?_ fun p => ?_
    · exact Complex.ofRealCLM.contDiff.comp (hP.comp contDiff_fst)
    · exact_mod_cast hPne p.1
  exact hnum.mul hden

/-- **The curvature of the slices is as regular as the data of the path.** -/
theorem contDiff_curvOfPath (hV : ContDiff ℝ (n : ℕ) (uncurry V))
    (hA : ContDiff ℝ (n : ℕ) (uncurry A)) (hP : ContDiff ℝ (n : ℕ) P)
    (hPne : ∀ t, P t ≠ 0) :
    ContDiff ℝ (n : ℕ) (uncurry (curvOfPath V A P)) := by
  have h : uncurry (curvOfPath V A P)
      = fun p : ℝ × ℝ =>
        (((starRingEnd ℂ) ((uncurry V) (p.1, p.2 / P p.1)))
          * ((uncurry A) (p.1, p.2 / P p.1))).im / P p.1 ^ 3 := rfl
  rw [h]
  have hresc := contDiff_rescale (P := P) hP hPne
  have hnum : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ =>
      (((starRingEnd ℂ) ((uncurry V) (p.1, p.2 / P p.1)))
        * ((uncurry A) (p.1, p.2 / P p.1))).im :=
    Complex.imCLM.contDiff.comp
      ((Complex.conjLIE.contDiff.comp (hV.comp hresc)).mul (hA.comp hresc))
  refine hnum.div ((hP.comp contDiff_fst).pow 3) fun p => ?_
  exact pow_ne_zero 3 (hPne p.1)

/-- **The tangent angle of the slices.**  It is jointly `C^{n+1}` as soon as the
curvature is and the argument of the tangent at the marked point is `C^{n+1}` in
the time. -/
theorem contDiff_angleOfPath
    (hcurv : ContDiff ℝ ((n : ℕ) + 1) (uncurry (curvOfPath V A P)))
    (harg : ContDiff ℝ ((n : ℕ) + 1) fun t => (tangentOfPath V P t 0).arg) :
    ContDiff ℝ ((n : ℕ) + 1) (uncurry (angleOfPath V A P)) := by
  have h : uncurry (angleOfPath V A P)
      = (fun p : ℝ × ℝ => (tangentOfPath V P p.1 0).arg)
        + uncurry fun t s => ∫ x in (0:ℝ)..s, curvOfPath V A P t x := by
    funext p
    simp [uncurry, angleOfPath]
  rw [h]
  exact (harg.comp contDiff_fst).add (ParametricPrimitiveSmooth.contDiff_primitive n hcurv)

/-! ### A branch of the argument along a curve avoiding the cut -/

/-- **The argument is smooth off the cut.**  On the slit plane it is the
imaginary part of the principal logarithm. -/
theorem contDiffAt_arg {z : ℂ} (h : z ∈ Complex.slitPlane) {m : WithTop ℕ∞} :
    ContDiffAt ℝ m (fun w : ℂ => w.arg) z := by
  have hlog : ContDiffAt ℝ m Complex.log z :=
    (Complex.contDiffAt_log h (n := m)).restrict_scalars ℝ
  refine (Complex.imCLM.contDiff.contDiffAt.comp z hlog).congr_of_eventuallyEq ?_
  filter_upwards with w
  simp [Function.comp, Complex.log_im]

/-- **The argument of a curve that never crosses the cut is as regular as the
curve.** -/
theorem contDiff_arg_comp {f : ℝ → ℂ} (hf : ContDiff ℝ (n : ℕ) f)
    (h : ∀ t, f t ∈ Complex.slitPlane) : ContDiff ℝ (n : ℕ) fun t => (f t).arg := by
  rw [contDiff_iff_contDiffAt]
  exact fun t => (contDiffAt_arg (h t)).comp t hf.contDiffAt

/-- **The branch hypothesis of `contDiff_angleOfPath` holds whenever the tangent
at the marked point stays off the cut.** -/
theorem contDiff_arg_tangentOfPath (hV : ContDiff ℝ (n : ℕ) (uncurry V))
    (hP : ContDiff ℝ (n : ℕ) P) (hPpos : ∀ t, 0 < P t)
    (hslit : ∀ t, V t 0 ∈ Complex.slitPlane) :
    ContDiff ℝ (n : ℕ) fun t => (tangentOfPath V P t 0).arg := by
  have hfun : (fun t => tangentOfPath V P t 0)
      = fun t : ℝ => (uncurry V) (t, 0) * (((P t : ℝ) : ℂ))⁻¹ := by
    funext t; simp [uncurry, tangentOfPath, div_eq_mul_inv]
  have hreg : ContDiff ℝ (n : ℕ) fun t => tangentOfPath V P t 0 := by
    rw [hfun]
    refine ContDiff.mul (hV.comp (contDiff_id.prodMk contDiff_const)) ?_
    refine ContDiff.inv (𝕜' := ℂ) (Complex.ofRealCLM.contDiff.comp hP) fun t => ?_
    exact_mod_cast (hPpos t).ne'
  refine contDiff_arg_comp hreg fun t => ?_
  have hP0 : (0 : ℝ) < P t := hPpos t
  have hre : (tangentOfPath V P t 0).re = (V t 0).re / P t := by
    simp [tangentOfPath, Complex.div_ofReal_re]
  have him : (tangentOfPath V P t 0).im = (V t 0).im / P t := by
    simp [tangentOfPath, Complex.div_ofReal_im]
  rcases hslit t with h | h
  · exact Or.inl (by rw [hre]; positivity)
  · refine Or.inr ?_
    rw [him]
    exact div_ne_zero h hP0.ne'

end FrontDataRegularity
