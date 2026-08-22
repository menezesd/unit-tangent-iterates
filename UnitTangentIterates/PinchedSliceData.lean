import Mathlib
import UnitTangentIterates.PinchedPathSlices

/-!
# The marked datum of a slice of a path

The `C²` estimate compares the selected inverses of the two *ends* of an
admissible path.  To subdivide a path one has to name its intermediate slices
as marked curves, that is, as members of `MarkedSpace.Data`: a bounded
continuous curve together with its velocity and its acceleration.

This file builds that datum.  A slice of an admissible path is a closed curve,
hence bounded together with its two parameter derivatives
(`MarkedSpace.exists_bound_of_periodic`), and `sliceData` packages the three of
them.  Its velocity and acceleration components *are* the derivatives of its
curve (`hasDerivAt_sliceData`, `hasDerivAt_sliceData'`), which is exactly what
the estimate asks of its two ends, and at a time at which the family is a given
marked datum whose components are the derivatives of its curve, the slice datum
*is* that datum (`sliceData_eq`), so that the ends of a subdivision agree with
the ends of the path.

Main results: `sliceBCF`, `sliceData`, `hasDerivAt_sliceData`,
`hasDerivAt_sliceData'`, `sliceData_eq`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath
open scoped BoundedContinuousFunction

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist

variable {kminP kh : ℝ} {p q : Data}

/-! ### A closed curve as a bounded continuous function -/

/-- A continuous `1`-periodic curve, as a bounded continuous function. -/
def sliceBCF (f : ℝ → ℂ) (hcont : Continuous f) (hper : Periodic f 1) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hcont
    (Classical.choose (MarkedSpace.exists_bound_of_periodic hcont hper))
    (Classical.choose_spec (MarkedSpace.exists_bound_of_periodic hcont hper))

@[simp] theorem coe_sliceBCF {f : ℝ → ℂ} (hcont : Continuous f) (hper : Periodic f 1) :
    ⇑(sliceBCF f hcont hper) = f := rfl

/-! ### The marked datum of a slice -/

section SliceData

variable {X : ℝ → ℝ → ℂ}

/-- The velocity of a family of closed curves is `1`-periodic in the
parameter. -/
theorem periodic_pathVel (hX : ContDiff ℝ (1 : ℕ) (uncurry X))
    (hper : ∀ t, Periodic (X t) 1) (t : ℝ) : Periodic (pathVel X t) 1 :=
  periodic_partialArc (hX.differentiable (by norm_num)) hper t

/-- The acceleration of a family of closed curves is `1`-periodic in the
parameter. -/
theorem periodic_pathAcc (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    (hper : ∀ t, Periodic (X t) 1) (t : ℝ) : Periodic (pathAcc X t) 1 := by
  have hV : ContDiff ℝ (1 : ℕ) (uncurry (pathVel X)) :=
    contDiff_partialArc_self (n := 1) (by exact_mod_cast hX)
  exact periodic_partialArc (hV.differentiable (by norm_num))
    (periodic_pathVel (hX.of_le (by norm_num)) hper) t

theorem contDiff_uncurry_pathVel (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) :
    ContDiff ℝ (1 : ℕ) (uncurry (pathVel X)) :=
  contDiff_partialArc_self (n := 1) (by exact_mod_cast hX)

theorem contDiff_uncurry_pathAcc (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) :
    ContDiff ℝ (0 : ℕ) (uncurry (pathAcc X)) :=
  contDiff_partialArc_self (n := 0) (by exact_mod_cast contDiff_uncurry_pathVel hX)

theorem continuous_slice_curve (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) (t : ℝ) :
    Continuous (X t) := (contDiff_slice hX t).continuous

theorem continuous_slice_pathVel (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) (t : ℝ) :
    Continuous (pathVel X t) := (contDiff_slice (contDiff_uncurry_pathVel hX) t).continuous

theorem continuous_slice_pathAcc (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) (t : ℝ) :
    Continuous (pathAcc X t) := (contDiff_slice (contDiff_uncurry_pathAcc hX) t).continuous

/-- **The marked datum of the slice at time `t`**: the slice, its velocity and
its acceleration. -/
def sliceData (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) (hper : ∀ t, Periodic (X t) 1)
    (t : ℝ) : Data :=
  (sliceBCF (X t) (continuous_slice_curve hX t) (hper t),
   sliceBCF (pathVel X t) (continuous_slice_pathVel hX t)
      (periodic_pathVel (hX.of_le (by norm_num)) hper t),
   sliceBCF (pathAcc X t) (continuous_slice_pathAcc hX t) (periodic_pathAcc hX hper t))

variable {hX : ContDiff ℝ (2 : ℕ) (uncurry X)} {hper : ∀ t, Periodic (X t) 1} {t : ℝ}

@[simp] theorem sliceData_fst : ⇑(sliceData hX hper t).1 = X t := rfl

@[simp] theorem sliceData_snd_fst : ⇑(sliceData hX hper t).2.1 = pathVel X t := rfl

@[simp] theorem sliceData_snd_snd : ⇑(sliceData hX hper t).2.2 = pathAcc X t := rfl

/-- The velocity component of a slice datum is the derivative of its curve. -/
theorem hasDerivAt_sliceData (u : ℝ) :
    HasDerivAt (⇑(sliceData hX hper t).1) ((sliceData hX hper t).2.1 u) u :=
  hasDerivAt_partialArc (hX.differentiable (by norm_num)) t u

/-- The acceleration component of a slice datum is the derivative of its
velocity. -/
theorem hasDerivAt_sliceData' (u : ℝ) :
    HasDerivAt (⇑(sliceData hX hper t).2.1) ((sliceData hX hper t).2.2 u) u := by
  have hV : ContDiff ℝ (1 : ℕ) (uncurry (pathVel X)) :=
    contDiff_partialArc_self (n := 1) (by exact_mod_cast hX)
  exact hasDerivAt_partialArc (hV.differentiable (by norm_num)) t u

/-- **A slice datum is the marked curve it is a slice of.**  At a time at which
the family is the curve of a marked datum whose two other components are the
derivatives of that curve, the slice datum is that datum. -/
theorem sliceData_eq (h : ∀ u, X t u = p.1 u)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) :
    sliceData hX hper t = p := by
  have h1 : ⇑(sliceData hX hper t).1 = ⇑p.1 := funext h
  have h2 : ⇑(sliceData hX hper t).2.1 = ⇑p.2.1 := by
    funext u
    have hA : HasDerivAt (⇑p.1) (pathVel X t u) u := by
      have := hasDerivAt_partialArc (hX.differentiable (by norm_num)) t u
      rwa [show X t = ⇑p.1 from funext h] at this
    exact hA.unique (hpd u)
  refine Prod.ext (DFunLike.coe_injective h1) (Prod.ext (DFunLike.coe_injective h2) ?_)
  refine DFunLike.coe_injective (funext fun u => ?_)
  have hV : ContDiff ℝ (1 : ℕ) (uncurry (pathVel X)) :=
    contDiff_partialArc_self (n := 1) (by exact_mod_cast hX)
  have hA : HasDerivAt (⇑p.2.1) (pathAcc X t u) u := by
    have := hasDerivAt_partialArc (hV.differentiable (by norm_num)) t u
    rwa [show pathVel X t = ⇑p.2.1 from h2] at this
  exact hA.unique (hpd2 u)

end SliceData

/-! ### The slice data of an admissible path -/

variable {Γ : NormalPath p q}

/-- The slice data of an admissible path. -/
def pinchedSliceData (hΓ : IsPinchedPath kminP kh Γ) (t : ℝ) : Data :=
  sliceData (hΓ.smooth.of_le (by norm_num)) hΓ.per t

@[simp] theorem pinchedSliceData_fst (hΓ : IsPinchedPath kminP kh Γ) (t : ℝ) :
    ⇑(pinchedSliceData hΓ t).1 = Γ.X t := rfl

theorem hasDerivAt_pinchedSliceData (hΓ : IsPinchedPath kminP kh Γ) (t u : ℝ) :
    HasDerivAt (⇑(pinchedSliceData hΓ t).1) ((pinchedSliceData hΓ t).2.1 u) u :=
  hasDerivAt_sliceData u

theorem hasDerivAt_pinchedSliceData' (hΓ : IsPinchedPath kminP kh Γ) (t u : ℝ) :
    HasDerivAt (⇑(pinchedSliceData hΓ t).2.1) ((pinchedSliceData hΓ t).2.2 u) u :=
  hasDerivAt_sliceData' u

/-- Every slice datum of an admissible path is an admissible curve. -/
theorem isPinchedCurve_pinchedSliceData (hΓ : IsPinchedPath kminP kh Γ) (t : ℝ) :
    IsPinchedCurve kminP kh (pinchedSliceData hΓ t) :=
  isPinchedCurve_of_slice hΓ (t₀ := t) (fun _ => rfl)

/-- At time `0` the slice datum of an admissible path is its initial marked
curve. -/
theorem pinchedSliceData_zero (hΓ : IsPinchedPath kminP kh Γ)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) :
    pinchedSliceData hΓ 0 = p :=
  sliceData_eq Γ.start hpd hpd2

/-- At the final time the slice datum of an admissible path is its terminal
marked curve. -/
theorem pinchedSliceData_final (hΓ : IsPinchedPath kminP kh Γ)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u) :
    pinchedSliceData hΓ Γ.T = q :=
  sliceData_eq Γ.finish hqd hqd2

end PinchedPath
