import UnitTangentIterates.RearOwnFrameDrift
import UnitTangentIterates.TimeDependentSpatialReanchoring

/-!
# Spatial frame certificates under moving reanchoring

A time-dependent translation of the spatial variable preserves spatial `C²`
regularity even when the translating phase is only continuous in time.  The
same applies to the normalized tangential field obtained by subtracting its
value at the moving base point.
-/

noncomputable section

open Function

namespace RearOwnFrameDrift

namespace SpatialC2

variable {xi rho : ℝ → ℝ → ℝ}

private theorem pairMap_continuous {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (TimeDependentSpatialReanchoring.pairMap q) := by
  exact continuous_fst.prodMk
    (continuous_snd.add (hq.comp continuous_fst))

/-- A continuous time-dependent spatial translation preserves a spatial `C²`
certificate.  No time derivative of the translating phase is required. -/
def shift {xi : ℝ → ℝ → ℝ} {q : ℝ → ℝ} (S : SpatialC2 xi)
    (hq : Continuous q) :
    SpatialC2 (TimeDependentSpatialReanchoring.shift xi q) where
  xi1 := TimeDependentSpatialReanchoring.shift S.xi1 q
  xi2 := TimeDependentSpatialReanchoring.shift S.xi2 q
  deriv1 := TimeDependentSpatialReanchoring.shift_spatial_deriv S.deriv1
  deriv2 := TimeDependentSpatialReanchoring.shift_spatial_deriv S.deriv2
  continuous0 := by
    simpa [TimeDependentSpatialReanchoring.shift,
      TimeDependentSpatialReanchoring.pairMap, Function.uncurry] using
      S.continuous0.comp (pairMap_continuous hq)
  continuous1 := by
    simpa [TimeDependentSpatialReanchoring.shift,
      TimeDependentSpatialReanchoring.pairMap, Function.uncurry] using
      S.continuous1.comp (pairMap_continuous hq)
  continuous2 := by
    simpa [TimeDependentSpatialReanchoring.shift,
      TimeDependentSpatialReanchoring.pairMap, Function.uncurry] using
      S.continuous2.comp (pairMap_continuous hq)

/-- The tangential field after translating by `q` and subtracting the value at
the moving base point.  It vanishes at the new spatial origin. -/
def tangentialReanchor (xi : ℝ → ℝ → ℝ) (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ TimeDependentSpatialReanchoring.shift xi q t x - xi t (q t)

@[simp] theorem tangentialReanchor_zero (xi : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (t : ℝ) : tangentialReanchor xi q t 0 = 0 := by
  simp [tangentialReanchor, TimeDependentSpatialReanchoring.shift]

/-- A continuous time-dependent tangential reanchoring preserves a spatial
`C²` certificate.  Its spatial derivatives are simply the shifted derivatives
of the original field; the subtracted base value is spatially constant. -/
def tangentialReanchorSpatialC2 {xi : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (S : SpatialC2 xi) (hq : Continuous q) :
    SpatialC2 (tangentialReanchor xi q) := by
  let T := S.shift hq
  let basePair : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, q p.1)
  have hbasePair : Continuous basePair :=
    continuous_fst.prodMk (hq.comp continuous_fst)
  refine
    { xi1 := T.xi1
      xi2 := T.xi2
      deriv1 := ?_
      deriv2 := T.deriv2
      continuous0 := ?_
      continuous1 := T.continuous1
      continuous2 := T.continuous2 }
  · intro t x
    simpa only [tangentialReanchor, sub_zero] using
      (T.deriv1 t x).sub (hasDerivAt_const x (xi t (q t)))
  · have hbase : Continuous (fun p : ℝ × ℝ ↦ xi p.1 (q p.1)) := by
      simpa [basePair, Function.uncurry] using S.continuous0.comp hbasePair
    simpa [tangentialReanchor, Function.uncurry] using T.continuous0.sub hbase

end SpatialC2

end RearOwnFrameDrift
