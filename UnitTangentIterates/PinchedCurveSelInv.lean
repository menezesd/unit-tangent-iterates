import Mathlib
import UnitTangentIterates.SelInvPerimBound
import UnitTangentIterates.SelInvPathTubeC2
import UnitTangentIterates.TurningNumberTube

/-!
# The selected inverse of an admissible curve exists

An **admissible curve** (`PinchedPathBasic.IsPinchedCurve kminP κ̂ a`) is a
closed `C⁶` curve of constant positive speed whose curvature in the normalized
parameter is pinched between `kminP` and `κ̂` and which is short, `κ̂·L < 4π`.
This file shows that such a curve satisfies *every* hypothesis of the
construction of the selected inverse, so that

`IsMarkedSelectedInverse κ̂ a (selInv κ̂ a)`

holds with nothing assumed beyond admissibility (and the frame condition, that
the velocity and the acceleration components of the marked datum are the
derivatives of its curve).

* `turning_of_isPinchedCurve` — the turning number of an admissible curve is one
  (the constant path at it is admissible, and a short pinched slice turns by
  `2π`);
* `isTubeMember_of_isPinchedCurve` — an admissible curve is a member of the
  tube, of speed at least its perimeter, of curvature at least `kminP` and with
  the chord-arc constant produced by `ConvexChordArcSpeed`;
* `curv_le_of_isPinchedCurve` — its curvature is at most `κ̂` in the form the
  construction asks for;
* `isMarkedSelectedInverse_selInv_of_isPinchedCurve` — hence the marked selected
  inverse of an admissible curve exists and is `selInv κ̂ a`, the embeddedness of
  the rear tracks being supplied by
  `TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short`;
* `selInv_spec_of_isPinchedCurve` — and the image is a member of the tube of
  curvature at least `kminP/√(1−kminP²)`, an oval whose unit-tangent transform
  retraces the curve.

Main results: `isTubeMember_of_isPinchedCurve`,
`isMarkedSelectedInverse_selInv_of_isPinchedCurve`,
`selInv_spec_of_isPinchedCurve`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open SelInvTubePathDist SelectedInverseMap RearOwnHigherRegularity FrontFromPath
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvPathCurvBoundC2
  SelInvPathTurningC2 SelInvPathTubeC2 ConvexChordArcSpeed TurningNumberTube

variable {kminP kh : ℝ} {a : Data}

/-! ### The frame data of the constant path at an admissible curve -/

/-- **The turning number of an admissible curve is one.** -/
theorem turning_of_isPinchedCurve (hkminP : 0 < kminP) (hc : IsPinchedCurve kminP kh a) :
    (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (pathVel (constFam a) 0 u)
        * pathAcc (constFam a) 0 u).im / pathPerim (constFam a) 0 ^ 2) = 2 * Real.pi := by
  have hΓ := isPinchedPath_constPinchedPath (kminP := kminP) (kh := kh) a hc
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry (constFam a)) := hΓ.smooth.of_le (by norm_num)
  have hXdiff : Differentiable ℝ (uncurry (constFam a)) := hΓ.smooth.differentiable (by norm_num)
  have hVC : ContDiff ℝ ((1 : ℕ)) (uncurry (pathVel (constFam a))) :=
    contDiff_partialArc_self (n := 1) hX2
  have hVdiff : Differentiable ℝ (uncurry (pathVel (constFam a))) :=
    hVC.differentiable (by norm_num)
  have hslicec : ∀ t : ℝ, Continuous fun u : ℝ => ((t, u) : ℝ × ℝ) :=
    fun t => continuous_const.prodMk continuous_id
  have hPpos : 0 < pathPerim (constFam a) 0 :=
    norm_pos_iff.2 (Complex.slitPlane_ne_zero (hΓ.slit 0))
  have hPne : ∀ t, pathPerim (constFam a) t ≠ 0 := by
    intro t
    have hp1 : ContDiff ℝ (1 : ℕ) (⇑a.1) := hc.smooth.of_le (by norm_num)
    rw [pathPerim_constFam hp1 t]
    exact hc.speed_pos.ne'
  have hVper : ∀ t, Periodic (pathVel (constFam a) t) 1 := periodic_partialArc hXdiff hΓ.per
  have hAper : ∀ t, Periodic (pathAcc (constFam a) t) 1 := periodic_partialArc hVdiff hVper
  have hVcont : Continuous (pathVel (constFam a) 0) := hVC.continuous.comp (hslicec 0)
  have hAcont : Continuous (pathAcc (constFam a) 0) :=
    (contDiff_partialArc_self (n := 0) hVC).continuous.comp (hslicec 0)
  have hAderiv : ∀ u, HasDerivAt (pathVel (constFam a) 0) (pathAcc (constFam a) 0 u) u :=
    fun u => hasDerivAt_partialArc hVdiff 0 u
  have hlowc : ∀ s, kminP ≤ curvOfPath (pathVel (constFam a)) (pathAcc (constFam a))
      (pathPerim (constFam a)) 0 s :=
    fun s => by rw [curvOfPath_eq_pathKn hPne 0 s]; exact hΓ.kmin 0 _
  have hhighc : ∀ s, curvOfPath (pathVel (constFam a)) (pathAcc (constFam a))
      (pathPerim (constFam a)) 0 s ≤ kh :=
    fun s => by rw [curvOfPath_eq_pathKn hPne 0 s]; exact hΓ.kmax 0 _
  exact turning_of_slice hAderiv (hVper 0) (hAper 0) hVcont hAcont (fun u => hΓ.speed 0 u)
    hPpos hkminP hlowc hhighc (hΓ.short 0)

/-! ### An admissible curve is a member of the tube -/

/-- **An admissible curve is a member of the tube**, of speed at least its
perimeter, of curvature at least `kminP` and with the chord-arc constant
produced by `ConvexChordArcSpeed`. -/
theorem isTubeMember_of_isPinchedCurve (hkminP : 0 < kminP) (hc : IsPinchedCurve kminP kh a)
    (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u)
    (hframe2 : ∀ u, HasDerivAt (⇑a.2.1) (a.2.2 u) u) :
    IsTubeMember (perim a) kminP
      (chordConstSpeed (perim a) (perim a * kminP) (perim a * kh) 1) a := by
  have hΓ := isPinchedPath_constPinchedPath (kminP := kminP) (kh := kh) a hc
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry (constFam a)) := hΓ.smooth.of_le (by norm_num)
  have hPpos : 0 < pathPerim (constFam a) 0 :=
    norm_pos_iff.2 (Complex.slitPlane_ne_zero (hΓ.slit 0))
  exact isTubeMember_of_slice hX2 hΓ.per (fun u => hΓ.speed 0 u) hPpos hkminP
    (hΓ.kmin 0) (hΓ.kmax 0) (turning_of_isPinchedCurve hkminP hc) (fun _ => rfl)
    hframe hframe2

/-- **The curvature of an admissible curve is at most `κ̂`,** in the form the
construction of the selected inverse asks for. -/
theorem curv_le_of_isPinchedCurve (hc : IsPinchedCurve kminP kh a)
    (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u)
    (hframe2 : ∀ u, HasDerivAt (⇑a.2.1) (a.2.2 u) u) (u : ℝ) :
    ((starRingEnd ℂ) (a.2.1 u) * a.2.2 u).im ≤ kh * ‖a.2.1 u‖ ^ 3 := by
  have hΓ := isPinchedPath_constPinchedPath (kminP := kminP) (kh := kh) a hc
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry (constFam a)) := hΓ.smooth.of_le (by norm_num)
  have hPne : pathPerim (constFam a) 0 ≠ 0 :=
    (norm_pos_iff.2 (Complex.slitPlane_ne_zero (hΓ.slit 0))).ne'
  exact curv_le_of_slice hX2 hPne rfl (fun u => hΓ.speed 0 u) (hΓ.kmax 0) (fun _ => rfl)
    hframe hframe2 u

/-! ### The selected inverse of an admissible curve -/

/-- **The marked selected inverse of an admissible curve exists.**  All the
hypotheses of `SelectedInverseMap.isMarkedSelectedInverse_selInv` are met: the
curve is a member of the tube, its curvature is at most `κ̂`, and its rear
tracks are embedded because it is short and its curvature is pinched away from
zero. -/
theorem isMarkedSelectedInverse_selInv_of_isPinchedCurve (hkminP : 0 < kminP) (hkh1 : kh < 1)
    (hc : IsPinchedCurve kminP kh a) (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u)
    (hframe2 : ∀ u, HasDerivAt (⇑a.2.1) (a.2.2 u) u) :
    IsMarkedSelectedInverse kh a (selInv kh a) := by
  have hperim : perim a = ‖deriv (⇑a.1) 0‖ := by rw [perim, (hframe 0).deriv]
  have hppos : 0 < perim a := by rw [hperim]; exact hc.speed_pos
  have hp := isTubeMember_of_isPinchedCurve hkminP hc hframe hframe2
  have hub := curv_le_of_isPinchedCurve hc hframe hframe2
  have hshort : kh * perim a < 4 * Real.pi := by rw [hperim]; exact hc.short
  exact isMarkedSelectedInverse_selInv hppos hkminP hkh1 hp hub
    (injOn_rearTrack_of_tubeMember_of_short hppos hkminP hkh1 hp hub hshort)

/-- **The geometry of the selected inverse of an admissible curve.**  The image
is a member of the tube of curvature at least `kminP/√(1−kminP²)`, an oval whose
unit-tangent transform retraces the curve. -/
theorem selInv_spec_of_isPinchedCurve (hkminP : 0 < kminP) (hkh1 : kh < 1)
    (hc : IsPinchedCurve kminP kh a) (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u)
    (hframe2 : ∀ u, HasDerivAt (⇑a.2.1) (a.2.2 u) u) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (selInv kh a)) (kminP / Real.sqrt (1 - kminP ^ 2)) dR
        (selInv kh a) ∧
      MainTheoremConditional.IsOval (ev (selInv kh a)) ∧
      (∀ u, ((starRingEnd ℂ) ((selInv kh a).2.1 u) * (selInv kh a).2.2 u).im
        ≤ kh / Real.sqrt (1 - kh ^ 2) * ‖(selInv kh a).2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev (selInv kh a))) = range (ev a) := by
  have hperim : perim a = ‖deriv (⇑a.1) 0‖ := by rw [perim, (hframe 0).deriv]
  have hppos : 0 < perim a := by rw [hperim]; exact hc.speed_pos
  have hp := isTubeMember_of_isPinchedCurve hkminP hc hframe hframe2
  have hub := curv_le_of_isPinchedCurve hc hframe hframe2
  have hshort : kh * perim a < 4 * Real.pi := by rw [hperim]; exact hc.short
  exact selInv_spec hppos hkminP hkh1 hp hub
    (injOn_rearTrack_of_tubeMember_of_short hppos hkminP hkh1 hp hub hshort)

/-! ### Iterating the selected inverse -/

/-- **The selected inverse can be iterated.**  The image of an admissible curve
is a member of the tube of curvature pinched between `kminP/√(1−kminP²)` and
`κ̂/√(1−κ̂²)`, and its perimeter is at most `2π/kminP`; so as soon as the new
curvature bound is again admissible and the new length threshold holds, the
marked selected inverse of the image exists in its turn. -/
theorem isMarkedSelectedInverse_selInv_selInv (hkminP : 0 < kminP) (hkh1 : kh < 1)
    (hc : IsPinchedCurve kminP kh a) (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u)
    (hframe2 : ∀ u, HasDerivAt (⇑a.2.1) (a.2.2 u) u)
    (hkap1 : kh / Real.sqrt (1 - kh ^ 2) < 1)
    (hshort : kh / Real.sqrt (1 - kh ^ 2) * (2 * Real.pi / kminP) < 4 * Real.pi) :
    IsMarkedSelectedInverse (kh / Real.sqrt (1 - kh ^ 2)) (selInv kh a)
      (selInv (kh / Real.sqrt (1 - kh ^ 2)) (selInv kh a)) := by
  have hkh0 : 0 < kh := lt_of_lt_of_le hkminP (le_trans (hc.kmin 0 0) (hc.kmax 0 0))
  have hkminP1 : kminP < 1 := lt_of_le_of_lt (le_trans (hc.kmin 0 0) (hc.kmax 0 0)) hkh1
  have hsq : (0 : ℝ) < 1 - kh ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 hsq
  have hsq' : (0 : ℝ) < 1 - kminP ^ 2 := by nlinarith
  have hkmin' : 0 < kminP / Real.sqrt (1 - kminP ^ 2) := by
    have : 0 < Real.sqrt (1 - kminP ^ 2) := Real.sqrt_pos.2 hsq'
    positivity
  -- the image is a nondegenerate curve
  have hlow := le_perim_selInv_of_isPinchedCurve hkminP hc hframe
  have hppos : 0 < perim (selInv kh a) :=
    lt_of_lt_of_le (by positivity) hlow
  have hup := perim_selInv_le_of_isPinchedCurve hkminP hc hframe
  obtain ⟨dR, -, hp', -, hub', -⟩ :=
    selInv_spec_of_isPinchedCurve hkminP hkh1 hc hframe hframe2
  have hshort' : kh / Real.sqrt (1 - kh ^ 2) * perim (selInv kh a) < 4 * Real.pi :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hup (by positivity)) hshort
  exact isMarkedSelectedInverse_selInv hppos hkmin' hkap1 hp' hub'
    (injOn_rearTrack_of_tubeMember_of_short hppos hkmin' hkap1 hp' hub' hshort')

end PinchedPath
