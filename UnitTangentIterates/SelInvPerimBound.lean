import Mathlib
import UnitTangentIterates.SelInvLipMonotone
import UnitTangentIterates.SelInvPathTubeBasePerimC2

/-!
# The perimeter of the selected inverse of an admissible curve is universally
bounded

`SelInvLipMonotone.dist_selInv_le_pinchedDist_of_perim_le` still asks for a
bound `E` on the perimeter of the selected inverse of an admissible curve.  This
file produces one, depending only on the curvature pinching:

* `perim_selInv_le` — the selected inverse never lengthens the curve: its
  perimeter is the rear arclength `∫₀^L cos δ` of one period, hence at most `L`
  (and where the marked selected inverse does not exist the map is the identity,
  so the bound is trivially true);
* `perim_le_of_isPinchedCurve` — an admissible curve is a closed curve of
  constant speed with turning number one and curvature at least `kminP`, so its
  perimeter is at most `2π/kminP` (this is `PerimeterFromTurning` applied to the
  constant path at the curve);
* `perim_selInv_le_of_isPinchedCurve` — the two combined.

Main results: `perim_selInv_le`, `perim_le_of_isPinchedCurve`,
`perim_selInv_le_of_isPinchedCurve`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open SelInvTubePathDist SelectedInverseMap RearTrack SelInvPathRegularityC2
  SelInvPathPerimC2 SelInvPathTubeBasePerimC2

variable {kminP kh : ℝ} {a : Data}

/-! ### The selected inverse does not lengthen the curve -/

/-- **The selected inverse of a marked curve is no longer than the curve.**  Its
perimeter is the rear arclength of one period, and the rear arclength of a
steering angle is at most the arclength. -/
theorem perim_selInv_le (kap : ℝ) (p : Data) : perim (selInv kap p) ≤ perim p := by
  by_cases hex : ∃ q, IsMarkedSelectedInverse kap p q
  · have hspec := hex.choose_spec
    obtain ⟨-, Θ, K, dl, sf, -, -, -, -, hode, -, hperim, -⟩ := hspec
    have hdc : Continuous dl :=
      continuous_iff_continuousAt.2 (fun s => (hode s).continuousAt)
    have hval : perim (selInv kap p) = rearArclength dl (perim p) := by
      rw [selInv, dif_pos hex]; exact hperim
    rw [hval]
    exact SelInvLipUniversal.rearArclength_le (norm_nonneg _) hdc
  · rw [selInv, dif_neg hex]

/-! ### The perimeter of an admissible curve -/

/-- **An admissible curve has perimeter at most `2π/kminP`.**  It is a closed
curve of constant speed whose curvature is pinched between `kminP` and `κ̂` and
which is short, so its turning number is one and its total curvature is `2π`. -/
theorem perim_le_of_isPinchedCurve (hkminP : 0 < kminP) (hc : IsPinchedCurve kminP kh a)
    (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) : perim a ≤ 2 * Real.pi / kminP := by
  have hp1 : ContDiff ℝ (1 : ℕ) (⇑a.1) := hc.smooth.of_le (by norm_num)
  have hΓ := isPinchedPath_constPinchedPath (kminP := kminP) (kh := kh) a hc
  have hbound : pathPerim (constFam a) 0 ≤ 2 * Real.pi / kminP :=
    (perim_pinch_of_path (constPinchedPath a hc) hΓ.smooth hΓ.speed hΓ.per
      hkminP hΓ.kmin hΓ.kmax hΓ.short hΓ.slit).2 0
  have hP : pathPerim (constFam a) 0 = ‖deriv (⇑a.1) 0‖ := pathPerim_constFam hp1 0
  have hpa : perim a = ‖deriv (⇑a.1) 0‖ := by
    rw [perim, (hframe 0).deriv]
  rw [hpa, ← hP]
  exact hbound

/-- **The selected inverse of an admissible curve has perimeter at most
`2π/kminP`.** -/
theorem perim_selInv_le_of_isPinchedCurve (hkminP : 0 < kminP)
    (hc : IsPinchedCurve kminP kh a) (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) :
    perim (selInv kh a) ≤ 2 * Real.pi / kminP :=
  le_trans (perim_selInv_le kh a) (perim_le_of_isPinchedCurve hkminP hc hframe)

/-! ### The selected inverse does not collapse the curve -/

/-- The rear arclength of a steering angle on the strip `[0, arcsin κ̂]` is at
least `√(1-κ̂²)` times the arclength. -/
theorem mul_le_rearArclength {dl : ℝ → ℝ} {kap L : ℝ} (hL : 0 ≤ L) (hdc : Continuous dl)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) :
    Real.sqrt (1 - kap ^ 2) * L ≤ rearArclength dl L := by
  have hint : IntervalIntegrable (fun u => Real.cos (dl u)) volume 0 L :=
    (Real.continuous_cos.comp hdc).intervalIntegrable 0 L
  have hle : (∫ _u in (0 : ℝ)..L, Real.sqrt (1 - kap ^ 2))
      ≤ ∫ u in (0 : ℝ)..L, Real.cos (dl u) :=
    intervalIntegral.integral_mono_on hL _root_.intervalIntegrable_const hint
      (fun u _ => Shadowing.cos_ge_of_mem_strip (hdmem u).1 (hdmem u).2)
  simpa [rearArclength, mul_comm] using hle

/-- **The selected inverse shrinks the curve by a factor at most `√(1-κ̂²)`.**
Its perimeter is the rear arclength of one period, and the steering angle lies
on the strip `[0, arcsin κ̂]`. -/
theorem mul_perim_le_perim_selInv (kap : ℝ) (p : Data) :
    Real.sqrt (1 - kap ^ 2) * perim p ≤ perim (selInv kap p) := by
  have hs1 : Real.sqrt (1 - kap ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  by_cases hex : ∃ q, IsMarkedSelectedInverse kap p q
  · obtain ⟨-, Θ, K, dl, sf, -, -, -, hdmem, hode, -, hperim, -⟩ := hex.choose_spec
    have hdc : Continuous dl :=
      continuous_iff_continuousAt.2 (fun s => (hode s).continuousAt)
    have hval : perim (selInv kap p) = rearArclength dl (perim p) := by
      rw [selInv, dif_pos hex]; exact hperim
    rw [hval]
    exact mul_le_rearArclength (norm_nonneg _) hdc hdmem
  · rw [selInv, dif_neg hex]
    calc Real.sqrt (1 - kap ^ 2) * perim p ≤ 1 * perim p :=
          mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ = perim p := one_mul _

/-- **An admissible curve has perimeter at least `2π/κ̂`.** -/
theorem le_perim_of_isPinchedCurve (hkminP : 0 < kminP) (hc : IsPinchedCurve kminP kh a)
    (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) : 2 * Real.pi / kh ≤ perim a := by
  have hp1 : ContDiff ℝ (1 : ℕ) (⇑a.1) := hc.smooth.of_le (by norm_num)
  have hΓ := isPinchedPath_constPinchedPath (kminP := kminP) (kh := kh) a hc
  have hbound : 2 * Real.pi / kh ≤ pathPerim (constFam a) 0 :=
    (perim_pinch_of_path (constPinchedPath a hc) hΓ.smooth hΓ.speed hΓ.per
      hkminP hΓ.kmin hΓ.kmax hΓ.short hΓ.slit).1 0
  have hP : pathPerim (constFam a) 0 = ‖deriv (⇑a.1) 0‖ := pathPerim_constFam hp1 0
  have hpa : perim a = ‖deriv (⇑a.1) 0‖ := by
    rw [perim, (hframe 0).deriv]
  rw [hpa, ← hP]
  exact hbound

/-- **The selected inverse of an admissible curve is a curve of perimeter at
least `2π√(1-κ̂²)/κ̂`**: it does not collapse. -/
theorem le_perim_selInv_of_isPinchedCurve (hkminP : 0 < kminP)
    (hc : IsPinchedCurve kminP kh a) (hframe : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) :
    Real.sqrt (1 - kh ^ 2) * (2 * Real.pi / kh) ≤ perim (selInv kh a) := by
  refine le_trans (mul_le_mul_of_nonneg_left
    (le_perim_of_isPinchedCurve hkminP hc hframe) (Real.sqrt_nonneg _)) ?_
  exact mul_perim_le_perim_selInv kh a

/-! ### The Lipschitz estimate with no free constants -/

variable {khat : ℝ} {p q : Data}

/-- **The selected inverse is Lipschitz for the pinched pseudometric, with a
constant depending only on the curvature pinching.**  The perimeter of the
selected inverse of an admissible curve is at most `2π/kminP`
(`perim_selInv_le_of_isPinchedCurve`), so the universal constant of the `C²`
estimate may be evaluated once and for all at that value. -/
theorem dist_selInv_le_pinchedDist_universal
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP)
    (hkhat : GaugeMarkedDataOfRearFamily.rearKappa1 kh ≤ khat) (hkhat0 : 0 ≤ khat)
    (hne : (pinchedSet kminP kh p q).Nonempty) :
    dist (selInv kh q) (selInv kh p)
      ≤ SelInvLipUniversal.selInvLipUniversal kminP kh khat (2 * Real.pi / kminP)
          (2 * Real.pi / kminP) * pinchedDist kminP kh p q :=
  dist_selInv_le_pinchedDist_of_perim_le hpd hpd2 hqd hqd2 hkh1 hkminP hkhat hkhat0
    (fun _ ha hfa => perim_selInv_le_of_isPinchedCurve hkminP ha hfa) hne

end PinchedPath
