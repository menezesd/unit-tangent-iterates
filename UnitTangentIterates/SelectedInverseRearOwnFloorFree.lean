import UnitTangentIterates.SelectedInverseRearOwn
import UnitTangentIterates.RearTrackEmbeddedFloorFree

/-!
# The rear track is an oval without a curvature floor
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MarkedSpace RearTrack ArclengthInverse RearOwnArclength

namespace SelectedInverseRearOwn

variable {Θ K dl sf : ℝ → ℝ} {F : ℝ → ℂ} {P kap : ℝ}

/-- **The rear track in its own arclength is an oval, with no curvature floor
on the front.**  `isOval_rearOwn` used `0 < kmin` in exactly one place: the
final strict positivity of the rear curvature `tan (δ (sf x))`, which it read
off the pinching `kmin/√(1-kmin²) ≤ tan δ`.  Strict positivity does not need a
floor.  The selected steering angle of a nonnegative, somewhere-nonzero
periodic front curvature is strictly positive everywhere
(`LowCurvatureAssembly.steering_pos_of_nonnegative_nonzero`), and `δ` stays
below `π/2` because `κ̂ < 1`, so `tan δ > 0` outright. -/
theorem isOval_rearOwn_floor_free (hP : 0 < P) (hkap1 : kap < 1)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hFper : Function.Periodic F P)
    (hKlow : ∀ s, 0 ≤ K s) (hKne : ∃ s, K s ≠ 0) (hKhigh : ∀ s, K s ≤ kap)
    (hdc : Continuous dl) (hdper : Function.Periodic dl P)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap))
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s)
    (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hinj : InjOn (rearTrack F Θ dl) (Ico 0 P)) :
    MainTheoremConditional.IsOval (fun x => rearTrack F Θ dl (sf x)) := by
  have hkap0 : 0 ≤ kap := le_trans (hKlow 0) (hKhigh 0)
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (dl s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  -- the selected steering angle is strictly positive
  have hdpos : ∀ s, 0 < dl s :=
    LowCurvatureAssembly.steering_pos_of_nonnegative_nonzero hP hdper hode
      (fun s => (hdmem s).1) hKlow hKne
  have hdlt : ∀ s, dl s < Real.pi / 2 := by
    intro s
    refine lt_of_le_of_lt (hdmem s).2 ?_
    exact Real.arcsin_lt_pi_div_two.mpr hkap1
  refine ⟨rearArclength dl P, rearPeriod_pos hP hcpos hdc hcos,
    periodic_rearOwn hcpos hdc hcos hdper hsfinv hF hFper,
    injOn_rearOwn hcpos hdc hcos hsfinv hinj,
    fun x => rearAngle Θ dl (sf x),
    fun x => hasDerivAt_rearOwnCurve hcpos hdc hcos hsfinv hF hΘ hode x,
    fun x => Real.tan (dl (sf x)),
    fun x => hasDerivAt_rearOwnAngleSf hcpos hdc hcos hsfinv hΘ hode x, fun x => ?_⟩
  exact Real.tan_pos_of_pos_of_lt_pi_div_two (hdpos (sf x)) (hdlt (sf x))

end SelectedInverseRearOwn
