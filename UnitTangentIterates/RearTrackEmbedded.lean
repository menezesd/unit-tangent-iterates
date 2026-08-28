import Mathlib
import UnitTangentIterates.ConvexEmbedded
import UnitTangentIterates.RearTrack
import UnitTangentIterates.LowCurvatureAssembly
import UnitTangentIterates.SelectedInverseTube

/-!
# The rear track of a tube member is embedded

Every path-distance bound for the selected inverse carries, at both of its
ends, the hypothesis `hinjR`: *for every steering solution on the selected
strip, the reconstructed rear track is injective on one period*.  It is the
embeddedness of the rear curve, and it has been assumed throughout.

It need not be.  On the selected strip the rear track is regular, with speed
`cos δ > 0` and tangent angle `Ψ = Θ - δ` turning at rate `sin δ`; if the front
curvature is *strictly* positive then the steering angle never vanishes
(`LowCurvatureAssembly.steering_ge_arcsin_of_curvature_ge`), so `Ψ` increases
strictly, and over one period of the front it increases by exactly `2π`, since
`Θ` does and `δ` is periodic.  A closed regular curve of strictly increasing
tangent angle and turning number one is embedded
(`ConvexEmbedded.injOn_Ico_of_turning_one`).

What remains an input is the turning number of the *front*, a global
topological fact which, following the convention of this project, is carried as
an explicit hypothesis; it is enough to assume it for one tangent-angle lift,
since two lifts differ by a constant.

Main results:

* `sub_const_of_lift`, `turning_of_lift` — two tangent-angle lifts of one curve
  differ by a constant, so the turning number does not depend on the lift;
* `injOn_rearTrack_of_curvature_pos` — the rear track of a front of strictly
  positive curvature and turning number one is embedded;
* `injOn_rearTrack_of_tube` — the hypothesis `hinjR` of the path-distance
  bounds, discharged for a member of the tube whose front tangent angle turns
  by `2π`.
-/

noncomputable section

open Set Function MarkedSpace RearTrack

namespace RearTrackEmbedded

variable {F : ℝ → ℂ} {Theta K delta : ℝ → ℝ}

/-! ### The tangent-angle lift is determined up to a constant -/

/-- **Two tangent-angle lifts of one curve differ by a constant.**  Their
derivatives agree by `SelectedInverseTube.curvature_unique`. -/
theorem sub_const_of_lift {Y : ℝ → ℂ} {th1 th2 k1 k2 : ℝ → ℝ}
    (hY1 : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th1 s : ℂ))) s)
    (hY2 : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th2 s : ℂ))) s)
    (hth1 : ∀ s, HasDerivAt th1 (k1 s) s) (hth2 : ∀ s, HasDerivAt th2 (k2 s) s) :
    ∀ s t : ℝ, th1 s - th2 s = th1 t - th2 t := by
  have hk := SelectedInverseTube.curvature_unique hY1 hY2 hth1 hth2
  have hd : ∀ s, HasDerivAt (fun u => th1 u - th2 u) 0 s := by
    intro s
    have h := (hth1 s).sub (hth2 s)
    rwa [hk s, sub_self] at h
  have hdiff : Differentiable ℝ fun u => th1 u - th2 u := fun s => (hd s).differentiableAt
  exact fun s t => is_const_of_deriv_eq_zero hdiff (fun u => (hd u).deriv) s t

/-- **The turning number does not depend on the lift.** -/
theorem turning_of_lift {Y : ℝ → ℂ} {th1 th2 k1 k2 : ℝ → ℝ} {P : ℝ}
    (hY1 : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th1 s : ℂ))) s)
    (hY2 : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th2 s : ℂ))) s)
    (hth1 : ∀ s, HasDerivAt th1 (k1 s) s) (hth2 : ∀ s, HasDerivAt th2 (k2 s) s)
    (hturn : ∀ s, th2 (s + P) = th2 s + 2 * Real.pi) :
    ∀ s, th1 (s + P) = th1 s + 2 * Real.pi := by
  intro s
  have h := sub_const_of_lift hY1 hY2 hth1 hth2 (s + P) s
  rw [hturn s] at h
  linarith

/-! ### The rear track is embedded -/

/-- **The rear track of a front of strictly positive curvature and turning
number one is embedded.** -/
theorem injOn_rearTrack_of_curvature_pos {P kmin kap : ℝ} (hP : 0 < P)
    (hkmin : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Theta (K s) s)
    (hK : ∀ s, kmin ≤ K s)
    (hturn : ∀ s, Theta (s + P) = Theta s + 2 * Real.pi)
    (hFper : Periodic F P) (hδper : Periodic delta P)
    (hδmem : ∀ s, delta s ∈ Icc 0 (Real.arcsin kap))
    (hδode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) (a : ℝ) :
    InjOn (rearTrack F Theta delta) (Ico a (a + P)) := by
  have hpi := Real.pi_pos
  have harc : Real.arcsin kap < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hkap1
  -- the steering angle is bounded away from zero
  have hstrip : ∀ s, delta s ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    fun s => ⟨(hδmem s).1, le_trans (hδmem s).2 harc.le⟩
  have hge := LowCurvatureAssembly.steering_ge_arcsin_of_curvature_ge hP hδper hδode hstrip hK
  have harcpos : 0 < Real.arcsin kmin := Real.arcsin_pos.mpr hkmin
  have hsinpos : ∀ s, 0 < Real.sin (delta s) := by
    intro s
    refine Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le harcpos (hge s)) ?_
    exact lt_of_le_of_lt (le_trans (hδmem s).2 harc.le) (by linarith)
  -- the rear track is regular with tangent angle `Ψ`
  have hX : ∀ s, HasDerivAt (rearTrack F Theta delta)
      ((Real.cos (delta s) : ℂ)
        * Complex.exp (Complex.I * (rearAngle Theta delta s : ℂ))) s :=
    fun s => hasDerivAt_rearTrack (hF s) (hΘ s) (hδode s)
  have hv : ∀ s, 0 < Real.cos (delta s) :=
    fun s => rear_speed_ge hkap1 hkap0 (hδmem s).1 (hδmem s).2
  have hΨd : ∀ s, HasDerivAt (rearAngle Theta delta) (Real.sin (delta s)) s :=
    fun s => hasDerivAt_rearAngle (hΘ s) (hδode s)
  have hΨcont : Continuous (rearAngle Theta delta) :=
    continuous_iff_continuousAt.mpr fun s => (hΨd s).continuousAt
  have hΨmono : StrictMono (rearAngle Theta delta) := by
    refine strictMono_of_deriv_pos fun s => ?_
    rw [(hΨd s).deriv]
    exact hsinpos s
  have hΨturn : ∀ s, rearAngle Theta delta (s + P) = rearAngle Theta delta s + 2 * Real.pi := by
    intro s
    simp only [rearAngle, hturn s, hδper s]
    ring
  have hRper : Periodic (rearTrack F Theta delta) P := by
    intro s
    simp only [rearTrack, hFper s]
    rw [rearTangent_periodic hδper hturn s]
  exact ConvexEmbedded.injOn_Ico_of_turning_one hX hv hΨcont hΨmono hΨturn hRper a

/-- **Embeddedness with flat front-curvature pieces.**  Nonnegative,
nontrivial periodic front curvature makes the periodic selected steering
strictly positive, so the rear tangent angle is strictly increasing even
though the front tangent angle need only be nondecreasing. -/
theorem injOn_rearTrack_of_curvature_nonnegative {P kap : ℝ} (hP : 0 < P)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Theta (K s) s)
    (hK : ∀ s, 0 ≤ K s) (hKne : ∃ s, K s ≠ 0)
    (hturn : ∀ s, Theta (s + P) = Theta s + 2 * Real.pi)
    (hFper : Periodic F P) (hδper : Periodic delta P)
    (hδmem : ∀ s, delta s ∈ Icc 0 (Real.arcsin kap))
    (hδode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) (a : ℝ) :
    InjOn (rearTrack F Theta delta) (Ico a (a + P)) := by
  have hδpos : ∀ s, 0 < delta s :=
    LowCurvatureAssembly.steering_pos_of_nonnegative_nonzero hP hδper hδode
      (fun s => (hδmem s).1) hK hKne
  have hsinpos : ∀ s, 0 < Real.sin (delta s) := by
    intro s
    apply Real.sin_pos_of_pos_of_lt_pi (hδpos s)
    exact lt_of_le_of_lt (le_trans (hδmem s).2
      (Real.arcsin_le_pi_div_two kap)) (by linarith [Real.pi_pos])
  have hX : ∀ s, HasDerivAt (rearTrack F Theta delta)
      ((Real.cos (delta s) : ℂ) *
        Complex.exp (Complex.I * (rearAngle Theta delta s : ℂ))) s :=
    fun s => hasDerivAt_rearTrack (hF s) (hΘ s) (hδode s)
  have hv : ∀ s, 0 < Real.cos (delta s) :=
    fun s => rear_speed_ge hkap1 hkap0 (hδmem s).1 (hδmem s).2
  have hΨd : ∀ s, HasDerivAt (rearAngle Theta delta) (Real.sin (delta s)) s :=
    fun s => hasDerivAt_rearAngle (hΘ s) (hδode s)
  have hΨcont : Continuous (rearAngle Theta delta) :=
    continuous_iff_continuousAt.mpr fun s => (hΨd s).continuousAt
  have hΨmono : StrictMono (rearAngle Theta delta) := by
    refine strictMono_of_deriv_pos fun s => ?_
    rw [(hΨd s).deriv]
    exact hsinpos s
  have hΨturn : ∀ s, rearAngle Theta delta (s + P) =
      rearAngle Theta delta s + 2 * Real.pi := by
    intro s
    simp only [rearAngle, hturn s, hδper s]
    ring
  have hRper : Periodic (rearTrack F Theta delta) P := by
    intro s
    simp only [rearTrack, hFper s]
    rw [rearTangent_periodic hδper hturn s]
  exact ConvexEmbedded.injOn_Ico_of_turning_one hX hv hΨcont hΨmono hΨturn hRper a

/-- **The embeddedness hypothesis of the path-distance bounds, discharged for a
member of the tube.**  It is enough that the tangent angle of the front turn by
`2π` over one period for one of its lifts. -/
theorem injOn_rearTrack_of_tube {c kmin dlt kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Theta' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta' (K' s) s) ∧
      (∀ s, Theta' (s + perim p) = Theta' s + 2 * Real.pi)) :
    ∀ Theta K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Theta s : ℂ))) s) →
      (∀ s, HasDerivAt Theta (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Theta dl) (Ico 0 (perim p)) := by
  intro Theta K dl hX hΘ hdlper hdlmem hdlode
  have hPpos : 0 < perim p := perim_pos hc hp
  obtain ⟨Theta', K', hX', hΘ', hturn'⟩ := hturn
  -- the curvature of the front is at least the tube's lower bound
  obtain ⟨Theta₀, K₀, -, -, hX₀, hΘ₀, hK₀low, -⟩ :=
    SelectedInverseTube.exists_front_data (kap := kap) hc hp hub
  have hKK₀ := SelectedInverseTube.curvature_unique hX hX₀ hΘ hΘ₀
  have hK : ∀ s, kmin ≤ K s := fun s => by rw [hKK₀ s]; exact hK₀low s
  have hturnΘ := turning_of_lift hX hX' hΘ hΘ' hturn'
  have hres := injOn_rearTrack_of_curvature_pos (F := ev p) (Theta := Theta) (K := K)
    (delta := dl) hPpos hkmin hkap0 hkap1 hX hΘ hK hturnΘ (periodic_ev hc hp) hdlper
    hdlmem hdlode 0
  simpa using hres

end RearTrackEmbedded
