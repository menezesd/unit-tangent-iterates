import UnitTangentIterates.RearTrackEmbedded
import UnitTangentIterates.TubeHarnackStrictness

/-!
# Embeddedness of the rear track without a curvature floor
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology MarkedSpace RearTrack ArclengthInverse
open CurvatureFromMarkedDistance

namespace RearTrackEmbedded

/-- Any tangent-angle lift of a tube member has curvature `arcCurv p`. -/
theorem curvature_eq_arcCurv {c kmin dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin dlt p) {Theta K : ℝ → ℝ}
    (hX : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Theta (K s) s) (s : ℝ) :
    K s = UnconditionalAssembly.arcCurv p s := by
  obtain ⟨theta₀, hX₀, hΘ₀⟩ := exists_arclength_angle hc hp
  exact SelectedInverseTube.curvature_unique hX hX₀ hΘ hΘ₀ s

/-- **The embeddedness hypothesis of the selected inverse, discharged for a
member of a tube with no curvature floor.**  `injOn_rearTrack_of_tube` needed
`0 < kmin` in order to make the periodic selected steering strictly positive.
The floor is not needed: nonnegative curvature that is somewhere nonzero already
does it, by `injOn_rearTrack_of_curvature_nonnegative`, and
`UnconditionalAssembly.arcCurv_nonzero` supplies the nonvanishing for free —
a closed curve cannot have identically zero curvature. -/
theorem injOn_rearTrack_of_tube_floor_free {c dlt kap : ℝ} (hc : 0 < c)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c 0 dlt p)
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
  have hKeq : ∀ s, K s = UnconditionalAssembly.arcCurv p s :=
    curvature_eq_arcCurv hc hp hX hΘ
  have hK : ∀ s, 0 ≤ K s := by
    intro s; rw [hKeq s]; exact UnconditionalAssembly.arcCurv_nonneg hc hp s
  have hKne : ∃ s, K s ≠ 0 := by
    obtain ⟨s, hs⟩ := UnconditionalAssembly.arcCurv_nonzero hc hp
    exact ⟨s, by rw [hKeq s]; exact hs⟩
  have hturnΘ := turning_of_lift hX hX' hΘ hΘ' hturn'
  have hres := injOn_rearTrack_of_curvature_nonnegative (F := ev p) (Theta := Theta)
    (K := K) (delta := dl) hPpos hkap0 hkap1 hX hΘ hK hKne hturnΘ
    (periodic_ev hc hp) hdlper hdlmem hdlode 0
  simpa using hres

end RearTrackEmbedded
