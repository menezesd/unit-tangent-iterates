import Mathlib
import UnitTangentIterates.TurningNumber
import UnitTangentIterates.SelectedInverseEmbedded
import UnitTangentIterates.SelectedInverseTubeCircle

/-!
# The turning-number hypothesis of the selected inverse, discharged by comparison

`SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember` and
`SelectedInverseEmbedded.selInv_spec_of_turning` reduce the embeddedness of the
rear tracks of a member of the tube to a single global normalization: that the
tangent angle of the front increases by `2π` over one period.  That
normalization is the Umlaufsatz, which is not available here.

This file removes it for the members of the tube that the paper actually
handles: those whose curvature is close to a **model curvature of known total
turning `2π`**.  By `TurningNumber.turning_eq_two_pi_of_integral` the turning of
a closed curve is quantized in `2π`, so a comparison with an error smaller than
`2π` pins it down exactly.  Since two tangent-angle presentations of the same
curve have the same curvature
(`SelectedInverseTube.curvature_unique`), the comparison need only be supplied
for **one** presentation.

* `turning_of_tubeMember_of_model` — the turning number of a member of the tube
  from an `L¹` comparison with a model curvature;
* `injOn_rearTrack_of_tubeMember_of_model` — the rear tracks of such a member
  are embedded;
* `selInv_spec_of_model` — the geometry of its selected inverse;
* `turning_of_tubeMember_of_sup_close` — the same comparison in uniform form,
  `ε·L < 2π`.
-/

noncomputable section

open Real Set Function MarkedSpace

namespace TurningNumberTube

/-- **The turning number of a member of the tube, from an `L¹` comparison with a
model.**  If some tangent-angle presentation of `ev p` has a curvature within
`2π` in `L¹` over one period of a model curvature `K₀` of total turning `2π`,
then *every* tangent-angle presentation of `ev p` increases by exactly `2π` over
one period — which is the hypothesis `hturn` of
`SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember`. -/
theorem turning_of_tubeMember_of_model {c kmin dlt : ℝ} {p : Data} {K₀ : ℝ → ℝ}
    (hc : 0 < c) (hp : IsTubeMember c kmin dlt p)
    (hK0int : IntervalIntegrable K₀ MeasureTheory.volume 0 (perim p))
    (hmodel : (∫ r in (0:ℝ)..perim p, K₀ r) = 2 * π)
    (hclose : ∃ Θ₁ K₁ : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ₁ (K₁ s) s) ∧
      IntervalIntegrable K₁ MeasureTheory.volume 0 (perim p) ∧
      (∫ r in (0:ℝ)..perim p, |K₁ r - K₀ r|) < 2 * π) :
    ∀ Θ K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      ∀ s, Θ (s + perim p) = Θ s + 2 * π := by
  obtain ⟨Θ₁, K₁, hX₁, hΘ₁, hK₁int, hL1⟩ := hclose
  intro Θ K hX hΘ
  have hKeq : ∀ s, K s = K₁ s :=
    fun s => SelectedInverseTube.curvature_unique hX hX₁ hΘ hΘ₁ s
  have hKfun : K = K₁ := funext hKeq
  subst hKfun
  exact TurningNumber.turning_eq_two_pi_of_L1_close (perim_pos hc hp).le hX hΘ
    (periodic_ev hc hp) hK₁int hK0int hmodel hL1

/-- **The same comparison in uniform form.**  A member of the tube whose
curvature is within `ε` of a model curvature of total turning `2π`, with
`ε·L < 2π`, has turning number one. -/
theorem turning_of_tubeMember_of_sup_close {c kmin dlt eps : ℝ} {p : Data} {K₀ : ℝ → ℝ}
    (hc : 0 < c) (hp : IsTubeMember c kmin dlt p)
    (hK0c : Continuous K₀)
    (hmodel : (∫ r in (0:ℝ)..perim p, K₀ r) = 2 * π)
    (heps : eps * perim p < 2 * π)
    (hclose : ∃ Θ₁ K₁ : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ₁ (K₁ s) s) ∧ Continuous K₁ ∧
      ∀ s, |K₁ s - K₀ s| ≤ eps) :
    ∀ Θ K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      ∀ s, Θ (s + perim p) = Θ s + 2 * π := by
  obtain ⟨Θ₁, K₁, hX₁, hΘ₁, hK₁c, hsup⟩ := hclose
  intro Θ K hX hΘ
  have hKfun : K = K₁ :=
    funext fun s => SelectedInverseTube.curvature_unique hX hX₁ hΘ hΘ₁ s
  subst hKfun
  exact TurningNumber.turning_eq_two_pi_of_sup_close (perim_pos hc hp).le hX hΘ
    (periodic_ev hc hp) hK₁c hK0c hmodel hsup heps

/-- **The rear tracks of a member of the tube close to a model are embedded.**
`SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember` with its topological
hypothesis replaced by the `L¹` comparison with a model of turning `2π`. -/
theorem injOn_rearTrack_of_tubeMember_of_model {c kmin dlt kap : ℝ} {p : Data} {K₀ : ℝ → ℝ}
    (hc : 0 < c) (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hK0int : IntervalIntegrable K₀ MeasureTheory.volume 0 (perim p))
    (hmodel : (∫ r in (0:ℝ)..perim p, K₀ r) = 2 * π)
    (hclose : ∃ Θ₁ K₁ : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ₁ (K₁ s) s) ∧
      IntervalIntegrable K₁ MeasureTheory.volume 0 (perim p) ∧
      (∫ r in (0:ℝ)..perim p, |K₁ r - K₀ r|) < 2 * π) :
    ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (ev p) Θ dl) (Ico 0 (perim p)) :=
  SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember hc hkminpos hkap1 hp hub
    (turning_of_tubeMember_of_model hc hp hK0int hmodel hclose)

/-- **The geometry of the selected inverse of a member of the tube close to a
model.**  `SelectedInverseEmbedded.selInv_spec_of_turning` with its topological
hypothesis replaced by the `L¹` comparison with a model of turning `2π`. -/
theorem selInv_spec_of_model {c kmin dlt kap : ℝ} {p : Data} {K₀ : ℝ → ℝ}
    (hc : 0 < c) (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hK0int : IntervalIntegrable K₀ MeasureTheory.volume 0 (perim p))
    (hmodel : (∫ r in (0:ℝ)..perim p, K₀ r) = 2 * π)
    (hclose : ∃ Θ₁ K₁ : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ₁ (K₁ s) s) ∧
      IntervalIntegrable K₁ MeasureTheory.volume 0 (perim p) ∧
      (∫ r in (0:ℝ)..perim p, |K₁ r - K₀ r|) < 2 * π) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (SelectedInverseMap.selInv kap p))
        (kmin / Real.sqrt (1 - kmin ^ 2)) dR (SelectedInverseMap.selInv kap p) ∧
      MainTheoremConditional.IsOval (ev (SelectedInverseMap.selInv kap p)) ∧
      (∀ u, ((starRingEnd ℂ) ((SelectedInverseMap.selInv kap p).2.1 u)
            * (SelectedInverseMap.selInv kap p).2.2 u).im
        ≤ kap / Real.sqrt (1 - kap ^ 2) * ‖(SelectedInverseMap.selInv kap p).2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev (SelectedInverseMap.selInv kap p))) = range (ev p) :=
  SelectedInverseEmbedded.selInv_spec_of_turning hc hkminpos hkap1 hp hub
    (turning_of_tubeMember_of_model hc hp hK0int hmodel hclose)

/-! ### The short case: no model needed -/

/-- **The turning number of a short member of the tube.**  A member of the tube
has curvature pinched by `0 < kmin ≤ K ≤ κ̂`; if moreover `κ̂·L < 4π` then its
total curvature lies in `(0, 4π)`, so its turning number is one and no
comparison with a model is needed. -/
theorem turning_of_tubeMember_of_short {c kmin dlt kap : ℝ} {p : Data}
    (hc : 0 < c) (hkminpos : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hshort : kap * perim p < 4 * π) :
    ∀ Θ K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      ∀ s, Θ (s + perim p) = Θ s + 2 * π := by
  obtain ⟨Θ₁, K₁, hK₁c, -, hX₁, hΘ₁, hlow, hhigh⟩ :=
    SelectedInverseTube.exists_front_data hc hp hub
  intro Θ K hX hΘ
  have hKfun : K = K₁ :=
    funext fun s => SelectedInverseTube.curvature_unique hX hX₁ hΘ hΘ₁ s
  subst hKfun
  exact TurningNumber.turning_eq_two_pi_of_pinched (perim_pos hc hp) hX hΘ
    (periodic_ev hc hp) hK₁c hkminpos hlow hhigh hshort

/-- **The rear tracks of a short member of the tube are embedded.**
`SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember` with its topological
hypothesis discharged by the length threshold `κ̂·L < 4π`. -/
theorem injOn_rearTrack_of_tubeMember_of_short {c kmin dlt kap : ℝ} {p : Data}
    (hc : 0 < c) (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hshort : kap * perim p < 4 * π) :
    ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (ev p) Θ dl) (Ico 0 (perim p)) :=
  SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember hc hkminpos hkap1 hp hub
    (turning_of_tubeMember_of_short hc hkminpos hp hub hshort)

/-! ### The comparison hypothesis is satisfiable -/

open SelectedInverseCircle SelectedInverseTubeCircle in
/-- **The hypotheses of `selInv_spec_of_model` are not vacuous.**  For the
marked circle of radius `r > 1` the model curvature `K₀ ≡ 1/r` has total
turning `2π` over the period `2πr` and the comparison error is `0`, so the
selected inverse of the circle has the asserted geometry with no topological
hypothesis assumed. -/
theorem selInv_spec_circle {r : ℝ} (hr : 1 < r) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
        ((1 / r) / Real.sqrt (1 - (1 / r) ^ 2)) dR
        (SelectedInverseMap.selInv (1 / r) (circleData r)) ∧
      MainTheoremConditional.IsOval (ev (SelectedInverseMap.selInv (1 / r) (circleData r))) ∧
      (∀ u, ((starRingEnd ℂ) ((SelectedInverseMap.selInv (1 / r) (circleData r)).2.1 u)
            * (SelectedInverseMap.selInv (1 / r) (circleData r)).2.2 u).im
        ≤ (1 / r) / Real.sqrt (1 - (1 / r) ^ 2)
            * ‖(SelectedInverseMap.selInv (1 / r) (circleData r)).2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev (SelectedInverseMap.selInv (1 / r) (circleData r))))
        = range (ev (circleData r)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hkmin : 0 < 1 / r := by positivity
  have hkap1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hperim : perim (circleData r) = 2 * Real.pi * r := perim_circleData hr0
  have hev : ev (circleData r) = circleFront r := ev_circleData hr0
  have hmodel : (∫ _ in (0:ℝ)..perim (circleData r), (1 / r : ℝ)) = 2 * π := by
    rw [hperim, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    field_simp
  refine selInv_spec_of_model (c := 2 * Real.pi * r) (by positivity) hkmin hkap1
    (circleData_mem_tube hr0) (circleData_curvature_le hr0)
    (intervalIntegrable_const (μ := MeasureTheory.volume) (c := 1 / r)) hmodel
    ⟨circleAngle r, fun _ => 1 / r, ?_, fun s => hasDerivAt_circleAngle s,
      intervalIntegrable_const (μ := MeasureTheory.volume) (c := 1 / r), ?_⟩
  · rw [hev]
    exact fun s => hasDerivAt_circleFront hr0 s
  · simpa using Real.pi_pos

end TurningNumberTube
