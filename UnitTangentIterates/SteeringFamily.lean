import UnitTangentIterates.SteeringExistence
import UnitTangentIterates.SelectedInverseRearOwn
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.UniformCeilings

/-!
# The steering and rear-arclength families of a moving front
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real ArclengthInverse RearTrack

namespace SteeringFamily

/-- **The steering family.**  A moving front whose curvature slices `K t` are
continuous, `Pₜ`-periodic and pinched in `[0, κ̂]` carries a family of selected
steering angles `δ t`, one per time, each solving `δ' = K − sin δ`, periodic with
the same period, and confined to the closed strip `[0, arcsin κ̂]`.

This supplies six of the interlocking hypotheses of
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`
— `hstrip0`, `hstrip1`, `hsteer`, `hδper`, `hcos`, and the positivity `hQpos`
below.  It says nothing about regularity of `δ` in `t`, which is a separate
question (ODE dependence on parameters). -/
theorem exists_steering_family {K : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kap : ℝ}
    (hP : ∀ t, 0 < P t) (hK : ∀ t, Continuous (K t))
    (hKper : ∀ t, Periodic (K t) (P t)) (hkap0 : 0 ≤ kap) (hkap1 : kap ≤ 1)
    (hK0 : ∀ t s, 0 ≤ K t s) (hKk : ∀ t s, K t s ≤ kap) :
    ∃ δ : ℝ → ℝ → ℝ, ∀ t,
      Periodic (δ t) (P t) ∧
      (∀ s, δ t s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (δ t s)) ∧
      (∀ s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s) := by
  have hslice : ∀ t : ℝ, ∃ d : ℝ → ℝ, Periodic d (P t) ∧
      (∀ s, d s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (d s)) ∧
      (∀ s, HasDerivAt d (K t s - Real.sin (d s)) s) := fun t =>
    SteeringExistence.exists_periodic_steering (hP t) (hK t) (hKper t) hkap0 hkap1
      (hK0 t) (hKk t)
  choose δ hδ using hslice
  exact ⟨δ, hδ⟩

/-- **The rear-arclength inverse family.**  Each `rearArclength (δ t)` has
derivative `cos (δ t) ≥ √(1−κ̂²) > 0`, hence is surjective and admits a right
inverse `sf t`.  This supplies `hsfinv`. -/
theorem exists_sf_family {δ : ℝ → ℝ → ℝ} {kap : ℝ} (hkap1 : kap < 1)
    (hkap0 : 0 ≤ kap)
    (hδc : ∀ t, Continuous (δ t))
    (hcos : ∀ t s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (δ t s)) :
    ∃ sf : ℝ → ℝ → ℝ, ∀ t x, rearArclength (δ t) (sf t x) = x := by
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hslice : ∀ t : ℝ, ∃ g : ℝ → ℝ, ∀ x, rearArclength (δ t) (g x) = x := fun t =>
    exists_rightInverse hcpos (fun s => hasDerivAt_rearArclength (hδc t) s) (hcos t)
  choose sf hsf using hslice
  exact ⟨sf, hsf⟩

/-- The rear periods are positive, uniformly in time. -/
theorem rearPeriod_pos_family {δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kap : ℝ}
    (hkap1 : kap < 1) (hkap0 : 0 ≤ kap) (hP : ∀ t, 0 < P t)
    (hδc : ∀ t, Continuous (δ t))
    (hcos : ∀ t s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (δ t s)) (t : ℝ) :
    0 < rearArclength (δ t) (P t) :=
  SelectedInverseRearOwn.rearPeriod_pos (hP t) (Real.sqrt_pos.mpr (by nlinarith)) (hδc t) (hcos t)

/-- And bounded above by the front periods, so a uniform ceiling on `P`
transfers.  This is the `hQmax` hypothesis. -/
theorem rearPeriod_le_family {δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {Qmax : ℝ}
    (hP : ∀ t, 0 ≤ P t) (hδc : ∀ t, Continuous (δ t))
    (hPmax : ∀ t, P t ≤ Qmax) (t : ℝ) :
    rearArclength (δ t) (P t) ≤ Qmax :=
  le_trans (rearArclength_le_of_period (hδc t) (hP t)) (hPmax t)

end SteeringFamily
