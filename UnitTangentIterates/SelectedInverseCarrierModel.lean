import Mathlib
import UnitTangentIterates.SelectedInverseCarrier
import UnitTangentIterates.SteeringExistence
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.TwoCapPairsAssembly

/-!
# The rear carrier of a model front is produced by the model curvature alone

`SelectedInverseCarrier.rearOwn_carrier` asks for a front `F` with tangent angle
`Θ`, a steering angle `δ` solving `δ_s = K − sin δ` and staying on the selected
strip, and a right inverse `sf` of the rear arclength.  For the **model front**
of the paper — the curve `TwoCapPairsAssembly.front κ θ₀ H` reconstructed from a
model curvature `κ` — all of these are produced by `κ` itself:

* the front and its tangent angle are the reconstruction and its tangent angle
  (`TwoCapPairsAssembly.front_hasDerivAt`);
* the periodic steering angle on the closed strip exists for any continuous
  periodic curvature pinched by `0 ≤ κ ≤ κ̂ ≤ 1`
  (`SteeringExistence.exists_periodic_steering`);
* the rear arclength `x = ∫ cos δ` has a right inverse, its derivative being at
  least `√(1 − κ̂²) > 0` (`ArclengthInverse.exists_inverse_rearArclength`).

`exists_rear_carrier_of_model` assembles them: for a model curvature pinched by
`0 ≤ κ ≤ κ̂ < 1` the rear track of the model front, written in its own
arclength, is a unit-speed curve whose tangent angle has derivative the rear
curvature `k_H = tan δ ∘ sf`, and that curvature satisfies the relation
`k_H(x_H)cos δ = sin δ` of the theorem *Curvature-measure matching*.  So the
rear side of a matching configuration over a model curvature needs no data
beyond that curvature.
-/

noncomputable section

open Real Set Function MeasureTheory

namespace SelectedInverseCarrierModel

open CurvatureInterpolation RearTrack ArclengthInverse SteeringExistence
  TwoCapPairsAssembly SelectedInverseCarrier

/-- **The rear carrier of a model front, produced from the model curvature.**
For a continuous `H`-periodic curvature pinched by `0 ≤ κ ≤ κ̂ < 1` there are a
periodic steering angle `δ` on the closed strip, a right inverse `sf` of the
rear arclength and a rear curvature `k_H` such that `k_H(x_H)cos δ = sin δ` and
the rear track of the model front written in its own arclength is a unit-speed
carrier of `k_H`. -/
theorem exists_rear_carrier_of_model {kappa : ℝ → ℝ} {H kap theta0 : ℝ}
    (hH : 0 < H) (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkk : ∀ s, kappa s ≤ kap) :
    ∃ delta sf kH : ℝ → ℝ,
      Periodic delta H ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      (∀ s, HasDerivAt delta (kappa s - Real.sin (delta s)) s) ∧
      (∀ x, rearArclength delta (sf x) = x) ∧
      (∀ t, kH (rearArclength delta t) * Real.cos (delta t) = Real.sin (delta t)) ∧
      (∀ x, HasDerivAt
          (fun z => rearTrack (front kappa theta0 H) (frontAngle kappa theta0) delta (sf z))
          (tau (rearAngle (frontAngle kappa theta0) delta (sf x))) x) ∧
      (∀ x, HasDerivAt
          (fun z => rearAngle (frontAngle kappa theta0) delta (sf z)) (kH x) x) := by
  -- the steering angle
  obtain ⟨delta, hdper, hdstrip, hdcos, hdode⟩ :=
    exists_periodic_steering hH hk hper hkap0 hkap1.le hk0 hkk
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hdc : Continuous delta :=
    continuous_iff_continuousAt.mpr fun s => (hdode s).continuousAt
  have hcospos : ∀ s, 0 < Real.cos (delta s) := fun s => lt_of_lt_of_le hcpos (hdcos s)
  -- the inverse of the rear arclength
  obtain ⟨sf, hsfinv⟩ :=
    exists_inverse_rearArclength hkap0 hkap1 hdc (fun s => (hdstrip s).1) (fun s => (hdstrip s).2)
  -- the rear arclength is injective, so `sf` is a two-sided inverse
  have hmono : StrictMono (rearArclength delta) :=
    strictMono_of_deriv_ge hcpos (fun s => hasDerivAt_rearArclength hdc s) hdcos
  have hsfleft : ∀ t, sf (rearArclength delta t) = t := fun t =>
    leftInverse_of_rightInverse hmono.injective hsfinv t
  have hkrel : ∀ t, (fun x => Real.tan (delta (sf x))) (rearArclength delta t)
      * Real.cos (delta t) = Real.sin (delta t) := by
    intro t
    simp only [hsfleft t, Real.tan_eq_sin_div_cos]
    field_simp
    rw [mul_div_assoc, div_self (hcospos t).ne', mul_one]
  have hcarrier := rearOwn_carrier (c := Real.sqrt (1 - kap ^ 2)) (K := kappa)
    (kH := fun x => Real.tan (delta (sf x))) hcpos hdc hdcos hsfinv
    (fun s => front_hasDerivAt (theta0 := theta0) (H := H) hk s)
    (fun s => hasDerivAt_tangentAngle (θ₀ := theta0) hk s) hdode hkrel
  exact ⟨delta, sf, fun x => Real.tan (delta (sf x)), hdper, hdstrip, hdcos, hdode, hsfinv,
    hkrel, hcarrier.1, hcarrier.2⟩

/-- **The hypotheses are not vacuous**: the constant curvature `1/2` of the
circle, of period `2π`, satisfies them with `κ̂ = 1/2`. -/
theorem exists_rear_carrier_of_model_circle :
    ∃ delta sf kH : ℝ → ℝ,
      Periodic delta (2 * Real.pi) ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin (1/2))) ∧
      (∀ s, Real.sqrt (1 - (1/2 : ℝ) ^ 2) ≤ Real.cos (delta s)) ∧
      (∀ s, HasDerivAt delta ((1/2 : ℝ) - Real.sin (delta s)) s) ∧
      (∀ x, rearArclength delta (sf x) = x) ∧
      (∀ t, kH (rearArclength delta t) * Real.cos (delta t) = Real.sin (delta t)) ∧
      (∀ x, HasDerivAt
          (fun z => rearTrack (front (fun _ => 1/2) 0 (2 * Real.pi))
            (frontAngle (fun _ => 1/2) 0) delta (sf z))
          (tau (rearAngle (frontAngle (fun _ => (1:ℝ)/2) 0) delta (sf x))) x) ∧
      (∀ x, HasDerivAt
          (fun z => rearAngle (frontAngle (fun _ => (1:ℝ)/2) 0) delta (sf z)) (kH x) x) :=
  exists_rear_carrier_of_model (kappa := fun _ => 1/2) (H := 2 * Real.pi) (kap := 1/2)
    (theta0 := 0) (by positivity) continuous_const (fun _ => rfl) (by norm_num) (by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl)

end SelectedInverseCarrierModel
