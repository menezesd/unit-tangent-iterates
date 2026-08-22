import Mathlib
import UnitTangentIterates.SteeringExistence
import UnitTangentIterates.SelectedRear
import UnitTangentIterates.RearDependence

/-!
# The selected inverse as an operator on front curvatures

The shadowing scheme of *A Noncircular Oval with Convex Unit-Tangent Iterates*
uses the **selected inverse** `B`, the map sending a front to its selected rear
track.  `SteeringExistence.lean` shows that the periodic steering angle inside
the closed strip exists and is unique, and `SelectedRear.lean` shows that it
depends Lipschitz-continuously on the front curvature.  This file turns those
two facts into an honest *operator*: on the set of admissible front curvatures

```
  Admissible S κ̂ K :  K continuous, S-periodic, 0 ≤ K ≤ κ̂
```

the assignment `K ↦ δ_K` is a well-defined function, characterized by the
properties of the selected steering angle, and non-expansive up to the factor
`1/√(1 − κ̂²)`:

```
  ‖δ_{K¹} − δ_{K²}‖_∞ ≤ ‖K¹ − K²‖_∞ / √(1 − κ̂²) .
```

Main results:

* `selectedSteering_periodic`, `selectedSteering_mem_strip`,
  `selectedSteering_hasDerivAt` : the defining properties;
* `eq_selectedSteering` : any periodic steering solution in the strip *is* the
  selected one — the operator is single-valued;
* `selectedSteering_sup_dist_le` : the Lipschitz bound, so the selected inverse
  is defined and continuous on the admissible set;
* `selectedRearCurvature_dist_le` : the induced rear curvature `tan δ_K` is
  Lipschitz in the front curvature as well.
-/

noncomputable section

open Real Set

namespace SelectedOperator

/-- The admissible front curvatures: continuous, `S`-periodic, with values in
`[0, κ̂]`. -/
structure Admissible (S kap : ℝ) (K : ℝ → ℝ) : Prop where
  continuous : Continuous K
  periodic : Function.Periodic K S
  nonneg : ∀ s, 0 ≤ K s
  le : ∀ s, K s ≤ kap

variable {S kap : ℝ} {K K1 K2 : ℝ → ℝ}

/-- The data needed for the selected steering angle to be defined. -/
private def Ok (S kap : ℝ) (K : ℝ → ℝ) : Prop :=
  0 < S ∧ 0 ≤ kap ∧ kap ≤ 1 ∧ Admissible S kap K

private theorem exists_sol (h : Ok S kap K) :
    ∃ delta : ℝ → ℝ, Function.Periodic delta S ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) :=
  SteeringExistence.exists_periodic_steering h.1 h.2.2.2.continuous h.2.2.2.periodic
    h.2.1 h.2.2.1 h.2.2.2.nonneg h.2.2.2.le

open Classical in
/-- **The selected steering angle of a front curvature**: the unique
`S`-periodic solution of `δ_s = K − sin δ` in the closed strip
`[0, arcsin κ̂]`.  (Off the admissible set the operator is set to `0`.) -/
def selectedSteering (S kap : ℝ) (K : ℝ → ℝ) : ℝ → ℝ :=
  if h : Ok S kap K then (exists_sol h).choose else 0

/-- The rear curvature selected by the front curvature `K`. -/
def selectedRearCurvature (S kap : ℝ) (K : ℝ → ℝ) : ℝ → ℝ :=
  fun s => Real.tan (selectedSteering S kap K s)

variable (hS : 0 < S) (hkap0 : 0 ≤ kap) (hkap1 : kap ≤ 1)

section Defining

variable (hK : Admissible S kap K)
include hS hkap0 hkap1 hK

private theorem ok : Ok S kap K := ⟨hS, hkap0, hkap1, hK⟩

theorem selectedSteering_periodic : Function.Periodic (selectedSteering S kap K) S := by
  rw [selectedSteering, dif_pos (ok hS hkap0 hkap1 hK)]
  exact (exists_sol (ok hS hkap0 hkap1 hK)).choose_spec.1

theorem selectedSteering_mem_strip (s : ℝ) :
    selectedSteering S kap K s ∈ Icc 0 (Real.arcsin kap) := by
  rw [selectedSteering, dif_pos (ok hS hkap0 hkap1 hK)]
  exact (exists_sol (ok hS hkap0 hkap1 hK)).choose_spec.2.1 s

theorem selectedSteering_cos_ge (s : ℝ) :
    Real.sqrt (1 - kap ^ 2) ≤ Real.cos (selectedSteering S kap K s) := by
  rw [selectedSteering, dif_pos (ok hS hkap0 hkap1 hK)]
  exact (exists_sol (ok hS hkap0 hkap1 hK)).choose_spec.2.2.1 s

theorem selectedSteering_hasDerivAt (s : ℝ) :
    HasDerivAt (selectedSteering S kap K)
      (K s - Real.sin (selectedSteering S kap K s)) s := by
  rw [selectedSteering, dif_pos (ok hS hkap0 hkap1 hK)]
  exact (exists_sol (ok hS hkap0 hkap1 hK)).choose_spec.2.2.2 s

/-- **The selected inverse is single-valued**: a periodic steering solution in
the closed strip is *the* selected one. -/
theorem eq_selectedSteering {e : ℝ → ℝ} (hper : Function.Periodic e S)
    (hrange : ∀ s, e s ∈ Icc 0 (Real.arcsin kap))
    (hode : ∀ s, HasDerivAt e (K s - Real.sin (e s)) s) :
    e = selectedSteering S kap K := by
  have hstrip : ∀ (f : ℝ → ℝ), (∀ s, f s ∈ Icc 0 (Real.arcsin kap)) →
      ∀ s, f s ∈ Icc (-(π / 2)) (π / 2) := by
    intro f hf s
    exact ⟨by linarith [(hf s).1, Real.pi_pos], le_trans (hf s).2 (Real.arcsin_le_pi_div_two kap)⟩
  exact Shadowing.steering_unique hS hode (selectedSteering_hasDerivAt hS hkap0 hkap1 hK) hper
    (selectedSteering_periodic hS hkap0 hkap1 hK) (hstrip e hrange)
    (hstrip _ (selectedSteering_mem_strip hS hkap0 hkap1 hK))

end Defining

/-- **The selected inverse is Lipschitz on the admissible set**:
`‖δ_{K¹} − δ_{K²}‖_∞ ≤ ‖K¹ − K²‖_∞ / √(1 − κ̂²)`. -/
theorem selectedSteering_sup_dist_le (hS : 0 < S) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (h1 : Admissible S kap K1) (h2 : Admissible S kap K2) {M : ℝ}
    (hM : ∀ s, |K1 s - K2 s| ≤ M) (s : ℝ) :
    |selectedSteering S kap K1 s - selectedSteering S kap K2 s|
      ≤ M / Real.sqrt (1 - kap ^ 2) :=
  SelectedRear.steering_sup_dist_le hS hkap1 hkap0
    (selectedSteering_hasDerivAt hS hkap0 hkap1.le h1)
    (selectedSteering_hasDerivAt hS hkap0 hkap1.le h2)
    (selectedSteering_periodic hS hkap0 hkap1.le h1)
    (selectedSteering_periodic hS hkap0 hkap1.le h2)
    (selectedSteering_mem_strip hS hkap0 hkap1.le h1)
    (selectedSteering_mem_strip hS hkap0 hkap1.le h2) hM s

/-- The selected **rear curvature** is Lipschitz in the front curvature too. -/
theorem selectedRearCurvature_dist_le (hS : 0 < S) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (h1 : Admissible S kap K1) (h2 : Admissible S kap K2) {M : ℝ}
    (hM : ∀ s, |K1 s - K2 s| ≤ M) (s : ℝ) :
    |selectedRearCurvature S kap K1 s - selectedRearCurvature S kap K2 s|
      ≤ M / Real.sqrt (1 - kap ^ 2) / (1 - kap ^ 2) := by
  have hk2 : (0:ℝ) < 1 - kap ^ 2 := by nlinarith
  have htan := RearDependence.abs_tan_sub_tan_le hkap0 hkap1
    (selectedSteering_mem_strip hS hkap0 hkap1.le h1 s)
    (selectedSteering_mem_strip hS hkap0 hkap1.le h2 s)
  have hd := selectedSteering_sup_dist_le hS hkap0 hkap1 h1 h2 hM s
  refine le_trans htan ?_
  gcongr

end SelectedOperator
