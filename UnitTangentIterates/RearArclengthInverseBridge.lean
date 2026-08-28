import Mathlib
import UnitTangentIterates.ArclengthInverse

noncomputable section

open Function Set

namespace RearArclengthInverseBridge

open RearTrack ArclengthInverse

/-- Complete inverse data for rear arclength on the selected steering strip. -/
structure Data (delta sf : ℝ → ℝ) (P : ℝ) where
  rearPeriod : ℝ
  rightInverse : ∀ x, rearArclength delta (sf x) = x
  leftInverse : ∀ s, sf (rearArclength delta s) = s
  sf_continuous : Continuous sf
  sf_deriv : ∀ x, HasDerivAt sf (1 / Real.cos (delta (sf x))) x
  arclength_shift : ∀ s,
    rearArclength delta (s + P) = rearArclength delta s + rearPeriod
  sf_shift : ∀ x, sf (x + rearPeriod) = sf x + P

/-- A right inverse of rear arclength automatically has all differential and
periodic inverse properties on the selected strip. -/
def data_of_rightInverse
    {kap P : ℝ} {delta sf : ℝ → ℝ}
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hdeltaC : Continuous delta) (hdeltaPer : Periodic delta P)
    (hdelta0 : ∀ s, 0 ≤ delta s)
    (hdelta1 : ∀ s, delta s ≤ Real.arcsin kap)
    (hsf : ∀ x, rearArclength delta (sf x) = x) :
    Data delta sf P := by
  have hc : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdelta0 s) (hdelta1 s)
  have hderiv : ∀ s, HasDerivAt (rearArclength delta)
      (Real.cos (delta s)) s := hasDerivAt_rearArclength hdeltaC
  have hmono : StrictMono (rearArclength delta) :=
    strictMono_rearArclength hdeltaC hkap1 hkap0 hdelta0 hdelta1
  refine
    { rearPeriod := rearArclength delta P
      rightInverse := hsf
      leftInverse := ?_
      sf_continuous := continuous_of_rightInverse hc hderiv hcos hsf
      sf_deriv := hasDerivAt_of_rightInverse hc hderiv hcos hsf
      arclength_shift := rearArclength_add_period hdeltaC hdeltaPer
      sf_shift := ?_ }
  · intro s
    apply hmono.injective
    exact hsf (rearArclength delta s)
  · intro x
    exact rightInverse_add_of_shift hmono.injective
      (rearArclength_add_period hdeltaC hdeltaPer) hsf x

/-- Pullback by the inverse converts front-periodic functions into
rear-periodic functions. -/
theorem periodic_comp_sf
    {delta sf f : ℝ → ℝ} {P : ℝ} (D : Data delta sf P)
    (hf : Periodic f P) : Periodic (fun x => f (sf x)) D.rearPeriod := by
  intro x
  change f (sf (x + D.rearPeriod)) = f (sf x)
  rw [D.sf_shift, hf]

/-- The inverse speed is periodic in rear arclength. -/
theorem periodic_inverseSpeed
    {delta sf : ℝ → ℝ} {P : ℝ} (D : Data delta sf P)
    (hdeltaPer : Periodic delta P) :
    Periodic (fun x => 1 / Real.cos (delta (sf x))) D.rearPeriod := by
  apply periodic_comp_sf D (f := fun s => 1 / Real.cos (delta s))
  intro s
  change 1 / Real.cos (delta (s + P)) = 1 / Real.cos (delta s)
  rw [hdeltaPer]

/-- Any front-periodic scalar observable remains continuous and periodic after
conversion to rear arclength. -/
theorem continuous_periodic_comp_sf
    {delta sf f : ℝ → ℝ} {P : ℝ} (D : Data delta sf P)
    (hfC : Continuous f) (hfPer : Periodic f P) :
    Continuous (fun x => f (sf x)) ∧
      Periodic (fun x => f (sf x)) D.rearPeriod :=
  ⟨hfC.comp D.sf_continuous, periodic_comp_sf D hfPer⟩

end RearArclengthInverseBridge
