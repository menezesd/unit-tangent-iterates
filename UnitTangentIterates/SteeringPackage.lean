import UnitTangentIterates.SteeringFamily
import UnitTangentIterates.SteeringArclengthJointC1

/-!
# The complete steering package at a common period
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real ArclengthInverse RearTrack

namespace SteeringFamily

/-- **The steering family of a moving front of fixed period, with its joint `C¹`
regularity.**

`exists_steering_family` produces `δ` by `choose`, so it carries no regularity in
the time parameter, while the rear-family constructor wants
`ContDiff ℝ 1 (uncurry δ)`.  For a **common** period that regularity is already
available: `SteeringArclengthJointC1.contDiff_one_uncurry_delta_arc` proves it
from a Lipschitz and a Taylor estimate on the curvature in the time parameter.

This theorem is the two combined, so the whole steering side of the constructor's
hypothesis list is produced at once:

  `hstrip0`, `hstrip1`, `hsteer`, `hδper`, `hcos`, `hδC`.

The restriction to a *fixed* period `P` is exactly the boundary the manifest
records (`PaperFormalizationManifest`, the variable-period passage): with `P`
varying, `SteeringVariablePeriod.continuous_uncurry_delta` still gives
continuity, but the `C¹` statement is not yet available. -/
theorem exists_steering_family_contDiff {K Kd : ℝ → ℝ → ℝ} {P kap Klip CK : ℝ}
    (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hKslice : ∀ t, Continuous (K t)) (hKper : ∀ t, Periodic (K t) P)
    (hK0 : ∀ t s, 0 ≤ K t s) (hKk : ∀ t s, K t s ≤ kap)
    (hKdper : ∀ t, Periodic (Kd t) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) :
    ∃ δ : ℝ → ℝ → ℝ,
      (∀ t, Periodic (δ t) P) ∧
      (∀ t s, δ t s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ t s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (δ t s)) ∧
      (∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s) ∧
      ContDiff ℝ 1 (uncurry δ) := by
  obtain ⟨δ, hδ⟩ := exists_steering_family (P := fun _ => P) (fun _ => hP)
    hKslice hKper hkap0 hkap1.le hK0 hKk
  refine ⟨δ, fun t => (hδ t).1, fun t s => (hδ t).2.1 s,
    fun t s => (hδ t).2.2.1 s, fun t s => (hδ t).2.2.2 s, ?_⟩
  exact SteeringArclengthJointC1.contDiff_one_uncurry_delta_arc hP hkap0 hkap1
    hKcont hKdcont (fun a s => (hδ a).2.2.2 s) (fun a => (hδ a).1)
    (fun a s => (hδ a).2.1 s) hKdper hKlip hKtaylor hCK

/-- The rear-arclength inverses of that family, completing `hsfinv`. -/
theorem exists_sf_of_package {δ : ℝ → ℝ → ℝ} {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hkap1 : kap < 1) (hδC : ContDiff ℝ 1 (uncurry δ))
    (hcos : ∀ t s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (δ t s)) :
    ∃ sf : ℝ → ℝ → ℝ, ∀ t x, rearArclength (δ t) (sf t x) = x := by
  have hslice : ∀ t, Continuous (δ t) := by
    intro t
    have := hδC.continuous
    exact this.comp (continuous_const.prodMk continuous_id)
  exact exists_sf_family hkap1 hkap0 hslice hcos

end SteeringFamily
