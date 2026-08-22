import Mathlib
import UnitTangentIterates.RearTrack
import UnitTangentIterates.SteeringExistence

/-!
# The selected inverse on the closed strip, assembled

This file combines the two halves of the lemma *Selected inverse on the closed
strip* of *A Noncircular Oval with Convex Unit-Tangent Iterates*:

> Let `F` be a regular convex `C²` closed curve with `0 ≤ K ≤ κ̂ < 1`.  There is
> a unique periodic steering solution `0 ≤ δ ≤ arcsin κ̂` of `δ_s = K − sin δ`.
> It defines a regular convex rear track.

The steering solution is produced in `SteeringExistence` (existence, by a fixed
point of the Poincaré map of the strip, and uniqueness), and the geometry of
the reconstructed rear is in `RearTrack`.  The statement below packages them:
from a unit-speed front `F` with tangent angle `Θ`, curvature `K = Θ_s`
continuous, `S`-periodic and inside `[0, κ̂]`, and with the tangent turning by
`2π` over a period, one obtains a rear track `R` with

* `R + e^{iΨ} = F`, i.e. `𝒯R = F`;
* `R_s = cos δ · e^{iΨ}` with `cos δ ≥ √(1 − κ̂²) > 0` — the rear is regular,
  and its arclength is strictly increasing;
* rear curvature `tan δ ≥ 0` — the rear is convex;
* the rear unit tangent is `S`-periodic — the rear closes up;
* and the steering angle producing it is the unique periodic one in the strip.
-/

noncomputable section

open Real Set Complex

namespace SelectedInverseStrip

/-- **Selected inverse on the closed strip.**  A unit-speed closed front whose
curvature is continuous, periodic and bounded by `κ̂ < 1` has a rear track,
regular and convex, obtained from the (unique) periodic steering solution in
the closed strip `[0, arcsin κ̂]`. -/
theorem selected_inverse_on_closed_strip {F : ℝ → ℂ} {Θ K : ℝ → ℝ} {S kap : ℝ}
    (hS : 0 < S) (hK : Continuous K) (hKper : Function.Periodic K S)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hK0 : ∀ s, 0 ≤ K s) (hKk : ∀ s, K s ≤ kap)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hturn : ∀ s, Θ (s + S) = Θ s + 2 * π) :
    ∃ delta : ℝ → ℝ,
      -- the steering angle: periodic, in the closed strip, and unique there
      Function.Periodic delta S ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) ∧
      (∀ e : ℝ → ℝ, Function.Periodic e S → (∀ s, e s ∈ Icc 0 (Real.arcsin kap)) →
        (∀ s, HasDerivAt e (K s - Real.sin (e s)) s) → e = delta) ∧
      -- the rear track it defines
      (∀ s, RearTrack.rearTrack F Θ delta s
          + Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ)) = F s) ∧
      (∀ s, HasDerivAt (RearTrack.rearTrack F Θ delta)
          ((Real.cos (delta s) : ℂ)
            * Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ))) s) ∧
      -- regularity
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      StrictMono (RearTrack.rearArclength delta) ∧
      -- convexity
      (∀ s, HasDerivAt (RearTrack.rearAngle Θ delta)
          (Real.tan (delta s) * Real.cos (delta s)) s) ∧
      (∀ s, 0 ≤ Real.tan (delta s)) ∧
      -- the rear closes up
      (∀ s, Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (s + S) : ℂ))
          = Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ))) := by
  obtain ⟨delta, hper, hrange, hcos, hode⟩ :=
    SteeringExistence.exists_periodic_steering hS hK hKper hkap0 hkap1.le hK0 hKk
  have hdcont : Continuous delta :=
    (Differentiable.continuous (fun s => (hode s).differentiableAt))
  have hstrip : ∀ (e : ℝ → ℝ), (∀ s, e s ∈ Icc 0 (Real.arcsin kap)) →
      ∀ s, e s ∈ Icc (-(π / 2)) (π / 2) := by
    intro e he s
    exact ⟨by linarith [(he s).1, Real.pi_pos], le_trans (he s).2 (Real.arcsin_le_pi_div_two kap)⟩
  have hcospos : ∀ s, 0 < Real.cos (delta s) := fun s =>
    RearTrack.rear_speed_ge hkap1 hkap0 (hrange s).1 (hrange s).2
  refine ⟨delta, hper, hrange, hode, ?_, ?_, ?_, hcos, ?_, ?_, ?_, ?_⟩
  · intro e hpere hrangee hodee
    exact Shadowing.steering_unique hS hodee hode hpere hper (hstrip e hrangee) (hstrip delta hrange)
  · exact fun s => RearTrack.unitTangentMap_rearTrack s
  · exact fun s => RearTrack.hasDerivAt_rearTrack (hF s) (hΘ s) (hode s)
  · exact RearTrack.strictMono_rearArclength hdcont hkap1 hkap0 (fun s => (hrange s).1)
      (fun s => (hrange s).2)
  · exact fun s => RearTrack.rear_curvature_eq_tan (hΘ s) (hode s) (ne_of_gt (hcospos s))
  · exact fun s => RearTrack.rear_curvature_nonneg hkap1 hkap0 (hrange s).1 (hrange s).2
  · exact fun s => RearTrack.rearTangent_periodic hper hturn s

end SelectedInverseStrip
