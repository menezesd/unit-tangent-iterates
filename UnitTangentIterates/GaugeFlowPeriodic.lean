import Mathlib
import UnitTangentIterates.GlobalODE
import UnitTangentIterates.RearFrameUniformBounds

/-!
# The gauge parameter of a closed family is a normalized parameter

`NormalGaugeFamily.lean` transports the parameter of a moving family along the
flow `Φ` of the tangential rate `h = −ξ/v`, so that the family moves with a
purely normal velocity.  The path metric of `PathMetric.lean`, on the other
hand, is defined for families parametrized by a **normalized** parameter, in
which every slice has period one.

The two are compatible, and for a soft reason: the frame data of a *closed*
family is periodic in the arclength, with the period `Q` of the reference
slice, so the tangential rate is `Q`-periodic in the arclength as well; the
flow of a `Q`-periodic field commutes with the translation by `Q`.  Hence, if
the flow starts from `Φ(0, u) = Qu` — the arclength parametrization of the
reference slice, normalized to period one — then

`Φ(t, u + 1) = Φ(t, u) + Q`  for every time `t`,

so the flowed parameter has period one at every time.

Main results:

* `flow_translation` — the flow of a `Q`-periodic field commutes with the
  translation by `Q`;
* `periodic_comp_flow` — hence any `Q`-periodic function of the arclength
  becomes a `1`-periodic function of the gauge parameter;
* `periodic_rearFamily` — the rear tracks of the family of selected rears are
  periodic in the rear arclength, with the rear period;
* `gauge_parameter_normalized_rear` — **the gauge parameter of the family of
  selected rears is a normalized parameter**: each flowed slice has period one.
-/

noncomputable section

open Set Function

namespace GaugeFlowPeriodic

/-! ### The flow of a periodic field -/

/-- **The flow of a `Q`-periodic field commutes with the translation by `Q`.**
If the flow starts at `Φ(0, u) = Qu`, then `Φ(t, u + 1) = Φ(t, u) + Q` at every
time. -/
theorem flow_translation {h : ℝ → ℝ → ℝ} {K : NNReal} {Q : ℝ} {Phi : ℝ → ℝ → ℝ}
    (hlip : ∀ t, LipschitzWith K (h t))
    (hper : ∀ t, Function.Periodic (h t) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u) (u t : ℝ) :
    Phi t (u + 1) = Phi t u + Q := by
  have h1 : ∀ r, HasDerivAt (fun r' => Phi r' (u + 1)) (h r (Phi r (u + 1))) r :=
    fun r => hPhid (u + 1) r
  have h2 : ∀ r, HasDerivAt (fun r' => Phi r' u + Q) (h r (Phi r u + Q)) r := by
    intro r
    have hd := (hPhid u r).add_const Q
    rwa [hper r (Phi r u)]
  have h0 : dist ((fun r' => Phi r' (u + 1)) 0) ((fun r' => Phi r' u + Q) 0) = 0 := by
    simp only [hPhi0]
    rw [dist_eq_zero]
    ring
  have hb := GlobalODE.dist_le_of_global_solutions (K := K) hlip h1 h2 0 t
  rw [h0, zero_mul] at hb
  have := le_antisymm hb dist_nonneg
  simpa [dist_eq_zero] using this

/-- **A `Q`-periodic function of the arclength is a `1`-periodic function of
the gauge parameter.** -/
theorem periodic_comp_flow {α : Type*} {h : ℝ → ℝ → ℝ} {K : NNReal} {Q : ℝ}
    {Phi : ℝ → ℝ → ℝ} {G : ℝ → ℝ → α}
    (hlip : ∀ t, LipschitzWith K (h t))
    (hper : ∀ t, Function.Periodic (h t) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u)
    (hG : ∀ t, Function.Periodic (G t) Q) (t : ℝ) :
    Function.Periodic (fun u => G t (Phi t u)) 1 := by
  intro u
  simp only
  rw [flow_translation hlip hper hPhid hPhi0 u t, hG t (Phi t u)]

/-! ### The tangential rate of a closed family -/

/-- The tangential rate `−ξ/v` of a family whose frame data is periodic in the
arclength is itself periodic in the arclength. -/
theorem periodic_gaugeRate {xi v : ℝ → ℝ → ℝ} {Q : ℝ}
    (hxiper : ∀ a, Function.Periodic (xi a) Q) (hvper : ∀ a, Function.Periodic (v a) Q)
    (a : ℝ) : Function.Periodic (GaugeRate.gaugeRate xi v a) Q := by
  intro x
  simp only [GaugeRate.gaugeRate, hxiper a x, hvper a x]

/-! ### The family of selected rears -/

open Real Complex RearTrack RearFamilyFrame UniformFrameBounds

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} {P Q : ℝ}

/-- **The rear tracks of the family of selected rears are periodic in the rear
arclength**, with the rear period `Q`: the front is periodic and the `2π` turn
of the tangent angle is invisible to the exponential. -/
theorem periodic_rearFamily (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hFper : ∀ a, Function.Periodic (F a) P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P) (a : ℝ) :
    Function.Periodic (rearFamily F Θ δ σ a) Q := by
  intro x
  have hF : F a (σ (x + Q)) = F a (σ x) := by
    rw [hσper x]; exact hFper a (σ x)
  have hang : (Θ a (σ (x + Q)) - δ a (σ (x + Q)) : ℝ)
      = (Θ a (σ x) - δ a (σ x)) + 2 * Real.pi :=
    RearFrameUniformBounds.frameAngle_shift (Q := Q) (P := P) hσper hΘper hδper a x
  have key : ∀ A : ℂ, Complex.exp (Complex.I * (A + 2 * (Real.pi : ℂ)))
      = Complex.exp (Complex.I * A) := by
    intro A
    have h2pi : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 :=
      Complex.exp_two_pi_mul_I
    rw [show Complex.I * (A + 2 * (Real.pi : ℂ))
        = Complex.I * A + 2 * (Real.pi : ℂ) * Complex.I by ring, Complex.exp_add, h2pi,
      mul_one]
  have hexp : Complex.exp (Complex.I * ((Θ a (σ (x + Q)) - δ a (σ (x + Q)) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((Θ a (σ x) - δ a (σ x) : ℝ) : ℂ)) := by
    rw [hang]; push_cast; exact key _
  simp only [rearFamily, rearTrack, rearAngle, hF, hexp]

/-- **The gauge parameter of the family of selected rears is a normalized
parameter.**  If the frame data of the bundle is periodic in the rear arclength
with the rear period `Q` — which `RearFrameUniformBounds.lean` establishes for
the family of selected rears — and the gauge flow starts at `Φ(0, u) = Qu`,
then every flowed slice `u ↦ R(t, Φ(t, u))` has period one, so the family is
parametrized as the path metric of `PathMetric.lean` requires. -/
theorem gauge_parameter_normalized_rear (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ}
    (hxiper : ∀ a, Function.Periodic (D.xi a) Q) (hvper : ∀ a, Function.Periodic (D.v a) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u)
    (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hFper : ∀ a, Function.Periodic (F a) P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P) (t : ℝ) :
    Function.Periodic (fun u => rearFamily F Θ δ σ t (Phi t u)) 1 :=
  periodic_comp_flow (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate
    (periodic_gaugeRate hxiper hvper) hPhid hPhi0
    (periodic_rearFamily (P := P) hσper hFper hΘper hδper) t

/-- The hypotheses are satisfiable: with a vanishing tangential rate the gauge
flow is the dilation `Φ(t, u) = Qu`, which translates by `Q` as it should. -/
example (Q : ℝ) : ∃ (h : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ → ℝ) (K : NNReal),
    (∀ t, LipschitzWith K (h t)) ∧ (∀ t, Function.Periodic (h t) Q) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t) ∧
      (∀ u, Phi 0 u = Q * u) ∧ ∀ u t, Phi t (u + 1) = Phi t u + Q := by
  refine ⟨fun _ _ => 0, fun _ u => Q * u, 0, fun _ => LipschitzWith.const' 0,
    fun _ _ => rfl, fun u t => ?_, fun _ => rfl, fun u t => by ring⟩
  simpa using hasDerivAt_const t (Q * u)

end GaugeFlowPeriodic
