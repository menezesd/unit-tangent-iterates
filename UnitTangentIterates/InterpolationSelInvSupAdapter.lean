import Mathlib
import UnitTangentIterates.SelectedRearGaugeQualitative
import UnitTangentIterates.SelInvRearFamilySupFundamentalC2

/-!
# Adapter from smooth interpolation data to the marking-defect comparison

`SelInvRearFamilySupFundamentalC2` is the correct terminal-marking interface:
it compares the nonaffinely gauge-marked terminal rear with the canonical
marked selected inverse using `MarkingFlowDefectC2`.  This file supplies its
entire qualitative rear-family hypothesis block from the smooth interpolation
data.  Periodicity of the normal rate and all numerical bounds remain explicit
because they are genuinely quantitative inputs of that comparison theorem.
-/

noncomputable section

open Function Set Complex RearTrack RearOwnArclength RearFamilyFrame

namespace InterpolationSelInvSupAdapter

open RearOwnHigherRegularity RearOwnMotion

variable {F : ℝ → ℝ → ℂ} {Theta delta K sf : ℝ → ℝ → ℝ} {kh : ℝ}

/-- **The qualitative hypothesis block of the sup-fundamental selected-rear
comparison.**  The source in the inverse Jacobi equation is chosen canonically
as the front normal velocity. -/
theorem exists_sup_fundamental_qualitative_inputs
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hF4 : ContDiff ℝ (4 : ℕ) (uncurry F))
    (hTheta4 : ContDiff ℝ (4 : ℕ) (uncurry Theta))
    (hdelta4 : ContDiff ℝ (4 : ℕ) (uncurry delta))
    (hsf4 : ContDiff ℝ (4 : ℕ) (uncurry sf))
    (hfront : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Theta t s : ℂ))) s)
    (hTheta : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    ∃ Ydot : ℝ → ℝ → ℂ,
      (∀ t x, HasDerivAt (fun r => rearOwn F Theta delta sf r x) (Ydot t x) t) ∧
      ContDiff ℝ 1 (uncurry delta) ∧
      ContDiff ℝ 1 (uncurry sf) ∧
      ContDiff ℝ (3 : ℕ) (uncurry Ydot) ∧
      ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Theta delta sf)) ∧
      ContDiff ℝ 1 (uncurry fun t x => Real.tan (delta t (sf t x))) ∧
      (∀ t x, HasDerivAt
        (fun x' => frameNormal Ydot (rearOwnAngle Theta delta sf) t x')
        (frontNormalVelocityAt (partialTime F) Theta delta t (sf t x)
            / Real.cos (delta t (sf t x))
          - frameNormal Ydot (rearOwnAngle Theta delta sf) t x) x) := by
  obtain ⟨Ydot, hYt, hYdot3, hang3, htan1, hjac⟩ :=
    SelectedRearGaugeQualitative.exists_canonical_gauge_jacobi_data_c3
      hkh0 hkh1 hF4 hTheta4 hdelta4 hsf4 hfront hTheta hsteer
      hstrip0 hstrip1 hsfinv
  exact ⟨Ydot, hYt, hdelta4.of_le (by norm_num), hsf4.of_le (by norm_num),
    hYdot3, hang3, htan1, hjac⟩

end InterpolationSelInvSupAdapter
