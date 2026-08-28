import Mathlib
import UnitTangentIterates.FlowJointContinuity

/-! # Joint continuity of the second initial-value derivative of a flow -/

noncomputable section

open Set Filter Topology MeasureTheory Function

namespace FlowJointContinuity

open FlowDerivative GaugeFlowTimeDerivative

/-- The closed-form second derivative of a scalar flow is jointly continuous
in time and initial parameter.  This is the joint version of
`continuous_flowDeriv2_initial`. -/
theorem continuous_flowDeriv2_prod
    {h hx hxx : ℝ → ℝ → ℝ} {K : NNReal} {ell : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (hlip : ∀ t, LipschitzWith K (h t))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxcont : Continuous (uncurry hx))
    (hxxcont : Continuous (uncurry hxx)) :
    Continuous fun p : ℝ × ℝ => flowDeriv2 hx hxx Phi ell p.1 p.2 := by
  have hflow : Continuous fun p : ℝ × ℝ => Phi p.1 p.2 :=
    continuous_flow_prod hlip hPhid hPhi0
  have hFD : Continuous fun p : ℝ × ℝ => flowDeriv hx Phi ell p.1 p.2 :=
    continuous_flowDeriv_prod hlip hPhid hPhi0 hxcont
  have hint : Continuous
      (uncurry fun z : ℝ × ℝ => fun s : ℝ =>
        hxx s (Phi s z.2) * flowDeriv hx Phi ell s z.2) := by
    have h1 : Continuous fun w : (ℝ × ℝ) × ℝ =>
        hxx w.2 (Phi w.2 w.1.2) :=
      hxxcont.comp (continuous_snd.prodMk
        (hflow.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))))
    have h2 : Continuous fun w : (ℝ × ℝ) × ℝ =>
        flowDeriv hx Phi ell w.2 w.1.2 :=
      hFD.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    simpa [uncurry] using h1.mul h2
  have hJ : Continuous fun z : ℝ × ℝ =>
      ∫ s in (0 : ℝ)..z.1,
        hxx s (Phi s z.2) * flowDeriv hx Phi ell s z.2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) hint continuous_fst
  simpa [flowDeriv2] using hFD.mul hJ

/-- Every time slice of the second flow derivative is continuous, projected
from the joint theorem. -/
theorem continuous_flowDeriv2_slice
    {h hx hxx : ℝ → ℝ → ℝ} {K : NNReal} {ell t : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (hlip : ∀ r, LipschitzWith K (h r))
    (hPhid : ∀ u r, HasDerivAt (fun s => Phi s u) (h r (Phi r u)) r)
    (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxcont : Continuous (uncurry hx))
    (hxxcont : Continuous (uncurry hxx)) :
    Continuous fun u => flowDeriv2 hx hxx Phi ell t u :=
  (continuous_flowDeriv2_prod hlip hPhid hPhi0 hxcont hxxcont).comp
    (continuous_const.prodMk continuous_id)

end FlowJointContinuity

