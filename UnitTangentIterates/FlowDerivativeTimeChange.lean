import Mathlib
import UnitTangentIterates.GaugeFlowTimeDerivative

/-! # Variational flows under a scalar time change -/

noncomputable section

open Function MeasureTheory intervalIntegral

namespace FlowDerivativeTimeChange

open FlowDerivative GaugeFlowTimeDerivative

/-- The first spatial variational flow commutes with a differentiable time
change fixing zero. -/
theorem flowDeriv_comp
    {B w : ℝ → ℝ} {hx : ℝ → ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}
    {ell t u : ℝ}
    (hB0 : B 0 = 0) (hBd : ∀ r, HasDerivAt B (w r) r)
    (hwc : Continuous w)
    (hgc : Continuous fun s => hx s (Phi s u)) :
    flowDeriv (fun r x => w r * hx (B r) x)
        (fun r v => Phi (B r) v) ell t u =
      flowDeriv hx Phi ell (B t) u := by
  have hchange := intervalIntegral.integral_comp_smul_deriv
    (a := 0) (b := t) (f := B) (f' := w) (g := fun s => hx s (Phi s u))
    (fun r _ => hBd r) hwc.continuousOn hgc
  simp only [smul_eq_mul, Function.comp_apply, hB0] at hchange
  simp only [flowDeriv]
  rw [hchange]

/-- The second spatial variational flow commutes with the same time change. -/
theorem flowDeriv2_comp
    {B w : ℝ → ℝ} {hx hxx : ℝ → ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}
    {ell t u : ℝ}
    (hB0 : B 0 = 0) (hBd : ∀ r, HasDerivAt B (w r) r)
    (hwc : Continuous w)
    (hxgc : Continuous fun s => hx s (Phi s u))
    (hxxgc : Continuous fun s => hxx s (Phi s u))
    (hFgc : Continuous fun s => flowDeriv hx Phi ell s u) :
    flowDeriv2 (fun r x => w r * hx (B r) x)
        (fun r x => w r * hxx (B r) x)
        (fun r v => Phi (B r) v) ell t u =
      flowDeriv2 hx hxx Phi ell (B t) u := by
  have hF : ∀ r,
      flowDeriv (fun a x => w a * hx (B a) x)
          (fun a v => Phi (B a) v) ell r u =
        flowDeriv hx Phi ell (B r) u := fun r =>
    flowDeriv_comp hB0 hBd hwc hxgc
  have hg : Continuous fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u :=
    hxxgc.mul hFgc
  have hchange := intervalIntegral.integral_comp_smul_deriv
    (a := 0) (b := t) (f := B) (f' := w)
    (g := fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u)
    (fun r _ => hBd r) hwc.continuousOn hg
  simp only [smul_eq_mul, Function.comp_apply, hB0] at hchange
  simp only [flowDeriv2]
  rw [hF t]
  congr 1
  rw [← hchange]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [hF r]
  ring

end FlowDerivativeTimeChange
