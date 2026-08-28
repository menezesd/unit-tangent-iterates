import UnitTangentIterates.GaugeRearFamilyRichTerminalStage
import UnitTangentIterates.MarkingFlowDefectC2
import UnitTangentIterates.NearIdentityDistortionBudget

/-!
# Near-identity bounds for the normalized terminal gauge marking

The terminal marking has `dpsi = flow1 / L` and `ddpsi = flow2 / L`.
The defining flow-jet equations retained by `TerminalJets` therefore turn the
integrated `MarkingFlowDefectC2` estimates directly into a single normalized
jet error suitable for `NearIdentityDistortionBudget`.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric FlowDerivative

namespace GaugeTerminalNearIdentityJets

open GaugeFlowMarkedTerminalJets GaugeRearFamilyRichTerminalStage
  GaugeRearFamilyVariableTerminal MarkingFlowDefectC2

def jetError (ell L c0 c2 : ℝ) : ℝ := max
  (flowDefectC1Int ell c0 / L) (flowDefectC2Int ell c0 c2 / L)

def jetLinearConst (ell L kappa kappa2 M : ℝ) : ℝ := max
  (ell * kappa * (Real.exp (kappa * M) + 1) / L)
  (ell ^ 2 * Real.exp (2 * kappa * M) * kappa2 / L)

theorem jetError_le_linear
    {ell L kappa kappa2 x M : ℝ}
    (hell : 0 ≤ ell) (hL : 0 < L) (hkappa : 0 ≤ kappa)
    (hkappa2 : 0 ≤ kappa2) (hx : 0 ≤ x) (hxM : x ≤ M) :
    jetError ell L (kappa * x) (kappa2 * x) ≤
      jetLinearConst ell L kappa kappa2 M * x := by
  obtain ⟨h1, h2⟩ := flowDefectInt_linear_bounds hell hkappa hkappa2 hx hxM
  apply max_le
  · calc
      flowDefectC1Int ell (kappa * x) / L ≤
          (ell * kappa * (Real.exp (kappa * M) + 1) * x) / L :=
        (div_le_div_iff_of_pos_right hL).2 h1
      _ = (ell * kappa * (Real.exp (kappa * M) + 1) / L) * x := by ring
      _ ≤ jetLinearConst ell L kappa kappa2 M * x :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hx
  · calc
      flowDefectC2Int ell (kappa * x) (kappa2 * x) / L ≤
          (ell ^ 2 * Real.exp (2 * kappa * M) * kappa2 * x) / L :=
        (div_le_div_iff_of_pos_right hL).2 h2
      _ = (ell ^ 2 * Real.exp (2 * kappa * M) * kappa2 / L) * x := by ring
      _ ≤ jetLinearConst ell L kappa kappa2 M * x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hx

theorem jetError_nonnegative
    {ell L c0 c2 : ℝ} (hell : 0 ≤ ell) (hL : 0 < L)
    (hc0 : 0 ≤ c0) (hc2 : 0 ≤ c2) :
    0 ≤ jetError ell L c0 c2 := by
  apply le_max_of_le_left
  exact div_nonneg (flowDefectC1Int_nonneg hell hc0) hL.le

/-- Summability transfer once the geometric parameters give a uniform linear
coefficient. -/
theorem summable_jetError_of_uniform_linear
    {eps x : ℕ → ℝ} {C : ℝ}
    (heps : ∀ k, 0 ≤ eps k) (hx : ∀ k, 0 ≤ x k)
    (hle : ∀ k, eps k ≤ C * x k) (hsum : Summable x) :
    Summable eps :=
  (hsum.mul_left C).of_nonneg_of_le heps hle

structure JetBounds
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : RichStageOutput J p front bound P0 kh khat M c C dlt)
    (eps : ℝ) : Prop where
  eps_nonnegative : 0 ≤ eps
  dpsi : ∀ u, |S.marking.dpsi u - 1| ≤ eps
  ddpsi : ∀ u, |S.ddpsi u| ≤ eps

/-- The quasi-periodic normalized marking forces the terminal flow period to
be exactly the physical scale `L`. -/
theorem terminal_flow_period
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    {J : TerminalJets xi xiX xiXX Phi ell L T base}
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : RichStageOutput J p front bound P0 kh khat M c C dlt)
    (hL : 0 < L) : Phi T 1 - Phi T 0 = L := by
  have h0 : Phi T 0 / L = 0 := by
    rw [← S.psi_eq]
    exact S.psi_zero
  have htr := S.marking.translate 0
  have h1 : Phi T 1 / L = 1 := by
    rw [← S.psi_eq]
    simpa [S.psi_zero] using htr
  have hLne : L ≠ 0 := ne_of_gt hL
  have hp0 : Phi T 0 = 0 := (div_eq_zero_iff).mp h0 |>.resolve_right hLne
  have hp1 : Phi T 1 = L := by
    apply (div_eq_iff hLne).mp at h1
    simpa using h1
  rw [hp0, hp1, sub_zero]

/-- Direct integrated flow estimates for the normalized first and second
marking jets. -/
def jetBounds_of_flow
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : RichStageOutput J p front bound P0 kh khat M c C dlt)
    (hell : 0 < ell) (hL : 0 < L) (hT : 0 ≤ T)
    {B B2 : ℝ → ℝ}
    (hB : Continuous B) (hB2 : Continuous B2)
    (hxiX : ∀ s x, |-(xiX s x)| ≤ B s)
    (hxiXX : ∀ s x, |-(xiXX s x)| ≤ B2 s) :
    JetBounds J S (jetError ell L
      (∫ s in (0 : ℝ)..T, B s) (∫ s in (0 : ℝ)..T, B2 s)) := by
  let c0 : ℝ := ∫ s in (0 : ℝ)..T, B s
  let c2 : ℝ := ∫ s in (0 : ℝ)..T, B2 s
  have hperiod : Phi T 1 - Phi T 0 = L := terminal_flow_period S hL
  have hfirst : ∀ u, |S.marking.dpsi u - 1| ≤ flowDefectC1Int ell c0 / L := by
    intro u
    have hraw := abs_flowDeriv_sub_period_le_int
      (hx := fun a y => -xiX a y) (Phi := Phi) hell hxiX hB hT
      (by simpa only [J.flow1_eq] using J.flow_deriv) u
    rw [hperiod] at hraw
    rw [← J.flow1_eq] at hraw
    rw [S.dpsi_eq]
    have heq : J.flow1 u / L - 1 = (J.flow1 u - L) / L := by
      field_simp
    rw [heq, abs_div, abs_of_pos hL]
    exact (div_le_div_iff_of_pos_right hL).2 (by simpa [c0] using hraw)
  have hsecond : ∀ u, |S.ddpsi u| ≤ flowDefectC2Int ell c0 c2 / L := by
    intro u
    have hraw := abs_flowDeriv_deriv_le_int
      (hx := fun a y => -xiX a y) (hxx := fun a y => -xiXX a y)
      (Phi := Phi) hell hxiX hB hxiXX hB2 hT u
    rw [S.ddpsi_eq, J.flow2_eq,
      GaugeFlowTimeDerivative.flowDeriv2, abs_div, abs_of_pos hL]
    exact (div_le_div_iff_of_pos_right hL).2 (by simpa [c0, c2] using hraw)
  have hc0 : 0 ≤ c0 := intervalIntegral.integral_nonneg hT (fun s _ => by
    exact le_trans (abs_nonneg (xiX s 0)) (by simpa using hxiX s 0))
  have hc2 : 0 ≤ c2 := intervalIntegral.integral_nonneg hT (fun s _ => by
    exact le_trans (abs_nonneg (xiXX s 0)) (by simpa using hxiXX s 0))
  have hd1 : 0 ≤ flowDefectC1Int ell c0 / L := div_nonneg
    (flowDefectC1Int_nonneg hell.le hc0) hL.le
  have hd2 : 0 ≤ flowDefectC2Int ell c0 c2 / L := by
    dsimp [flowDefectC2Int]
    positivity
  refine
    { eps_nonnegative := le_trans hd1 (le_max_left _ _)
      dpsi := fun u => (hfirst u).trans (le_max_left _ _)
      ddpsi := fun u => (hsecond u).trans (le_max_right _ _) }

end GaugeTerminalNearIdentityJets
