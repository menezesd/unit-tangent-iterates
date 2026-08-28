import UnitTangentIterates.GaugeTerminalNearIdentityJets
import UnitTangentIterates.ConfiguredStableRowDefectProvider
import UnitTangentIterates.NormalizedMarkingControlledJunction

/-!
# Summable configured gauge-jet distortion

The spatial derivatives of the rear-frame gauge field are bounded by the
first two rear-curvature constants times the preceding path density.  The
terminal flow estimates therefore make both normalized marking jets linear in
the actual stable row defect.  This module packages that estimate and the
resulting tail distortion budget.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric FlowDerivative

namespace ConfiguredGaugeJetDistortion

open GaugeTerminalNearIdentityJets GaugeFlowMarkedTerminalJets
  GaugeRearFamilyRichTerminalStage GaugeRearFamilyVariableTerminal
  ConfiguredApproximateDefectPathRowwise
  AnchoredJacobiStableTransition NormalizedTerminalMarkingComposition
  NormalizedMarkingControlledJunction

/-- Uniform majorant used for the two normalized terminal marking jets. -/
def eps (D : ConstructedConfiguredSequenceWeighted.Data)
    (Cjet : ℝ) (n k : ℕ) : ℝ := Cjet * rowDefect D (n + k)

theorem eps_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) {Cjet : ℝ}
    (hCjet : 0 ≤ Cjet) (n k : ℕ) : 0 ≤ eps D Cjet n k :=
  mul_nonneg hCjet ((ConfiguredStableRowDefectProvider.provider D).nonnegative n k)

theorem summable_eps
    (D : ConstructedConfiguredSequenceWeighted.Data) {Cjet : ℝ}
    (n : ℕ) : Summable (eps D Cjet n) := by
  simpa [eps, ConfiguredStableRowDefectProvider.error] using
    ((ConfiguredStableRowDefectProvider.provider D).summable n).mul_left Cjet

theorem tsum_eps
    (D : ConstructedConfiguredSequenceWeighted.Data) (Cjet : ℝ) (n : ℕ) :
    (∑' k, eps D Cjet n k) =
      Cjet * ∑' k, rowDefect D (n + k) := by
  simp [eps, tsum_mul_left]

/-- Every configured row has a depth after which both marking jets are at
most `1/2`. -/
theorem eventually_eps_le_half
    (D : ConstructedConfiguredSequenceWeighted.Data) {Cjet : ℝ}
    (n : ℕ) : ∀ᶠ k in Filter.atTop, eps D Cjet n k ≤ 1 / 2 := by
  have ht : Filter.Tendsto (eps D Cjet n) Filter.atTop (nhds 0) :=
    (summable_eps D n).tendsto_atTop_zero
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [he] with k hk
  exact hk.le

/-- Enlarge a concrete jet certificate to a larger scalar majorant. -/
def jetBounds_mono
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    {J : TerminalJets xi xiX xiXX Phi ell L T base}
    {p front : Data} {bound P0 kh khat M c C dlt e e' : ℝ}
    {S : RichStageOutput J p front bound P0 kh khat M c C dlt}
    (B : JetBounds J S e) (hee : e ≤ e') : JetBounds J S e' where
  eps_nonnegative := B.eps_nonnegative.trans hee
  dpsi u := (B.dpsi u).trans hee
  ddpsi u := (B.ddpsi u).trans hee

/-- The concrete jet estimate supplies exactly the controlled-junction
parameters consumed by the arclength-scaled transition. -/
def controlledAnchoringBounds_of_jetBounds
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    {J : TerminalJets xi xiX xiXX Phi ell L T base}
    {p front : Data} {bound P0 kh khat M c C dlt e : ℝ}
    {S : RichStageOutput J p front bound P0 kh khat M c C dlt}
    (B : JetBounds J S e) (he : e ≤ 1 / 2) :
    ControlledAnchoringBounds (NormalizedC2Marking.ofRichStage S)
      (1 - e) (1 + e) e := by
  have hm : 0 < 1 - e := by linarith [B.eps_nonnegative]
  refine
    { m_pos := hm
      M_nonneg := by linarith [B.eps_nonnegative]
      N_nonneg := B.eps_nonnegative
      lower := ?_
      upper := ?_
      second := B.ddpsi }
  · intro u
    have hneg := neg_le_of_abs_le (B.dpsi u)
    dsimp [NormalizedC2Marking.ofRichStage]
    linarith
  · intro u
    dsimp [NormalizedC2Marking.ofRichStage]
    calc
      |S.marking.dpsi u| = |(S.marking.dpsi u - 1) + 1| := by ring_nf
      _ ≤ |S.marking.dpsi u - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ e + 1 := by simpa using add_le_add_right (B.dpsi u) 1
      _ = 1 + e := by ring

/-- Direct actual-stage estimate.  The two frame derivative bounds are the
ones proved internally by the long rear-family construction; this theorem
turns them into terminal marking jets rather than assuming a `JetBounds`
callback. -/
theorem stage_jetBounds
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : RichStageOutput J p front bound P0 kh khat M c C dlt)
    {m : ℝ → ℝ} {kappa kappa2 Mcap : ℝ}
    (hell : 0 < ell) (hL : 0 < L) (hT : 0 ≤ T)
    (hm : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hxiX : ∀ t x, |-(xiX t x)| ≤ kappa * m t)
    (hxiXX : ∀ t x, |-(xiXX t x)| ≤ kappa2 * m t)
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hcost : (∫ t in (0 : ℝ)..T, m t) ≤ Mcap) :
    let x := ∫ t in (0 : ℝ)..T, m t
    let e := jetError ell L (kappa * x) (kappa2 * x)
    JetBounds J S e ∧
      e ≤ jetLinearConst ell L kappa kappa2 Mcap * x := by
  dsimp only
  let B : ℝ → ℝ := fun t => kappa * m t
  let B2 : ℝ → ℝ := fun t => kappa2 * m t
  have hx : 0 ≤ ∫ t in (0 : ℝ)..T, m t :=
    intervalIntegral.integral_nonneg hT (fun t _ => hm0 t)
  have hB : Continuous B := continuous_const.mul hm
  have hB2 : Continuous B2 := continuous_const.mul hm
  have hJB := jetBounds_of_flow J S hell hL hT hB hB2 hxiX hxiXX
  have hIntB : (∫ t in (0 : ℝ)..T, B t) =
      kappa * ∫ t in (0 : ℝ)..T, m t := by
    simp [B, intervalIntegral.integral_const_mul]
  have hIntB2 : (∫ t in (0 : ℝ)..T, B2 t) =
      kappa2 * ∫ t in (0 : ℝ)..T, m t := by
    simp [B2, intervalIntegral.integral_const_mul]
  rw [hIntB, hIntB2] at hJB
  exact ⟨hJB, jetError_le_linear hell.le hL hkappa hkappa2 hx hcost⟩

/-- Specialize the actual-stage estimate to the configured stable error. -/
theorem configured_stage_jetBounds
    (D : ConstructedConfiguredSequenceWeighted.Data) {Cjet : ℝ} {n k : ℕ}
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : RichStageOutput J p front bound P0 kh khat M c C dlt)
    {m : ℝ → ℝ} {kappa kappa2 Mcap : ℝ}
    (hell : 0 < ell) (hL : 0 < L) (hT : 0 ≤ T)
    (hm : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hxiX : ∀ t x, |-(xiX t x)| ≤ kappa * m t)
    (hxiXX : ∀ t x, |-(xiXX t x)| ≤ kappa2 * m t)
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hcost : (∫ t in (0 : ℝ)..T, m t) ≤ rowDefect D (n + k))
    (hcap : rowDefect D (n + k) ≤ Mcap)
    (hCjet : jetLinearConst ell L kappa kappa2 Mcap ≤ Cjet) :
    JetBounds J S (eps D Cjet n k) := by
  obtain ⟨B, hB⟩ := stage_jetBounds J S hell hL hT hm hm0 hxiX hxiXX
    hkappa hkappa2 (hcost.trans hcap)
  apply jetBounds_mono B
  calc
    jetError ell L (kappa * (∫ t in (0 : ℝ)..T, m t))
        (kappa2 * (∫ t in (0 : ℝ)..T, m t)) ≤
        jetLinearConst ell L kappa kappa2 Mcap *
          (∫ t in (0 : ℝ)..T, m t) := hB
    _ ≤ jetLinearConst ell L kappa kappa2 Mcap * rowDefect D (n + k) :=
      mul_le_mul_of_nonneg_left hcost (by
        exact le_trans (by positivity) (le_max_left _ _))
    _ ≤ Cjet * rowDefect D (n + k) :=
      mul_le_mul_of_nonneg_right hCjet
        ((ConfiguredStableRowDefectProvider.provider D).nonnegative n k)
    _ = eps D Cjet n k := rfl

/-- A tail of every row supplies the complete near-identity distortion
budget used by the stable component induction. -/
theorem exists_tail_budget
    (D : ConstructedConfiguredSequenceWeighted.Data) {Cjet : ℝ}
    (hCjet : 0 ≤ Cjet) (n : ℕ) :
    ∃ N E,
      E = ∑' k, eps D Cjet n (N + k) ∧
      DistortionBudget
        (NearIdentityDistortionBudget.invLower (fun k => eps D Cjet n (N + k)))
        (NearIdentityDistortionBudget.upper (fun k => eps D Cjet n (N + k)))
        (fun k => eps D Cjet n (N + k)) (2 * E) E E := by
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 (eventually_eps_le_half D n))
  let e : ℕ → ℝ := fun k => eps D Cjet n (N + k)
  have he0 : ∀ k, 0 ≤ e k := fun k => eps_nonnegative D hCjet n (N + k)
  have heHalf : ∀ k, e k ≤ 1 / 2 := by
    intro k
    exact hN (N + k) (Nat.le_add_right N k)
  have hinj : Function.Injective (fun k : ℕ => N + k) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have hes : Summable e :=
    (summable_eps D n).comp_injective hinj
  refine ⟨N, ∑' k, e k, rfl, ?_⟩
  exact NearIdentityDistortionBudget.budget he0 heHalf hes le_rfl

end ConfiguredGaugeJetDistortion
