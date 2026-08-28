import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
import UnitTangentIterates.ArclengthScaledJacobiTransition

/-! # Converting fully physical terminal components to unweighted components -/

noncomputable section

open Set MeasureTheory MarkedTopology

namespace FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  VariableArclengthScaledJacobiTransition

/-- Uniformly scale every component by the same scalar. -/
def scaleAll (c : ℝ) (V : Components) : Components where
  w := c * V.w
  s0 := c * V.s0
  s1 := c * V.s1
  s2 := c * V.s2

theorem scaleAll_nonnegative {c : ℝ} {V : Components}
    (hc : 0 ≤ c) (hV : V.Nonnegative) : (scaleAll c V).Nonnegative where
  w := mul_nonneg hc hV.w
  s0 := mul_nonneg hc hV.s0
  s1 := mul_nonneg hc hV.s1
  s2 := mul_nonneg hc hV.s2

/-- Uniform scaling is exactly homogeneous for all four transition
inequalities, so none of the junction constants changes. -/
theorem transition_scaleAll
    {x y : Components} {a MA NA C0 C1 C2 c : ℝ}
    (H : Transition x y a MA NA C0 C1 C2) (hc : 0 ≤ c) :
    Transition (scaleAll c x) (scaleAll c y) a MA NA C0 C1 C2 where
  w := by
    calc
      c * y.w ≤ c * (a * x.w) := mul_le_mul_of_nonneg_left H.w hc
      _ = a * (c * x.w) := by ring
  s0 := by
    calc
      c * y.s0 ≤ c * (C0 * x.w) := mul_le_mul_of_nonneg_left H.s0 hc
      _ = C0 * (c * x.w) := by ring
  s1 := by
    calc
      c * y.s1 ≤ c * (MA * C1 * (x.w + x.s0)) :=
        mul_le_mul_of_nonneg_left H.s1 hc
      _ = MA * C1 * (c * x.w + c * x.s0) := by ring
  s2 := by
    calc
      c * y.s2 ≤ c *
          (MA ^ 2 * C2 * (x.w + x.s0 + x.s1) +
            NA * C1 * (x.w + x.s0)) :=
        mul_le_mul_of_nonneg_left H.s2 hc
      _ = MA ^ 2 * C2 * (c * x.w + c * x.s0 + c * x.s1) +
          NA * C1 * (c * x.w + c * x.s0) := by ring

/-- Scale precisely the two spatial derivative channels. -/
def scaleSpatial (L : ℝ) (V : Components) : Components where
  w := V.w
  s0 := V.s0
  s1 := L * V.s1
  s2 := L ^ 2 * V.s2

theorem scaleSpatial_nonnegative {L : ℝ} {V : Components}
    (hL : 0 ≤ L) (hV : V.Nonnegative) : (scaleSpatial L V).Nonnegative where
  w := hV.w
  s0 := hV.s0
  s1 := mul_nonneg hL hV.s1
  s2 := mul_nonneg (sq_nonneg L) hV.s2

/-- Scaling the whole chain preserves its transition after multiplying both
spatial constants by `L²`. -/
theorem transition_scaleSpatial
    {x y : Components} {a MA NA C0 C1 C2 L : ℝ}
    (H : Transition x y a MA NA C0 C1 C2)
    (hx : x.Nonnegative) (hL : 1 ≤ L)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    Transition (scaleSpatial L x) (scaleSpatial L y)
      a MA NA C0 (L ^ 2 * C1) (L ^ 2 * C2) where
  w := H.w
  s0 := H.s0
  s1 := by
    have hsum : 0 ≤ x.w + x.s0 := add_nonneg hx.w hx.s0
    have hcoef : 0 ≤ MA * C1 * (x.w + x.s0) :=
      mul_nonneg (mul_nonneg hMA hC1) hsum
    calc
      L * y.s1 ≤ L * (MA * C1 * (x.w + x.s0)) :=
        mul_le_mul_of_nonneg_left H.s1 (zero_le_one.trans hL)
      _ ≤ L ^ 2 * (MA * C1 * (x.w + x.s0)) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (L - 1)]) hcoef
      _ = MA * (L ^ 2 * C1) *
          ((scaleSpatial L x).w + (scaleSpatial L x).s0) := by
        simp [scaleSpatial]
        ring
  s2 := by
    have hA : 0 ≤ MA ^ 2 * C2 := mul_nonneg (sq_nonneg MA) hC2
    have hB : 0 ≤ NA * C1 := mul_nonneg hNA hC1
    have hs1 : x.s1 ≤ L * x.s1 := by
      nlinarith [hx.s1]
    have hsum : x.w + x.s0 + x.s1 ≤ x.w + x.s0 + L * x.s1 := by
      linarith
    calc
      L ^ 2 * y.s2 ≤ L ^ 2 *
          (MA ^ 2 * C2 * (x.w + x.s0 + x.s1) +
            NA * C1 * (x.w + x.s0)) :=
        mul_le_mul_of_nonneg_left H.s2 (sq_nonneg L)
      _ = (MA ^ 2 * C2) * (L ^ 2 * (x.w + x.s0 + x.s1)) +
          (NA * C1) * (L ^ 2 * (x.w + x.s0)) := by ring
      _ ≤ (MA ^ 2 * C2) * (L ^ 2 * (x.w + x.s0 + L * x.s1)) +
          (NA * C1) * (L ^ 2 * (x.w + x.s0)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum (sq_nonneg L)) hA)
          le_rfl
      _ = MA ^ 2 * (L ^ 2 * C2) *
            ((scaleSpatial L x).w + (scaleSpatial L x).s0 +
              (scaleSpatial L x).s1) +
          NA * (L ^ 2 * C1) *
            ((scaleSpatial L x).w + (scaleSpatial L x).s0) := by
        simp [scaleSpatial]
        ring

/-- Exact period-power conversion at the terminal row. -/
theorem terminal_le_scaleSpatial
    {P : ℝ → ℝ} {eta : ℝ → ℝ → ℝ} {L : ℝ}
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ P t)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, P t ≤ L)
    (hW : IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hS1 : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (eta t))) volume 0 1)
    (hS1P : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (eta t)) / P t) volume 0 1)
    (hS2 : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (eta t))) volume 0 1)
    (hS2P : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (eta t)) / P t ^ 2) volume 0 1) :
    let U := ArclengthScaledJacobiTransition.physicalComponents 1 eta
    let V := scaleSpatial L
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents P eta)
    U.w ≤ V.w ∧ U.s0 ≤ V.s0 ∧ U.s1 ≤ V.s1 ∧ U.s2 ≤ V.s2 := by
  dsimp only
  refine ⟨?_, le_rfl, ?_, ?_⟩
  · simpa [ArclengthScaledJacobiTransition.physicalComponents,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents,
      one_mul] using W_le_physicalW hW hPW hP1
  · unfold ArclengthScaledJacobiTransition.physicalComponents scaleSpatial
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      spatialS1 S
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one hS1
      (hS1P.const_mul L) fun t ht => by
        have hp : 0 < P t := zero_lt_one.trans_le (hP1 t ht)
        have hz : 0 ≤ supNorm (iteratedDeriv 1 (eta t)) := supNorm_nonneg _
        calc
          supNorm (iteratedDeriv 1 (eta t)) =
              P t * (supNorm (iteratedDeriv 1 (eta t)) / P t) := by
            field_simp
          _ ≤ L * (supNorm (iteratedDeriv 1 (eta t)) / P t) :=
            mul_le_mul_of_nonneg_right (hPL t ht) (div_nonneg hz hp.le)
  · unfold ArclengthScaledJacobiTransition.physicalComponents scaleSpatial
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      spatialS2 S
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one hS2
      (hS2P.const_mul (L ^ 2)) fun t ht => by
        have hp : 0 < P t := zero_lt_one.trans_le (hP1 t ht)
        have hz : 0 ≤ supNorm (iteratedDeriv 2 (eta t)) := supNorm_nonneg _
        have hsq : P t ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ hp.le (hPL t ht) 2
        calc
          supNorm (iteratedDeriv 2 (eta t)) =
              P t ^ 2 * (supNorm (iteratedDeriv 2 (eta t)) / P t ^ 2) := by
            field_simp
          _ ≤ L ^ 2 *
              (supNorm (iteratedDeriv 2 (eta t)) / P t ^ 2) :=
            mul_le_mul_of_nonneg_right hsq
              (div_nonneg hz (sq_nonneg (P t)))

/-- Convert a fully physical terminal row to the unweighted terminal by
uniformly scaling the whole row by `L²`.  This is deliberately coarser than
`scaleSpatial`, but is exactly homogeneous along the entire transition
chain. -/
theorem terminal_le_scaleAll
    {P : ℝ → ℝ} {eta : ℝ → ℝ → ℝ} {L : ℝ}
    (hL : 1 ≤ L)
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ P t)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, P t ≤ L)
    (hW : IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hS1 : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (eta t))) volume 0 1)
    (hS1P : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (eta t)) / P t) volume 0 1)
    (hS2 : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (eta t))) volume 0 1)
    (hS2P : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (eta t)) / P t ^ 2) volume 0 1) :
    let U := ArclengthScaledJacobiTransition.physicalComponents 1 eta
    let V := scaleAll (L ^ 2)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents P eta)
    U.w ≤ V.w ∧ U.s0 ≤ V.s0 ∧ U.s1 ≤ V.s1 ∧ U.s2 ≤ V.s2 := by
  let V :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents P eta
  have hV : V.Nonnegative := physicalComponents_nonnegative
    (fun t ht => le_trans (by norm_num) (hP1 t ht)) eta
  have hsp := terminal_le_scaleSpatial hP1 hPL hW hPW hS1 hS1P hS2 hS2P
  have h1sq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hLsq : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  dsimp only at hsp ⊢
  change
    (ArclengthScaledJacobiTransition.physicalComponents 1 eta).w ≤
        (scaleAll (L ^ 2) V).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 eta).s0 ≤
        (scaleAll (L ^ 2) V).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 eta).s1 ≤
        (scaleAll (L ^ 2) V).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 eta).s2 ≤
        (scaleAll (L ^ 2) V).s2
  refine ⟨hsp.1.trans ?_, hsp.2.1.trans ?_, hsp.2.2.1.trans ?_, hsp.2.2.2⟩
  · simpa [scaleAll] using mul_le_mul_of_nonneg_right h1sq hV.w
  · simpa [scaleAll] using mul_le_mul_of_nonneg_right h1sq hV.s0
  · simpa [scaleAll, scaleSpatial] using
      mul_le_mul_of_nonneg_right hLsq hV.s1

end FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
