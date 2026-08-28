import UnitTangentIterates.ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial
import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineAncestryExtension

/-! # Endpoints for normalized nonaffine chosen ancestries -/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeNonaffineAncestryExtension
  ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  VariableArclengthScaledJacobiTransition

variable {MA NA Etotal Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : Output RJ Etotal Dtarget}

theorem markedPhysicalComponents_nonnegative
    {J : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {eta : ℝ → ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ J t u)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t) :
    (markedPhysicalComponents J P eta).Nonnegative := by
  refine
    { w := ?_
      s0 := by simpa [markedPhysicalComponents] using S_nonneg 0 eta
      s1 := by
        simpa [markedPhysicalComponents] using
          (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
            hP eta).s1
      s2 := by
        simpa [markedPhysicalComponents] using
          (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
            hP eta).s2 }
  unfold markedPhysicalComponents jacobianPhysicalW
  exact intervalIntegral.integral_nonneg zero_le_one fun t ht =>
    intervalIntegral.integral_nonneg zero_le_one fun u hu =>
      mul_nonneg (hJ t ht u hu) (abs_nonneg _)

theorem markedPhysicalComponents_nonnegative_of_sourceJets
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax eps : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (J : SourceNormalizedJetBounds A eps) (heps : eps ≤ 1 / 4) :
    (markedPhysicalComponents A.phi1 A.P Gamma.eta).Nonnegative := by
  apply markedPhysicalComponents_nonnegative
  · intro t ht u _
    exact le_trans (by
      have hp := A.period_pos t
      have : 0 < (1 - eps) * A.P t := mul_pos (by linarith) hp
      exact this.le) (J.lower t ht u)
  · exact fun t _ => (A.period_pos t).le

/-- Normalized source jets bounded by one quarter give the integrated base
Jacobian comparison.  Integrability is retained as a regularity sidecar, not
as a quantitative callback. -/
theorem jacobianPhysicalW_le_two_physicalW_of_sourceJets
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax eps : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (J : SourceNormalizedJetBounds A eps) (heps : eps ≤ 1 / 4)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    (heta : ∀ t, Continuous (Gamma.eta t))
    (hjac : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1,
        A.phi1 t u * |Gamma.eta t u|) volume 0 1) :
    jacobianPhysicalW A.phi1 Gamma.eta ≤ 2 * physicalW A.P Gamma.eta := by
  have hphys : IntervalIntegrable
      (fun t => A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1 := by
    simpa [mul_comm] using F.w.mul_continuousOn
      A.period_contDiff.continuous.continuousOn
  unfold jacobianPhysicalW physicalW
  calc
    (∫ t in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|) ≤
        ∫ t in (0 : ℝ)..1,
          2 * (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
      apply intervalIntegral.integral_mono_on zero_le_one hjac
        (hphys.const_mul 2)
      intro t ht
      rw [← mul_assoc]
      rw [← intervalIntegral.integral_const_mul]
      have hjinner : IntervalIntegrable
          (fun u => A.phi1 t u * |Gamma.eta t u|) volume 0 1 :=
        ((A.phi1_continuous t).mul (heta t).abs).intervalIntegrable 0 1
      have hpinner : IntervalIntegrable
          (fun u => (2 * A.P t) * |Gamma.eta t u|) volume 0 1 :=
        (continuous_const.mul (heta t).abs).intervalIntegrable 0 1
      apply intervalIntegral.integral_mono_on zero_le_one
        hjinner hpinner
      intro u _
      have hu := J.upper t ht u
      have habs := abs_nonneg (Gamma.eta t u)
      have hP := (A.period_pos t).le
      have hcoef : A.phi1 t u ≤ 2 * A.P t := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoef habs
    _ = 2 * (∫ t in (0 : ℝ)..1,
        A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
      rw [intervalIntegral.integral_const_mul]

/-- The normalized chosen lower jet gives the reverse terminal `W`
comparison with factor two. -/
theorem physicalW_le_two_jacobianPhysicalW_of_chosenJets
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax eps : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (J : NormalizedJetBounds W eps) (heps : eps ≤ 1 / 2)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable W.Delta.eta)
    (heta : ∀ t, Continuous (W.Delta.eta t))
    (hjac : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1,
        W.phi1 t u * |W.Delta.eta t u|) volume 0 1) :
    physicalW (rearPeriod A) W.Delta.eta ≤
      2 * jacobianPhysicalW W.phi1 W.Delta.eta := by
  have hRc : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t => (E.frame.period_deriv t).differentiableAt
  have hphys : IntervalIntegrable
      (fun t => rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |W.Delta.eta t u|) volume 0 1 := by
    simpa [mul_comm] using F.w.mul_continuousOn hRc.continuousOn
  unfold jacobianPhysicalW physicalW
  calc
    (∫ t in (0 : ℝ)..1, rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |W.Delta.eta t u|) ≤
        ∫ t in (0 : ℝ)..1, 2 *
          (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) := by
      apply intervalIntegral.integral_mono_on zero_le_one hphys
        (hjac.const_mul 2)
      intro t ht
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul]
      have hpinner : IntervalIntegrable
          (fun u => rearPeriod A t * |W.Delta.eta t u|) volume 0 1 :=
        ((show Continuous (fun _ : ℝ => rearPeriod A t) from continuous_const).mul
          (heta t).abs).intervalIntegrable 0 1
      have hjinner : IntervalIntegrable
          (fun u => 2 * (W.phi1 t u * |W.Delta.eta t u|)) volume 0 1 :=
        ((show Continuous (fun _ : ℝ => (2 : ℝ)) from continuous_const).mul
          ((W.phi1_continuous t).mul (heta t).abs)).intervalIntegrable 0 1
      apply intervalIntegral.integral_mono_on zero_le_one
        hpinner hjinner
      intro u _
      have hlow := (abs_le.mp (J.dpsi t ht u)).1
      have hR : 0 < rearPeriod A t := A.rear_period_pos t
      have hj : (1 - eps) * rearPeriod A t ≤ W.phi1 t u := by
        apply (le_div_iff₀ hR).1
        simpa [normalizedPsi1, sub_mul] using hlow
      have hu : rearPeriod A t ≤ 2 * W.phi1 t u := by
        nlinarith
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hu (abs_nonneg (W.Delta.eta t u))
    _ = 2 * (∫ t in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) := by
      rw [intervalIntegral.integral_const_mul]

/-- At the base, the three spatial channels of the normalized marked node are
exactly the fully physical channels.  Only the Jacobian `W` channel pays the
fixed near-identity factor two. -/
theorem marked_le_two_fullyPhysical
    {J : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {eta : ℝ → ℝ → ℝ}
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    (hw : jacobianPhysicalW J eta ≤ 2 * physicalW P eta) :
    let U := markedPhysicalComponents J P eta
    let V := scaleAll 2
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents P eta)
    U.w ≤ V.w ∧ U.s0 ≤ V.s0 ∧ U.s1 ≤ V.s1 ∧ U.s2 ≤ V.s2 := by
  let X :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents P eta
  have hX : X.Nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
      hP eta
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [markedPhysicalComponents, scaleAll,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
      using hw
  · change S 0 eta ≤ 2 * S 0 eta
    linarith [S_nonneg 0 eta]
  · change spatialS1 P eta ≤ 2 * spatialS1 P eta
    have hs1 : 0 ≤ spatialS1 P eta := by
      simpa [X,
        FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
        using hX.s1
    linarith
  · change spatialS2 P eta ≤ 2 * spatialS2 P eta
    have hs2 : 0 ≤ spatialS2 P eta := by
      simpa [X,
        FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
        using hX.s2
    linarith

/-- Combine the normalized base comparison with the configured physical base
estimate.  This is the exact initial bound used by a nonaffine ancestry. -/
theorem configured_base_le_two_edgePhysicalDefect
    {MA NA K0 K1 K2 : ℝ}
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ)
    (hw :
      let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
        (K0 := K0) (K1 := K1) (K2 := K2)
      let A := B.source n
      jacobianPhysicalW A.phi1
          (B.column.step.richStage (n + 1)).stage.increment.eta ≤
        2 * physicalW A.P
          (B.column.step.richStage (n + 1)).stage.increment.eta) :
    let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
      (K0 := K0) (K1 := K1) (K2 := K2)
    let A := B.source n
    let V := markedPhysicalComponents A.phi1 A.P
      (B.column.step.richStage (n + 1)).stage.increment.eta
    V.w ≤ 2 * ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (n + 1) ∧
      V.s0 ≤ 2 * ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (n + 1) ∧
      V.s1 ≤ 2 * ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (n + 1) ∧
      V.s2 ≤ 2 * ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (n + 1) := by
  dsimp only at hw ⊢
  let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
    (K0 := K0) (K1 := K1) (K2 := K2)
  let A := B.source n
  let eta := (B.column.step.richStage (n + 1)).stage.increment.eta
  have hmarked := marked_le_two_fullyPhysical
    (J := A.phi1) (P := A.P) (eta := eta)
    (fun t _ => (A.period_pos t).le) hw
  have hbase :=
    ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial.base_fullyPhysical_components_le_edgePhysicalDefect
      (K0 := K0) (K1 := K1) (K2 := K2) J n
  dsimp only at hmarked hbase
  exact ⟨hmarked.1.trans (mul_le_mul_of_nonneg_left hbase.1 (by norm_num)),
    hmarked.2.1.trans (mul_le_mul_of_nonneg_left hbase.2.1 (by norm_num)),
    hmarked.2.2.1.trans
      (mul_le_mul_of_nonneg_left hbase.2.2.1 (by norm_num)),
    hmarked.2.2.2.trans
      (mul_le_mul_of_nonneg_left hbase.2.2.2 (by norm_num))⟩

/-- The canonical nonaffine base row, with the only marking loss isolated in
`hw`, initializes an ancestry at defect `2 * edgePhysicalDefect`. -/
def configuredBaseAncestry
    (O : Output RJ Etotal Dtarget)
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ)
    (eps : ℝ)
    (jets :
      let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
        (K0 := K0) (K1 := K1) (K2 := K2)
      let A := B.source n
      SourceNormalizedJetBounds A eps)
    (heps : eps ≤ 1 / 4)
    (F :
      let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
        (K0 := K0) (K1 := K1) (K2 := K2)
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
        (B.column.step.richStage (n + 1)).stage.increment.eta)
    (heta :
      let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
        (K0 := K0) (K1 := K1) (K2 := K2)
      ∀ t, Continuous ((B.column.step.richStage (n + 1)).stage.increment.eta t))
    (hjac :
      let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
        (K0 := K0) (K1 := K1) (K2 := K2)
      let A := B.source n
      IntervalIntegrable (fun t => ∫ u in (0 : ℝ)..1,
        A.phi1 t u * |(B.column.step.richStage (n + 1)).stage.increment.eta t u|)
        volume 0 1) :
    let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
      (K0 := K0) (K1 := K1) (K2 := K2)
    Ancestry O (B.column.step.richStage (n + 1)).stage.increment 0
      (2 * ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
        (n + 1)) := by
  dsimp only at jets F heta hjac ⊢
  let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
    (K0 := K0) (K1 := K1) (K2 := K2)
  let A := B.source n
  let eta := (B.column.step.richStage (n + 1)).stage.increment.eta
  let V := markedPhysicalComponents A.phi1 A.P eta
  have hV : V.Nonnegative :=
    markedPhysicalComponents_nonnegative_of_sourceJets jets heps
  have hw := jacobianPhysicalW_le_two_physicalW_of_sourceJets
    jets heps F heta hjac
  have hinitial := configured_base_le_two_edgePhysicalDefect
    (K0 := K0) (K1 := K1) (K2 := K2) J n hw
  exact
    { V := fun _ => V
      baseJ := A.phi1
      baseP := A.P
      baseEta := eta
      base_eq := rfl
      d_nonnegative := mul_nonneg (by norm_num)
        (ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect_nonnegative
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (n + 1))
      components_nonnegative := fun _ _ => hV
      initial_le := hinitial
      links := by intro j hj; omega }

/-- A normalized ancestry whose final node is identified with the current
recosted path. -/
structure ConcreteAncestry
    {p q : Data} (Gamma : NormalPath p q) (depth : ℕ) (edgeDefect : ℝ) where
  ancestry : Ancestry O Gamma depth (2 * edgeDefect)
  terminalJ : ℝ → ℝ → ℝ
  terminalP : ℝ → ℝ
  terminal_eq : ancestry.V depth =
    markedPhysicalComponents terminalJ terminalP Gamma.eta

namespace ConcreteAncestry

variable {p q p' q' : Data} {Gamma : NormalPath p q}
  {Gamma' : NormalPath p' q'} {depth : ℕ} {edgeDefect : ℝ}

/-- Append a normalized nonaffine link and install its recosted target as the
new concrete endpoint. -/
def snoc
    (H : ConcreteAncestry (O := O) Gamma depth edgeDefect)
    (J : ℝ → ℝ → ℝ) (P : ℝ → ℝ)
    (htarget : (markedPhysicalComponents J P Gamma'.eta).Nonnegative)
    (L : NonaffineChosenLink O
      (extendV H.ancestry (markedPhysicalComponents J P Gamma'.eta)) depth) :
    ConcreteAncestry (O := O) Gamma' (depth + 1) edgeDefect where
  ancestry := Ancestry.snoc H.ancestry
    (markedPhysicalComponents J P Gamma'.eta) htarget L
  terminalJ := J
  terminalP := P
  terminal_eq := extendV_succ H.ancestry _

/-- The concrete endpoint converts to a split history with exact initial
defect `L² * (2 * edgeDefect)`, i.e. `2L² * edgeDefect`. -/
def toScaledSplitHistory
    (H : ConcreteAncestry (O := O) Gamma depth edgeDefect)
    (hE : Etotal ≤ 1 / 8) (L : ℝ)
    (terminal_le :
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s2) :
    ConfiguredRecursiveEdgeActualPhysicalSplitHistory.SplitHistory Gamma
      (fun j => scaleAll (L ^ 2) (H.ancestry.V j)) O.major depth Etotal
      configuredC0 configuredC1 configuredC2
      (L ^ 2 * (2 * edgeDefect)) :=
  Ancestry.toScaledSplitHistory O H.ancestry hE L terminal_le

end ConcreteAncestry

/-- A normalized chosen first jet bounded by one half and a rear-period floor
give the pointwise inverse-Jacobian factor two used at the terminal row. -/
theorem rearPeriod_le_two_chosen_phi1
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax eps : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (H : NormalizedJetBounds W eps) (heps : eps ≤ 1 / 2) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
      rearPeriod A t ≤ 2 * W.phi1 t u := by
  intro t ht u
  have hlow := (abs_le.mp (H.dpsi t ht u)).1
  have hR : 0 < rearPeriod A t := A.rear_period_pos t
  have hj : (1 - eps) * rearPeriod A t ≤ W.phi1 t u := by
    apply (le_div_iff₀ hR).1
    simpa [normalizedPsi1, sub_mul] using hlow
  nlinarith

/-- Convert the final normalized marked node to the unweighted terminal row.
The period powers cost `L²`, and the chosen inverse Jacobian costs at most two;
the single hypothesis `2 ≤ L²` absorbs both. -/
theorem terminal_le_scaleAll_marked
    {J : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {eta : ℝ → ℝ → ℝ} {L : ℝ}
    (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ P t)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, P t ≤ L)
    (hw : physicalW P eta ≤ 2 * jacobianPhysicalW J eta)
    (hW : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t => P t * ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (eta t))) volume 0 1)
    (hS1P : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (eta t)) / P t) volume 0 1)
    (hS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (eta t))) volume 0 1)
    (hS2P : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (eta t)) / P t ^ 2) volume 0 1) :
    let U := ArclengthScaledJacobiTransition.physicalComponents 1 eta
    let V := scaleAll (L ^ 2) (markedPhysicalComponents J P eta)
    U.w ≤ V.w ∧ U.s0 ≤ V.s0 ∧ U.s1 ≤ V.s1 ∧ U.s2 ≤ V.s2 := by
  have hsp := terminal_le_scaleSpatial hP1 hPL hW hPW hS1 hS1P hS2 hS2P
  have hmarkedW : 0 ≤ jacobianPhysicalW J eta := by
    have hpw : 0 ≤ physicalW P eta :=
      physicalW_nonnegative (fun t ht => (zero_le_one.trans (hP1 t ht))) eta
    nlinarith
  have h1sq : 1 ≤ L ^ 2 := le_trans (by norm_num) hL2
  have hLsq : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  dsimp only at hsp ⊢
  refine ⟨hsp.1.trans ?_, hsp.2.1.trans ?_,
    hsp.2.2.1.trans ?_, hsp.2.2.2⟩
  · change physicalW P eta ≤ L ^ 2 * jacobianPhysicalW J eta
    exact hw.trans (mul_le_mul_of_nonneg_right hL2 hmarkedW)
  · change S 0 eta ≤ L ^ 2 * S 0 eta
    simpa using mul_le_mul_of_nonneg_right h1sq (S_nonneg 0 eta)
  · change L * spatialS1 P eta ≤ L ^ 2 * spatialS1 P eta
    exact mul_le_mul_of_nonneg_right hLsq
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
        (fun t ht => (zero_le_one.trans (hP1 t ht))) eta).s1

namespace ConcreteAncestry

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax eps edgeDefect : ℝ}
  {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
    Gamma P0 kh khat Qmax}
  {E : Applied Gamma A} {depth : ℕ}

/-- Fully quantitative-callback-free terminal closure for an actual chosen
path.  Only regularity/integrability sidecars and the exact endpoint field
identities remain. -/
def toScaledSplitHistoryOfChosen
    (W : ChosenPath Gamma A E.Phi a b)
    (H : ConcreteAncestry (O := O) W.Delta depth edgeDefect)
    (hJ : H.terminalJ = W.phi1)
    (hP : H.terminalP = rearPeriod A)
    (jets : NormalizedJetBounds W eps) (heps : eps ≤ 1 / 2)
    (hEtotal : Etotal ≤ 1 / 8) (L : ℝ)
    (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ rearPeriod A t)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, rearPeriod A t ≤ L)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      W.Delta.eta)
    (heta : ∀ t, Continuous (W.Delta.eta t))
    (hjac : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1,
        W.phi1 t u * |W.Delta.eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t => rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |W.Delta.eta t u|) volume 0 1)
    (hS1P : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (W.Delta.eta t)) /
        rearPeriod A t) volume 0 1)
    (hS2P : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (W.Delta.eta t)) /
        rearPeriod A t ^ 2) volume 0 1) :
    ConfiguredRecursiveEdgeActualPhysicalSplitHistory.SplitHistory
      W.Delta (fun j => scaleAll (L ^ 2) (H.ancestry.V j))
      O.major depth Etotal configuredC0 configuredC1 configuredC2
      (L ^ 2 * (2 * edgeDefect)) := by
  apply H.toScaledSplitHistory hEtotal L
  rw [H.terminal_eq, hJ, hP]
  apply terminal_le_scaleAll_marked hL hL2 hP1 hPL
  · exact physicalW_le_two_jacobianPhysicalW_of_chosenJets
      W jets heps F heta hjac
  · exact F.w
  · exact hPW
  · exact F.s1
  · exact hS1P
  · exact F.s2
  · exact hS2P

end ConcreteAncestry

end ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
