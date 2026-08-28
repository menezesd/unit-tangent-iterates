import UnitTangentIterates.ConfiguredRichBaseStageProvider
import UnitTangentIterates.NormalizedMarkingControlledJunction
import UnitTangentIterates.VariableSpeedReparamTransport
import UnitTangentIterates.PhysicalRearLimitKinematicClosure

/-!
# Configured mapped rich-stage provider

The gauge rear-family theorem produces a path with an affine initial marking.
The preceding rich stage supplies the actual nonaffine marking.  We compose
the two by the controlled fixed spatial junction, retain the physical terminal
base and its normalized marking, and obtain the weighted recursive cost with
the explicit amplification `15 * mapK kh`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace ConfiguredRichMapStageProvider

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  GaugeRearFamilyVariableTerminal
  NormalizedTerminalMarkingComposition
  NormalizedMarkingControlledJunction
  ConfiguredApproximateDefectPathRowwise

def mapP1 (D : ConstructedConfiguredSequenceWeighted.Data)
    (rawP1 : ℕ → ℝ) (MA : ℝ) (n : ℕ) : ℝ :=
  max (rowP1 D n) (rawP1 n * MA)

def mapG1 (D : ConstructedConfiguredSequenceWeighted.Data)
    (rawP1 rawG1 : ℕ → ℝ) (MA NA : ℝ) (n : ℕ) : ℝ :=
  max (rowG1 D n) (rawG1 n * MA ^ 2 + rawP1 n * NA)

def mapCg (D : ConstructedConfiguredSequenceWeighted.Data)
    (rawP1 rawCg : ℕ → ℝ) (MA NA : ℝ) (n : ℕ) : ℝ :=
  max (rowCg D n) (rawCg n * MA ^ 2 + D.kstar * rawP1 n * NA)

def K (kh mA MA NA : ℝ) : ℝ :=
  reparamCostConst mA MA NA * SelectedInverseApproximateMapPath.mapK kh

theorem K_nonneg {kh mA MA NA : ℝ} (hmA : 0 < mA)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ K kh mA MA NA :=
  mul_nonneg (reparamCostConst_nonneg hmA)
    (SelectedInverseApproximateMapPath.mapK_nonneg hkh0 hkh1)

theorem one_le_K {kh mA MA NA : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    1 ≤ K kh mA MA NA := by
  exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
    (mul_le_mul (one_le_reparamCostConst mA MA NA)
      (SelectedInverseApproximateMapPath.one_le_mapK hkh0 hkh1)
      zero_le_one (le_trans zero_le_one (one_le_reparamCostConst mA MA NA)))

/-- One affine-initial gauge image before its marking is anchored.  All
differential rear-family hypotheses are hidden behind the existing gauge
rear-family theorem; this package retains only its actual output and the
physical terminal certificate needed by the recursive scheme. -/
structure AffineGaugeImage
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh mA MA NA c dlt : ℝ}
    (rawP1 rawG1 rawCg C : ℕ → ℝ)
    {Q current : ℕ → Data} {k : ℕ}
    (S : ColumnStep Q current
      (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
      (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
      (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt)
    (n : ℕ) where
  affineRear : Data
  rear : Data
  terminalBase : Data
  physicalKinematics : PhysicalRearLimitKinematics kh terminalBase
    (S.richStage (n + 1)).terminalBase
  affinePath : NormalPath (S.richStage n).terminalBase affineRear
  affineC2 : C2NormalPathData affinePath
  affineGeometry : IsVariableSpeedNormalPath
    (rowP0 D n) (rawP1 n) D.kstar (rawG1 n) (rawCg n) affinePath
  affineCost : cost affinePath ≤
    SelectedInverseApproximateMapPath.mapK kh *
      cost (S.richStage (n + 1)).stage.increment
  finish : ∀ u,
    affinePath.X affinePath.T ((S.richStage n).marking.marking.psi u) =
      rear.1 u
  lambda : ℝ
  Lambda : ℝ
  marking : NormalizedC2Marking terminalBase rear lambda Lambda
  terminal : RawTerminalResidual (S.next (n + 1)) rear

/-- The remaining rear-family input is genuinely local: for a complete prior
column and a row it produces the affine gauge image.  In particular it does
not assume a mapped rich stage or its weighted bound. -/
structure AffineGaugeProvider
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh mA MA NA c dlt : ℝ}
    (rawP1 rawG1 rawCg C : ℕ → ℝ)
    (anchor : ∀ {Q current k}
      (S : ColumnStep Q current
        (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
        (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
        (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt) n,
      ControlledAnchoringBounds (S.richStage n).marking mA MA NA) where
  image : ∀ {Q current k}
    (S : ColumnStep Q current
      (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
      (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
      (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt) n,
    Nonempty (AffineGaugeImage D rawP1 rawG1 rawCg C S n)

/-- Assemble the actual mapped column.  The start is definitionally the prior
nonaffine endpoint, and the recursive error is exactly `K^(k+1)d(n+k+1)`. -/
def provider
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh mA MA NA c dlt : ℝ}
    {Q : ℕ → Data}
    (rawP1 rawG1 rawCg C : ℕ → ℝ)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hmA : 0 < mA)
    (hP0 : ∀ n, 0 < rowP0 D n)
    (hkstar : 0 ≤ D.kstar)
    (hP1 : ∀ n, 0 ≤ rawP1 n)
    (hG1 : ∀ n, 0 ≤ rawG1 n)
    (hCg : ∀ n, 0 ≤ rawCg n)
    (anchor : ∀ {Q current k}
      (S : ColumnStep Q current
        (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
        (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
        (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt) n,
      ControlledAnchoringBounds (S.richStage n).marking mA MA NA)
    (G : AffineGaugeProvider D rawP1 rawG1 rawCg C anchor) :
    MapStageProvider Q
      (ConfiguredRowDefectProvider.error D (K kh mA MA NA))
      (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
      (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt := by
  refine { map := ?_ }
  intro k current S
  let I : ∀ n, AffineGaugeImage D rawP1 rawG1 rawCg C S n := fun n =>
    Classical.choice (G.image S n)
  let next : ℕ → Data := fun n => (I n).rear
  refine ⟨{
    next := next
    richStage := fun n => ?_ }⟩
  let A := S.richStage n
  let W := I n
  have hstart : ∀ u,
      W.affinePath.X 0 (A.marking.marking.psi u) = (S.next n).1 u := by
    intro u
    rw [W.affinePath.start]
    exact (A.marking.marking.position u).symm
  let J := controlledJunction W.affinePath A.marking (anchor S n) hstart W.finish
  let Delta : NormalPath (S.next n) W.rear :=
    reparamAtJunction W.affinePath W.affineC2 J
  have hDelta0 : IsVariableSpeedNormalPath (rowP0 D n)
      (rawP1 n * MA) D.kstar
      (rawG1 n * MA ^ 2 + rawP1 n * NA)
      (rawCg n * MA ^ 2 + D.kstar * rawP1 n * NA) Delta := by
    simpa [Delta, J, controlledJunction] using
      PathMetric.isVariableSpeedNormalPath_reparamAtJunction
        W.affineC2 J W.affineGeometry (hP0 n) (hP1 n) hkstar
        (hG1 n) (hCg n) (anchor S n).M_nonneg (anchor S n).N_nonneg
  have hDelta : IsVariableSpeedNormalPath (rowP0 D n)
      (mapP1 D rawP1 MA n) D.kstar
      (mapG1 D rawP1 rawG1 MA NA n) (mapCg D rawP1 rawCg MA NA n) Delta :=
    IsVariableSpeedNormalPath.mono Delta hDelta0 hkstar
      (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
  have hcost : cost Delta ≤
      ConfiguredRowDefectProvider.error D (K kh mA MA NA) n (k + 1) := by
    rw [show cost Delta = reparamCostConst mA MA NA * cost W.affinePath by
      exact controlledJunction_cost W.affinePath W.affineC2 A.marking
        (anchor S n) hstart W.finish]
    calc
      reparamCostConst mA MA NA * cost W.affinePath ≤
          reparamCostConst mA MA NA *
            (SelectedInverseApproximateMapPath.mapK kh *
              cost (S.richStage (n + 1)).stage.increment) :=
        mul_le_mul_of_nonneg_left W.affineCost (reparamCostConst_nonneg hmA)
      _ = K kh mA MA NA * cost (S.richStage (n + 1)).stage.increment := by
        simp [K, mul_assoc]
      _ ≤ K kh mA MA NA * ConfiguredRowDefectProvider.error D (K kh mA MA NA) (n + 1) k :=
        mul_le_mul_of_nonneg_left
          (S.richStage (n + 1)).stage.increment_cost (K_nonneg hmA hkh0 hkh1)
      _ = ConfiguredRowDefectProvider.error D (K kh mA MA NA) n (k + 1) := by
        simp [ConfiguredRowDefectProvider.error,
          PathMetric.WeightedRecursiveDefect.pullbackError, pow_succ]
        ring
  exact
    { stage :=
        { increment := Delta
          increment_geometry := hDelta
          increment_cost := hcost
          rear_curve_deriv := W.terminal.rear_curve_deriv
          rear_vel_deriv := W.terminal.rear_vel_deriv
          rear_periodic := W.terminal.rear_periodic
          rear_curvature_nonnegative := W.terminal.rear_curvature_nonnegative
          range_edge := W.terminal.range_edge
          rear_harnack := W.terminal.rear_harnack }
      terminalBase := W.terminalBase
      lambda := W.lambda
      Lambda := W.Lambda
      marking := W.marking }

end ConfiguredRichMapStageProvider
