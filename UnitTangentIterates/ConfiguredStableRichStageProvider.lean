import UnitTangentIterates.ConfiguredRichBaseStageProvider
import UnitTangentIterates.ConfiguredStableVariableTerminalCapstone
import UnitTangentIterates.AnchoredJacobiStableTransition
import UnitTangentIterates.CanonicalNormalPathRecost

/-!
# Stable configured rich-stage providers

This file bridges the paper's componentwise Jacobi invariant to the recursive
provider API.  The only cost-specific analytic datum retained is the honest
comparison of the chosen path cost with the sum of its four paper
functionals.  Once each component has a depth-uniform bound, the recursive
error is `Cstable * rowDefect D (n + k)` with no multiplicative propagation.
-/

noncomputable section

open Function Set MarkedSpace PathMetric MarkedTopology
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace ConfiguredStableRichStageProvider

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
open ConfiguredApproximateDefectPathRowwise
open GaugeRearFamilyVariableTerminal
open AnchoredJacobiStableTransition

/-! ## Componentwise cost conversion -/

/-- A path whose actual stored cost is controlled by the four functionals and
whose four functionals have the same scalar bound.  The first field is kept
explicit: it is not a consequence of the bare `NormalPath` structure, whose
cost density may be any common majorant. -/
structure ComponentCostCertificate
    {p q : Data} (Gamma : NormalPath p q) (C d : ℝ) : Prop where
  cost_le_components : cost Gamma ≤
    (components Gamma.eta).w + (components Gamma.eta).s0 +
      (components Gamma.eta).s1 + (components Gamma.eta).s2
  w_le : (components Gamma.eta).w ≤ C * d
  s0_le : (components Gamma.eta).s0 ≤ C * d
  s1_le : (components Gamma.eta).s1 ≤ C * d
  s2_le : (components Gamma.eta).s2 ≤ C * d

theorem ComponentCostCertificate.cost_le_four_mul
    {p q : Data} {Gamma : NormalPath p q} {C d : ℝ}
    (H : ComponentCostCertificate Gamma C d) :
    cost Gamma ≤ (4 * C) * d := by
  calc
    cost Gamma ≤ (components Gamma.eta).w +
        (components Gamma.eta).s0 + (components Gamma.eta).s1 +
        (components Gamma.eta).s2 := H.cost_le_components
    _ ≤ C * d + C * d + C * d + C * d :=
      add_le_add (add_le_add (add_le_add H.w_le H.s0_le) H.s1_le) H.s2_le
    _ = (4 * C) * d := by ring

/-- Construct the component certificate directly from the summable-distortion
transition theorem. -/
def ComponentCostCertificate.of_distortionBudget
    {p q : Data} (Gamma : NormalPath p q)
    {V : ℕ → Components} {a MA NA : ℕ → ℝ}
    {Aw AM AN C0 C1 C2 d : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ k, (V k).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ k, Transition (V k) (V (k + 1))
      (a k) (MA k) (NA k) C0 C1 C2)
    (k : ℕ) (hcomponents : components Gamma.eta = V k)
    (hcost : cost Gamma ≤
      (components Gamma.eta).w + (components Gamma.eta).s0 +
        (components Gamma.eta).s1 + (components Gamma.eta).s2) :
    ComponentCostCertificate Gamma (stableConst Aw AM AN C0 C1 C2) d := by
  have H := depth_uniform_components B hC0 hC1 hC2 hd hV hinit hstep k
  rw [← hcomponents] at H
  exact ⟨hcost, H.1, H.2.1, H.2.2.1, H.2.2.2⟩

/-- One row-independent distortion total and one row-independent set of
Jacobi coefficients.  Keeping this object outside the stage quantifiers is
the crucial uniformity required by the triangular limit. -/
structure UniformTransitionBudget (a MA NA : ℕ → ℝ) where
  Aw : ℝ
  AM : ℝ
  AN : ℝ
  C0 : ℝ
  C1 : ℝ
  C2 : ℝ
  distortion : DistortionBudget a MA NA Aw AM AN
  C0_nonnegative : 0 ≤ C0
  C1_nonnegative : 0 ≤ C1
  C2_nonnegative : 0 ≤ C2

def UniformTransitionBudget.componentConst {a MA NA : ℕ → ℝ}
    (B : UniformTransitionBudget a MA NA) : ℝ :=
  stableConst B.Aw B.AM B.AN B.C0 B.C1 B.C2

def UniformTransitionBudget.scale {a MA NA : ℕ → ℝ}
    (B : UniformTransitionBudget a MA NA) : ℝ :=
  4 * B.componentConst

/-- The component certificate obtained from a single budget shared by all
depths. -/
def ComponentCostCertificate.of_uniformBudget
    {p q : Data} (Gamma : NormalPath p q)
    {V : ℕ → Components} {a MA NA : ℕ → ℝ}
    (B : UniformTransitionBudget a MA NA) {d : ℝ} (hd : 0 ≤ d)
    (hV : ∀ k, (V k).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ k, Transition (V k) (V (k + 1))
      (a k) (MA k) (NA k) B.C0 B.C1 B.C2)
    (k : ℕ) (hcomponents : components Gamma.eta = V k)
    (hcost : cost Gamma ≤
      (components Gamma.eta).w + (components Gamma.eta).s0 +
        (components Gamma.eta).s1 + (components Gamma.eta).s2) :
    ComponentCostCertificate Gamma B.componentConst d :=
  ComponentCostCertificate.of_distortionBudget Gamma B.distortion
    B.C0_nonnegative B.C1_nonnegative B.C2_nonnegative hd hV hinit hstep
    k hcomponents hcost

/-- Canonical recosting removes the arbitrary-majorant ambiguity completely:
the cost comparison is a theorem, and only the four component estimates remain
from the gauge analysis. -/
def ComponentCostCertificate.of_recost
    {p q : Data} (Gamma : NormalPath p q)
    (hT : Gamma.T = 1) (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2))
    {C d : ℝ}
    (hw : (components Gamma.eta).w ≤ C * d)
    (hs0 : (components Gamma.eta).s0 ≤ C * d)
    (hs1 : (components Gamma.eta).s1 ≤ C * d)
    (hs2 : (components Gamma.eta).s2 ≤ C * d) :
    ComponentCostCertificate
      (CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2) C d := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using CanonicalNormalPathRecost.cost_recost_le_markedComponents
      Gamma hT hC2 heta heta1 heta2
  · simpa using hw
  · simpa using hs0
  · simpa using hs1
  · simpa using hs2

/-! ## Base column -/

/-- The stable constant used by `depth_uniform_components` is at least one. -/
theorem one_le_stableConst (Aw AM AN C0 C1 C2 : ℝ) :
    1 ≤ stableConst Aw AM AN C0 C1 C2 := by
  unfold stableConst s0Const
  exact (le_max_left 1 _).trans
    ((le_max_left _ _).trans (le_max_right _ _))

/-- Rebound the canonical configured base stage by one stable scalar and by
the actual common `P1/G1/Cg` ceilings. -/
def baseProvider
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cstable c dlt : ℝ} {Q : ℕ → Data}
    (hCstable : 1 ≤ Cstable)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (R : ConfiguredRichBaseStageProvider.PhysicalRearNormalization D Q)
    (C P1 G1 Cg : ℕ → ℝ)
    (hP1 : ∀ n, rowP1 D n ≤ P1 n)
    (hG1 : ∀ n, rowG1 D n ≤ G1 n)
    (hCg : ∀ n, rowCg D n ≤ Cg n)
    (hkstar : 0 ≤ D.kstar) :
    BaseStageProvider Q
      (ConfiguredScaledStableRowDefectProvider.error D Cstable)
      (rowP0 D) P1 (fun _ => D.kstar) G1 Cg C c dlt := by
  let B := Classical.choice
    (ConfiguredRichBaseStageProvider.provider_mono
      (K := 1) (c := c) (dlt := dlt) D hQ R C P1 G1 Cg
      hP1 hG1 hCg hkstar).base
  refine ⟨⟨{
    next := B.next
    richStage := fun n => ?_ }⟩⟩
  let S := B.richStage n
  have hd : 0 ≤ rowDefect D n :=
    (ConfiguredStableRowDefectProvider.provider D).nonnegative n 0
  have hcost : cost S.stage.increment ≤
      ConfiguredScaledStableRowDefectProvider.error D Cstable n 0 := by
    calc
      cost S.stage.increment ≤ ConfiguredRowDefectProvider.error D 1 n 0 :=
        S.stage.increment_cost
      _ = rowDefect D n := by
        simp [ConfiguredRowDefectProvider.error,
          PathMetric.WeightedRecursiveDefect.pullbackError]
      _ ≤ Cstable * rowDefect D n := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hCstable hd
      _ = ConfiguredScaledStableRowDefectProvider.error D Cstable n 0 := by
        simp [ConfiguredScaledStableRowDefectProvider.error]
  exact
    { stage :=
        { increment := S.stage.increment
          increment_geometry := S.stage.increment_geometry
          increment_cost := hcost
          rear_curve_deriv := S.stage.rear_curve_deriv
          rear_vel_deriv := S.stage.rear_vel_deriv
          rear_periodic := S.stage.rear_periodic
          rear_curvature_nonnegative := S.stage.rear_curvature_nonnegative
          range_edge := S.stage.range_edge
          rear_harnack := S.stage.rear_harnack }
      terminalBase := S.terminalBase
      lambda := S.lambda
      Lambda := S.Lambda
      marking := S.marking }

/-! ## Mapped columns -/

/-- One actual stable selected-rear image.  The geometric bounds use the
common recursive ceilings directly.  The component certificate is the only
place where the paper's stable transition enters this adapter. -/
structure StableGaugeImage
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Ccomponent Cstable c dlt : ℝ}
    (P1 G1 Cg C : ℕ → ℝ)
    {Q current : ℕ → Data} {k : ℕ}
    (S : ColumnStep Q current
      (ConfiguredScaledStableRowDefectProvider.error D Cstable) k
      (rowP0 D) P1 (fun _ => D.kstar) G1 Cg C c dlt)
    (n : ℕ) where
  rear : Data
  terminalBase : Data
  increment : NormalPath (S.next n) rear
  increment_geometry : IsVariableSpeedNormalPath
    (rowP0 D n) (P1 n) D.kstar (G1 n) (Cg n) increment
  component_cost : ComponentCostCertificate increment Ccomponent
    (rowDefect D (n + (k + 1)))
  lambda : ℝ
  Lambda : ℝ
  marking :
    NormalizedTerminalMarkingComposition.NormalizedC2Marking
      terminalBase rear lambda Lambda
  terminal : RawTerminalResidual (S.next (n + 1)) rear

/-- Local analytic provider consumed by the stable recursive map adapter. -/
structure StableGaugeProvider
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Ccomponent Cstable c dlt : ℝ}
    (P1 G1 Cg C : ℕ → ℝ) where
  image : ∀ {Q current k}
    (S : ColumnStep Q current
      (ConfiguredScaledStableRowDefectProvider.error D Cstable) k
      (rowP0 D) P1 (fun _ => D.kstar) G1 Cg C c dlt) n,
    Nonempty (StableGaugeImage D
      (Ccomponent := Ccomponent) (Cstable := Cstable)
      (c := c) (dlt := dlt) P1 G1 Cg C S n)

/-- Assemble every mapped column from componentwise stable images. -/
def mapProvider
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Ccomponent Cstable c dlt : ℝ} {Q : ℕ → Data}
    (P1 G1 Cg C : ℕ → ℝ)
    (hscale : 4 * Ccomponent ≤ Cstable)
    (G : StableGaugeProvider
      (D := D) (Ccomponent := Ccomponent) (Cstable := Cstable)
      (c := c) (dlt := dlt) P1 G1 Cg C) :
    MapStageProvider Q
      (ConfiguredScaledStableRowDefectProvider.error D Cstable)
      (rowP0 D) P1 (fun _ => D.kstar) G1 Cg C c dlt := by
  refine { map := ?_ }
  intro k current S
  let I : ∀ n, StableGaugeImage D
      (Ccomponent := Ccomponent) (Cstable := Cstable)
      (c := c) (dlt := dlt) P1 G1 Cg C S n := fun n =>
    Classical.choice (G.image S n)
  refine ⟨{
    next := fun n => (I n).rear
    richStage := fun n => ?_ }⟩
  let W := I n
  have hd : 0 ≤ rowDefect D (n + (k + 1)) :=
    (ConfiguredStableRowDefectProvider.provider D).nonnegative n (k + 1)
  have hcost : cost W.increment ≤
      ConfiguredScaledStableRowDefectProvider.error D Cstable n (k + 1) := by
    calc
      cost W.increment ≤ (4 * Ccomponent) * rowDefect D (n + (k + 1)) :=
        W.component_cost.cost_le_four_mul
      _ ≤ Cstable * rowDefect D (n + (k + 1)) :=
        mul_le_mul_of_nonneg_right hscale hd
      _ = ConfiguredScaledStableRowDefectProvider.error D Cstable n (k + 1) :=
        rfl
  exact
    { stage :=
        { increment := W.increment
          increment_geometry := W.increment_geometry
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

/-- The canonical choice from the depth-uniform transition constant. -/
def canonicalStableScale (Aw AM AN C0 C1 C2 : ℝ) : ℝ :=
  4 * stableConst Aw AM AN C0 C1 C2

theorem canonicalStableScale_nonnegative (Aw AM AN C0 C1 C2 : ℝ) :
    0 ≤ canonicalStableScale Aw AM AN C0 C1 C2 := by
  unfold canonicalStableScale
  exact mul_nonneg (by norm_num)
    (zero_le_one.trans (one_le_stableConst Aw AM AN C0 C1 C2))

end ConfiguredStableRichStageProvider
