import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
import UnitTangentIterates.JacobiControlledJunctionComponents
import UnitTangentIterates.PhysicalArclengthJacobiTransition

/-!
# Configured transition data for marking-aware chosen rows

The marking-aware long theorem retains the spatial Jacobi ODE, but its
existential output currently forgets the four integrated density gains.  This
module isolates that exact erasure boundary.  Once those gains are retained
for the actual chosen path, the existing physical rescaling theorem constructs
the recursive component transition.  No additional endpoint alignment is
needed: the target is already `Output.chosen.Delta`.
-/

noncomputable section

open MarkedTopology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareConfiguredTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  GaugeMarkedDataOfRearFamily
  JacobiControlledJunctionComponents
  NormalPathC2IncrementVariableSpeed
  PathMetricJacobi
  PhysicalArclengthJacobiTransition
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Functional measurability retained at the final integration boundary.
The separated gauge theorem already supplies every pointwise inequality. -/
structure FunctionalFacts
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {bound : ℝ} {E : Applied Gamma A}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (O : Output E B) : Prop where
  front : FunctionalIntegrable Gamma.eta
  rear : FunctionalIntegrable O.chosen.Delta.eta

def separatedCW
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (H : SeparatedApplied E) : ℝ := max 0 H.CW

def separatedC0
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (H : SeparatedApplied E) : ℝ := max 0 H.C0

def separatedC1
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (H : SeparatedApplied E) : ℝ :=
  max 0 (max H.C10 H.C11)

def separatedC2
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (H : SeparatedApplied E) : ℝ :=
  max 0 (max H.C20 (max H.C21 H.C22))

/-- Aggregate the theorem-produced separated coefficients only after their
pointwise estimates have been attached to the actual chosen path. -/
def rawOfSeparatedApplied
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    {O : Output E B} (H : SeparatedApplied E) (F : FunctionalFacts O) :
    RawJacobiAnalyticInput Gamma.eta O.chosen.Delta.eta
      (separatedCW H) (separatedC0 H) (separatedC1 H) (separatedC2 H) := by
  let G := H.flowedChosen O.chosen
  apply RawJacobiAnalyticInput.of_density_bounds
    (le_max_left 0 H.CW) (le_max_left 0 H.C0) F.front F.rear
  · intro t _
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    exact (G.w t).trans (mul_le_mul_of_nonneg_right
      (le_max_right 0 H.CW) hw)
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    exact (G.s0 t).trans (mul_le_mul_of_nonneg_right
      (le_max_right 0 H.C0) hw)
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    have hs : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have h10 : H.C10 ≤ separatedC1 H :=
      (le_max_left H.C10 H.C11).trans (le_max_right 0 _)
    have h11 : H.C11 ≤ separatedC1 H :=
      (le_max_right H.C10 H.C11).trans (le_max_right 0 _)
    calc
      supNorm (iteratedDeriv 1 (O.chosen.Delta.eta t)) ≤
          H.C10 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            H.C11 * supNorm (Gamma.eta t) := G.s1 t
      _ ≤ separatedC1 H * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            separatedC1 H * supNorm (Gamma.eta t) :=
        add_le_add (mul_le_mul_of_nonneg_right h10 hw)
          (mul_le_mul_of_nonneg_right h11 hs)
      _ = separatedC1 H * (supNorm (Gamma.eta t) +
          ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by ring
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    have hs0 : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have hs1 : 0 ≤ supNorm (iteratedDeriv 1 (Gamma.eta t)) := supNorm_nonneg _
    have h20 : H.C20 ≤ separatedC2 H :=
      (le_max_left H.C20 (max H.C21 H.C22)).trans (le_max_right 0 _)
    have h21 : H.C21 ≤ separatedC2 H :=
      ((le_max_left H.C21 H.C22).trans
        (le_max_right H.C20 (max H.C21 H.C22))).trans (le_max_right 0 _)
    have h22 : H.C22 ≤ separatedC2 H :=
      ((le_max_right H.C21 H.C22).trans
        (le_max_right H.C20 (max H.C21 H.C22))).trans (le_max_right 0 _)
    calc
      supNorm (iteratedDeriv 2 (O.chosen.Delta.eta t)) ≤
          H.C20 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            H.C21 * supNorm (Gamma.eta t) +
            H.C22 * supNorm (iteratedDeriv 1 (Gamma.eta t)) := G.s2 t
      _ ≤ separatedC2 H * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            separatedC2 H * supNorm (Gamma.eta t) +
            separatedC2 H * supNorm (iteratedDeriv 1 (Gamma.eta t)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right h20 hw)
          (mul_le_mul_of_nonneg_right h21 hs0))
          (mul_le_mul_of_nonneg_right h22 hs1)
      _ = separatedC2 H * supNorm (Gamma.eta t) +
          separatedC2 H * supNorm (iteratedDeriv 1 (Gamma.eta t)) +
          separatedC2 H * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by ring
  · intro t
    refine ⟨O.chosen.Delta.m t, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact O.chosen.Delta.abs_eta_le t x
  · intro t
    have hd1 : deriv (O.chosen.Delta.eta t) = O.chosen.c2.eta1 t :=
      funext fun u ↦ (O.chosen.c2.eta_deriv t u).deriv
    simpa only [iteratedDeriv_one, hd1] using O.chosen.c2.eta1_bdd t
  · intro t
    have hd1 : deriv (O.chosen.Delta.eta t) = O.chosen.c2.eta1 t :=
      funext fun u ↦ (O.chosen.c2.eta_deriv t u).deriv
    have hd2 : deriv (O.chosen.c2.eta1 t) = O.chosen.c2.eta2 t :=
      funext fun u ↦ (O.chosen.c2.eta1_deriv t u).deriv
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero, hd1, hd2]
    exact O.chosen.c2.eta2_bdd t

/-- The identity spatial junction embeds raw physical bounds into any stable
recursive distortion ceiling with `1 <= MA` and `0 <= NA`. -/
def identityFixedReparamBounds
    (eta : ℝ → ℝ → ℝ) {MA NA : ℝ}
    (hMA : 1 ≤ MA) (hNA : 0 ≤ NA) :
    FixedReparamBounds eta eta 1 MA NA := by
  have hS1 : 0 ≤ S 1 eta := by
    unfold S
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun _ _ ↦ supNorm_nonneg _)
  have hS2 : 0 ≤ S 2 eta := by
    unfold S
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun _ _ ↦ supNorm_nonneg _)
  have hMA0 : 0 ≤ MA := zero_le_one.trans hMA
  have hsq : 1 ≤ MA ^ 2 := by nlinarith
  refine
    { w := by simp
      s0 := le_rfl
      s1 := ?_
      s2 := ?_ }
  · calc
      S 1 eta = 1 * S 1 eta := by ring
      _ ≤ MA * S 1 eta := mul_le_mul_of_nonneg_right hMA hS1
  · calc
      S 2 eta = 1 * S 2 eta := by ring
      _ ≤ MA ^ 2 * S 2 eta := mul_le_mul_of_nonneg_right hsq hS2
      _ ≤ MA ^ 2 * S 2 eta + NA * S 1 eta :=
        le_add_of_nonneg_right (mul_nonneg hNA hS1)

/-- Exact missing analytic data for one actual chosen terminal output.

`raw` consists of the four density-gain estimates erased by the current
marking-aware long theorem.  `domination` is only scalar physical rescaling;
it contains no new path or endpoint choice. -/
structure ConfiguredTransitionData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)}
    {B : TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E}
    (O : Output E B) where
  CW : ℝ
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  raw : RawJacobiAnalyticInput
    (S.column.step.richStage (n + 1)).stage.increment.eta
    O.chosen.Delta.eta CW c0 c1 c2
  domination : Domination
    (period (n + 1) k) (period n (k + 1)) (a n k)
    CW c0 c1 c2 K0 K1 K2
  MA_ge_one : 1 ≤ MA n k
  NA_nonnegative : 0 ≤ NA n k

/-- Construct configured transition data from the theorem-produced separated
sidecar, rather than accepting an unrelated raw Jacobi certificate. -/
def ConfiguredTransitionData.ofSeparatedApplied
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)}
    {B : TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E}
    {O : Output E B}
    (H : SeparatedApplied E) (F : FunctionalFacts O)
    (HD : Domination
      (period (n + 1) k) (period n (k + 1)) (a n k)
      (separatedCW H) (separatedC0 H) (separatedC1 H) (separatedC2 H)
      K0 K1 K2)
    (hMA : 1 ≤ MA n k) (hNA : 0 ≤ NA n k) :
    ConfiguredTransitionData (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) O where
  CW := separatedCW H
  c0 := separatedC0 H
  c1 := separatedC1 H
  c2 := separatedC2 H
  raw := rawOfSeparatedApplied H F
  domination := HD
  MA_ge_one := hMA
  NA_nonnegative := hNA

/-- Integrate the retained density gains, rescale to physical components, and
install the identity junction into the configured stable transition. -/
def ConfiguredTransitionData.transition
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)}
    {B : TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E}
    {O : Output E B}
    (D : ConfiguredTransitionData (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) O)
    (hperiod : 1 ≤ period n (k + 1)) :
    Transition
      (components (period (n + 1) k)
        (S.column.step.richStage (n + 1)).stage.increment.eta)
      (components (period n (k + 1)) O.chosen.Delta.eta)
      (a n k) (MA n k) (NA n k) K0 K1 K2 := by
  let rawPhysical : RawBounds
      (period (n + 1) k) (period n (k + 1))
      (S.column.step.richStage (n + 1)).stage.increment.eta
      O.chosen.Delta.eta (a n k) K0 K1 K2 :=
    RawBounds.of_normalized D.raw.toScaledRawJacobiBounds D.domination
  let junction : FixedReparamBounds O.chosen.Delta.eta O.chosen.Delta.eta
      1 (MA n k) (NA n k) :=
    identityFixedReparamBounds O.chosen.Delta.eta D.MA_ge_one D.NA_nonnegative
  simpa using transition_of_raw_and_fixedReparam hperiod (by norm_num)
    (zero_le_one.trans D.MA_ge_one) D.NA_nonnegative rawPhysical junction

/-- The existing row construction with precisely its transition field
removed.  This prevents a configured density package from depending
circularly on the abstract transition it is meant to construct. -/
structure RowConstructionCore
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  terminalInput : ∀ E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n),
    TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E
  P1_le : GaugeFlowDerivCost.costP1
      (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1
      (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  terminal_perim_ge_one :
    1 ≤ perim (S.column.step.richStage (n + 1)).terminalBase
  period_ge_one : 1 ≤ period n (k + 1)
  components_nonnegative : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    (components (period n (k + 1)) O.chosen.Delta.eta).Nonnegative
  components_bound : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    ComponentBound (components (period n (k + 1)) O.chosen.Delta.eta)
      (diagonal (n + (k + 1)))

/-- Row-construction data with the transition replaced by the exact retained
density package above. -/
structure ConfiguredRowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  core : RowConstructionCore (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  transitionData : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (core.terminalInput E)),
    ConfiguredTransitionData (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) O

/-- A row core carrying only theorem-produced separated applications and the
remaining integration/scalar facts.  In particular it has no raw Jacobi or
transition callback. -/
structure SeparatedRowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  core : RowConstructionCore (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  separated : ∀ E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n),
    SeparatedApplied E
  functional : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (core.terminalInput E)),
    FunctionalFacts O
  domination : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n)),
    Domination (period (n + 1) k) (period n (k + 1)) (a n k)
      (separatedCW (separated E)) (separatedC0 (separated E))
      (separatedC1 (separated E)) (separatedC2 (separated E)) K0 K1 K2
  MA_ge_one : 1 ≤ MA n k
  NA_nonnegative : 0 ≤ NA n k

/-- The nonaffine separated application selected canonically from the current
source's quantitative marking and slice facts. -/
noncomputable def nonaffineSeparated
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 m M : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : Nonaffine.Facts (S.source n) (P1 n) m M)
    (E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)) :
    SeparatedApplied E :=
  Classical.choice (exists_nonaffineSeparatedApplied E F)

/-- A row core with actual nonaffine source-marking facts.  Its separated
application is theorem-produced, so the row no longer carries an arbitrary
four-gain callback. -/
structure NonaffineSeparatedRowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 m M : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  core : RowConstructionCore (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  facts : Nonaffine.Facts (S.source n) (P1 n) m M
  functional : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (core.terminalInput E)),
    FunctionalFacts O
  domination : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n)),
    Domination (period (n + 1) k) (period n (k + 1)) (a n k)
      (separatedCW (nonaffineSeparated facts E))
      (separatedC0 (nonaffineSeparated facts E))
      (separatedC1 (nonaffineSeparated facts E))
      (separatedC2 (nonaffineSeparated facts E)) K0 K1 K2
  MA_ge_one : 1 ≤ MA n k
  NA_nonnegative : 0 ≤ NA n k

def NonaffineSeparatedRowConstruction.separatedRow
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 m M : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : NonaffineSeparatedRowConstruction (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) (m := m) (M := M) S) :
    SeparatedRowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  core := R.core
  separated E := nonaffineSeparated R.facts E
  functional := R.functional
  domination := R.domination
  MA_ge_one := R.MA_ge_one
  NA_nonnegative := R.NA_nonnegative

def NonaffineSeparatedRowConstruction.configured
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 m M : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : NonaffineSeparatedRowConstruction (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) (m := m) (M := M) S) :
    ConfiguredRowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  core := R.core
  transitionData E O := ConfiguredTransitionData.ofSeparatedApplied
    (nonaffineSeparated R.facts E) (R.functional E O) (R.domination E)
    R.MA_ge_one R.NA_nonnegative

/-- The remaining row data once the sliced-column invariant has supplied all
nonaffine source facts. -/
structure SlicedNonaffineRowData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (H : SlicedCorrelatedColumn S) where
  core : RowConstructionCore (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  functional : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (core.terminalInput E)),
    FunctionalFacts O
  domination : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n)),
    Domination (period (n + 1) k) (period n (k + 1)) (a n k)
      (separatedCW (nonaffineSeparated (Nonaffine.Facts.ofSlicedColumn H) E))
      (separatedC0 (nonaffineSeparated (Nonaffine.Facts.ofSlicedColumn H) E))
      (separatedC1 (nonaffineSeparated (Nonaffine.Facts.ofSlicedColumn H) E))
      (separatedC2 (nonaffineSeparated (Nonaffine.Facts.ofSlicedColumn H) E))
      K0 K1 K2
  MA_ge_one : 1 ≤ MA n k
  NA_nonnegative : 0 ≤ NA n k

/-- Install the sliced-column invariant into a concrete nonaffine row. -/
def SlicedNonaffineRowData.construction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {H : SlicedCorrelatedColumn S}
    (R : SlicedNonaffineRowData (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) H) :
    NonaffineSeparatedRowConstruction (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2)
      (m := (H.slice n).markingLower) (M := (H.slice n).markingUpper) S where
  core := R.core
  facts := Nonaffine.Facts.ofSlicedColumn H
  functional := R.functional
  domination := R.domination
  MA_ge_one := R.MA_ge_one
  NA_nonnegative := R.NA_nonnegative

/-- Direct ordinary row construction, avoiding any loss of the sliced
invariant through an intermediate provider interface. -/
def SlicedNonaffineRowData.rowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {H : SlicedCorrelatedColumn S}
    (R : SlicedNonaffineRowData (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) H) :
    FiniteSmoothRearFamilyMarkingAwareDirectSuccessor.RowConstruction
      (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  terminalInput := R.core.terminalInput
  P1_le := R.core.P1_le
  G1_le := R.core.G1_le
  Cg_le := R.core.Cg_le
  terminal_perim_ge_one := R.core.terminal_perim_ge_one
  period_ge_one := R.core.period_ge_one
  components_nonnegative := R.core.components_nonnegative
  components_bound := R.core.components_bound
  transition E O := (ConfiguredTransitionData.ofSeparatedApplied
    (nonaffineSeparated (Nonaffine.Facts.ofSlicedColumn H) E)
    (R.functional E O) (R.domination E) R.MA_ge_one R.NA_nonnegative).transition
      R.core.period_ge_one

/-- All rows at one recursive depth, with their transitions constructed from
the preserved nonaffine slice invariant. -/
structure SlicedNonaffineRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (H : SlicedCorrelatedColumn S) where
  rowData : ∀ n, SlicedNonaffineRowData (n := n) (a := a) (MA := MA)
    (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) H
  analytic : ∀ n, AnalyticSuccessor
    ((rowData (n + 1)).rowConstruction.chosenRow.output.chosen.Delta)
    (S.source (n + 1)) (P0 n) (kh n) (khat n) (Qmax n)

/-- Forget the sliced presentation after it has generated the ordinary row
family consumed by `successorOfRows`. -/
def SlicedNonaffineRowFamily.rowConstructionFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {H : SlicedCorrelatedColumn S}
    (F : SlicedNonaffineRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) H) :
    FiniteSmoothRearFamilyMarkingAwareDirectSuccessor.RowConstructionFamily
      (a := a) (MA := MA) (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S where
  construction n := (F.rowData n).rowConstruction
  analytic := F.analytic

/-- Invariant-preserving all-depth row production. -/
structure SlicedNonaffineRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  family : ∀ {current k}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (H : SlicedCorrelatedColumn S),
    SlicedNonaffineRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) H

/-- The chosen rows and successor selected by a sliced nonaffine family. -/
def SlicedNonaffineRowFamily.chosenFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {H : SlicedCorrelatedColumn S}
    (F : SlicedNonaffineRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) H) :
    FiniteSmoothRearFamilyMarkingAwareDirectSuccessor.ChosenRowFamily
      (a := a) (MA := MA) (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S :=
  F.rowConstructionFamily.chosenFamily

/-- Recursive nonaffine row production with the next sliced source retained.
The extra two fields are needed only for legacy analytic rows; exact rows can
reuse the sidecar already stored in `AnalyticSuccessor.exact`. -/
structure RecursiveSlicedNonaffineRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  rows : SlicedNonaffineRowProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2
  mappedSlice : ∀ {current k}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2} (H : SlicedCorrelatedColumn S) n,
    AnalyticSuccessorSliceFacts
      ((((rows.family H).chosenFamily.successor).mappedColumn).source n)
  mappedPeriodUpper_le : ∀ {current k}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2} (H : SlicedCorrelatedColumn S) n,
    (mappedSlice H n).periodUpper ≤ P1 n

/-- The invariant-indexed successor provider generated by all-depth nonaffine
rows. -/
def RecursiveSlicedNonaffineRowProvider.slicedProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : RecursiveSlicedNonaffineRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    SlicedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 where
  successor S H := (G.rows.family H).chosenFamily.successor
  mappedSlice S H := G.mappedSlice H
  mappedPeriodUpper_le S H := G.mappedPeriodUpper_le H

/-- Synthesize the formerly abstract raw transition field from each retained
separated application. -/
def SeparatedRowConstruction.configured
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : SeparatedRowConstruction (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S) :
    ConfiguredRowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  core := R.core
  transitionData E O := ConfiguredTransitionData.ofSeparatedApplied
    (R.separated E) (R.functional E O) (R.domination E)
    R.MA_ge_one R.NA_nonnegative

/-- Replace an existing abstract transition proof by the constructed density
transition.  This is useful immediately for providers whose other row fields
are already packaged by `RowConstruction`. -/
def ConfiguredRowConstruction.rowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : ConfiguredRowConstruction (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S) :
    FiniteSmoothRearFamilyMarkingAwareDirectSuccessor.RowConstruction
      (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  terminalInput := R.core.terminalInput
  P1_le := R.core.P1_le
  G1_le := R.core.G1_le
  Cg_le := R.core.Cg_le
  terminal_perim_ge_one := R.core.terminal_perim_ge_one
  period_ge_one := R.core.period_ge_one
  components_nonnegative := R.core.components_nonnegative
  components_bound := R.core.components_bound
  transition E O := (R.transitionData E O).transition R.core.period_ge_one

end FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
