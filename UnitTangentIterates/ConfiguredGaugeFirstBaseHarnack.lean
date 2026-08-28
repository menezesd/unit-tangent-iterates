import UnitTangentIterates.ConfiguredGaugeFirstPhysicalSequence
import UnitTangentIterates.ConfiguredCompatiblePhysicalRearSequence
import UnitTangentIterates.EnrichedPhysicalHarnackClosureAdapters

/-!
# Harnack and common-tube data for gauge-first aligned bases

The gauge-first recursion stores every base front as a phase shift followed by
an orientation-preserving rigid motion of the configured model front.  This
module transports model strictness through that presentation and records the
exact monotonicity hypotheses needed to lower tube constants.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredGaugeFirstBaseHarnack

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredCompatiblePhysicalRearSequence
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredModelPairSource
  EnrichedPhysicalChosenRichFamily
  EnrichedPhysicalHarnackClosure
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube

/-- Integrated strictness is invariant under an orientation-preserving rigid
motion. -/
def rigidLimitStrictnessDataH {p : Data}
    (H : UnconditionalAssembly.LimitStrictnessDataH p)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    UnconditionalAssembly.LimitStrictnessDataH (MarkedRigid.rigidData a w p) := by
  let phi : ℝ := Complex.arg w
  have hphase : Complex.exp ((phi : ℂ) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [phi] using h
  have hperim : perim (MarkedRigid.rigidData a w p) = perim p := by
    simp [perim, hw]
  refine
    { theta := fun s => phi + H.theta s
      k := H.k
      curve_deriv := ?_
      angle_deriv := ?_
      curvature_periodic := ?_
      curvature_nonnegative := H.curvature_nonnegative
      curvature_harnack := H.curvature_harnack
      curvature_nonzero := H.curvature_nonzero }
  · intro s
    have hd := ((H.curve_deriv s).const_mul w).const_add a
    have hexp : Complex.exp (Complex.I * (((phi + H.theta s : ℝ) : ℂ))) =
        w * Complex.exp (Complex.I * ((H.theta s : ℝ) : ℂ)) := by
      rw [show (((phi + H.theta s : ℝ) : ℂ)) =
        (phi : ℂ) + (H.theta s : ℂ) by norm_num, mul_add, Complex.exp_add]
      rw [show Complex.I * (phi : ℂ) = (phi : ℂ) * Complex.I by ring,
        hphase]
    have hev : ev (MarkedRigid.rigidData a w p) =
        fun t => a + w * ev p t := by
      funext t
      simp [ev, hperim]
    rw [hev, hexp]
    simpa [add_comm] using hd
  · intro s
    simpa [add_comm] using (H.angle_deriv s).const_add phi
  · rw [hperim]
    exact H.curvature_periodic

/-- A canonical strictness certificate on each configured front transports
to the exact aligned base selected by the gauge-first presentation recursion. -/
def alignedStrictness
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt : ℝ}
    (S : Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (H : ∀ n, UnconditionalAssembly.LimitStrictnessDataH (Q n))
    (n : ℕ) : UnconditionalAssembly.LimitStrictnessDataH
      (alignedQ S hQ n) := by
  let A := presentations (S := S) (hQ := hQ) n
  let HS := shiftLimitStrictnessDataH S.c_pos (S.front_tube n)
    (H n) A.phase
  simpa [alignedQ, Presentation.data, RichStageDataPhaseRigidTransport.move, A]
    using rigidLimitStrictnessDataH HS A.translation A.rotation A.rotation_norm

/-- The aligned configured fronts carry the same Harnack representative: the
representative is the aligned datum itself. -/
def baseHarnack
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt : ℝ}
    (S : Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (hdlt : 0 < dlt)
    (H : ∀ n, UnconditionalAssembly.LimitStrictnessDataH (Q n)) :
    ∀ n, ArclengthHarnackCertificate (alignedQ S hQ n) := by
  intro n
  exact
    { q := alignedQ S hQ n
      c := c
      dlt := dlt
      c_pos := S.c_pos
      dlt_pos := hdlt
      tube := alignedQ_tube S hQ n
      same_range := rfl
      strictness := alignedStrictness S hQ H n }

/-- Lowering the requested speed and chord constants gives a common tube on
every aligned base front. -/
theorem alignedQ_commonTube
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt cb db : ℝ}
    (S : Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (hcb : cb ≤ c) (hdb : db ≤ dlt) :
    ∀ n, IsTubeMember cb 0 db (alignedQ S hQ n) := by
  intro n
  exact (alignedQ_tube S hQ n).mono hcb hdb

/-- Presentation-facing base certificate consumed by construction-core
completion.  The upstream model constructor must supply `modelStrictness`, and
the concrete tube budget must prove the two displayed constant comparisons. -/
structure Certificate
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt : ℝ}
    (S : Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (cb db : ℝ) where
  cb_pos : 0 < cb
  db_pos : 0 < db
  cb_le : cb ≤ c
  db_le : db ≤ dlt
  modelStrictness : ∀ n, UnconditionalAssembly.LimitStrictnessDataH (Q n)

def Certificate.baseHarnack
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt cb db : ℝ}
    {S : Input D Q kh c dlt}
    {hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n)}
    (Z : Certificate S hQ cb db) :
    ∀ n, ArclengthHarnackCertificate (alignedQ S hQ n) :=
  ConfiguredGaugeFirstBaseHarnack.baseHarnack S hQ
    (Z.db_pos.trans_le Z.db_le) Z.modelStrictness

def Certificate.baseTube
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt cb db : ℝ}
    {S : Input D Q kh c dlt}
    {hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n)}
    (Z : Certificate S hQ cb db) :
    ∀ n, IsTubeMember cb 0 db (alignedQ S hQ n) :=
  alignedQ_commonTube S hQ Z.cb_le Z.db_le

end ConfiguredGaugeFirstBaseHarnack
