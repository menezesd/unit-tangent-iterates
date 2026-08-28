import UnitTangentIterates.ConfiguredGaugeFirstPhysicalSequence
import UnitTangentIterates.ConfiguredGaugeEndpointDefect
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Physical facts for the gauge-first canonical terminal

The depth-zero gauge stage stores a cyclic shift and a unit rigid image of the
canonical `kH` carrier.  This module transports the ordinary Frenet package
through those two harmless changes of presentation.  In particular the
curvature Lipschitz constant is obtained from the configured derivative bound;
it is not retained as a callback.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredGaugeFirstTerminalPhysicalFacts

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredGaugeEndpointDefect
  RichStageDataPhaseRigidTransport

/-- The canonical configured `kH` carrier has the complete ordinary physical
endpoint package used by the gauge marking-defect estimate. -/
def carrierFacts
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) : TerminalPhysicalFacts A.data := by
  let cfg := D.model.configs n
  have hLip : ∀ s t, |cfg.kH s - cfg.kH t| ≤ D.kd * |s - t| := by
    intro s t
    have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ cfg.kH x :=
      fun x _ => (cfg.hasDerivAt_kH x).differentiableAt
    have hbdd : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv cfg.kH x‖ ≤ D.kd := by
      intro x _
      rw [(cfg.hasDerivAt_kH x).deriv, Real.norm_eq_abs]
      simpa [D.model_kd] using cfg.abs_kHderiv_le x
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hbdd convex_univ (mem_univ s) (mem_univ t)
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  refine
    { cq := A.c
      kmin := 0
      dlt := A.dlt
      L := 2 * D.Hs n
      kb := D.kstar
      kL := D.kd
      Theta := CurvatureInterpolation.tangentAngle cfg.kH D.model.thetaBase
      curvature := cfg.kH
      cq_pos := A.c_pos
      tube := A.tube
      perim_eq := A.perim_eq
      curve_frenet := ?_
      angle_deriv := ?_
      curvature_bound := ?_
      curvature_lipschitz := hLip }
  · intro s
    rw [A.curve_eq]
    simpa [SelectedInverseCarrier.tau_eq_exp] using
      (CurvatureInterpolation.hasDerivAt_interpCurve
        (kappa := cfg.kH) (θ₀ := D.model.thetaBase) (L := D.Hs n)
        cfg.continuous_kH s)
  · exact CurvatureInterpolation.hasDerivAt_tangentAngle cfg.continuous_kH
  · intro s
    rw [abs_of_nonneg (cfg.kH_nonneg s)]
    simpa [D.model_kstar] using cfg.kH_le s

/-- Cyclic re-marking preserves all intrinsic endpoint constants. -/
def shiftFacts {b : Data} (P : TerminalPhysicalFacts b) (r : ℝ) :
    TerminalPhysicalFacts (MarkedShift.shiftData r b) := by
  let q := r * P.L
  have hL : perim b ≠ 0 := by
    exact ne_of_gt (perim_pos P.cq_pos P.tube)
  have hev : ev (MarkedShift.shiftData r b) = fun s => ev b (s + q) := by
    funext s
    rw [SelectedInverseShiftEquivariance.ev_shiftData P.tube hL r s,
      P.perim_eq]
  refine
    { cq := P.cq
      kmin := P.kmin
      dlt := P.dlt
      L := P.L
      kb := P.kb
      kL := P.kL
      Theta := fun s => P.Theta (s + q)
      curvature := fun s => P.curvature (s + q)
      cq_pos := P.cq_pos
      tube := MarkedShift.isTubeMember_shiftData P.tube r
      perim_eq := (SelectedInverseShiftEquivariance.perim_shiftData P.tube r).trans
        P.perim_eq
      curve_frenet := ?_
      angle_deriv := ?_
      curvature_bound := fun s => P.curvature_bound (s + q)
      curvature_lipschitz := ?_ }
  · intro s
    have hi : HasDerivAt (fun x : ℝ => x + q) 1 s := by
      simpa using (hasDerivAt_id s).add_const q
    rw [hev]
    simpa [Function.comp_def] using (P.curve_frenet (s + q)).scomp s hi
  · intro s
    have hi : HasDerivAt (fun x : ℝ => x + q) 1 s := by
      simpa using (hasDerivAt_id s).add_const q
    simpa [Function.comp_def] using (P.angle_deriv (s + q)).scomp s hi
  · intro s t
    have h := P.curvature_lipschitz (s + q) (t + q)
    simpa only [add_sub_add_right_eq_sub] using h

/-- Orientation-preserving rigid motion preserves the intrinsic endpoint
constants and rotates the tangent angle by `arg w`. -/
def rigidFacts {b : Data} (P : TerminalPhysicalFacts b)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    TerminalPhysicalFacts (MarkedRigid.rigidData a w b) := by
  let phi : ℝ := Complex.arg w
  have hphase : Complex.exp ((phi : ℂ) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [phi] using h
  have hperim : perim (MarkedRigid.rigidData a w b) = perim b := by
    simp [perim, hw]
  refine
    { cq := P.cq
      kmin := P.kmin
      dlt := P.dlt
      L := P.L
      kb := P.kb
      kL := P.kL
      Theta := fun s => phi + P.Theta s
      curvature := P.curvature
      cq_pos := P.cq_pos
      tube := MarkedRigid.isTubeMember_rigidData hw P.tube
      perim_eq := hperim.trans P.perim_eq
      curve_frenet := ?_
      angle_deriv := ?_
      curvature_bound := P.curvature_bound
      curvature_lipschitz := P.curvature_lipschitz }
  · intro s
    have hd := ((P.curve_frenet s).const_mul w).const_add a
    have hexp : Complex.exp (Complex.I * (((phi + P.Theta s : ℝ) : ℂ))) =
        w * Complex.exp (Complex.I * ((P.Theta s : ℝ) : ℂ)) := by
      rw [show (((phi + P.Theta s : ℝ) : ℂ)) =
        (phi : ℂ) + (P.Theta s : ℂ) by norm_num, mul_add, Complex.exp_add]
      rw [show Complex.I * (phi : ℂ) = (phi : ℂ) * Complex.I by ring,
        hphase]
    have hev : ev (MarkedRigid.rigidData a w b) = fun t => a + w * ev b t := by
      funext t
      simp [ev, hperim]
    rw [hev, hexp]
    simpa [add_comm] using hd
  · intro s
    simpa [add_comm] using (P.angle_deriv s).const_add phi

/-- The exact phase/rigid presentation used by the gauge-first recursion. -/
def moveFacts {b : Data} (P : TerminalPhysicalFacts b)
    (a w : ℂ) (r : ℝ) (hw : ‖w‖ = 1) :
    TerminalPhysicalFacts (move a w r b) :=
  rigidFacts (shiftFacts P r) a w hw

/-- Physical endpoint facts for the terminal base selected at row `n`. -/
theorem chosenTerminalPhysical
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ} (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (Krow : ℝ) (C : ℕ → ℝ) (n : ℕ) :
    Nonempty (TerminalPhysicalFacts
      (Classical.choose
        (ConfiguredGaugeFirstPhysicalSequence.exists_richStage
          S hQ Krow C n)).terminalBase) := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations
    (S := S) (hQ := hQ) n
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A
  have heq := Classical.choose_spec
    (ConfiguredGaugeFirstPhysicalSequence.exists_richStage S hQ Krow C n)
  rw [heq.1]
  exact ⟨moveFacts (carrierFacts (S.carrier n))
    A.translation A.rotation r A.rotation_norm⟩

end ConfiguredGaugeFirstTerminalPhysicalFacts
