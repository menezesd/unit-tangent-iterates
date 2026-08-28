import UnitTangentIterates.PaperMainTheoremC2Projection
import UnitTangentIterates.SelectedRearAllOrdersRegularity

/-!
# Smooth paper-facing projection from local shifted rear stages
-/

noncomputable section

open Set MarkedSpace

namespace PaperMainTheoremSmoothProjection

/-- The paper-facing projection with honest `C∞` regularity.  The infinity
index is the inner `ℕ∞` infinity; bare outer `⊤` would assert analyticity. -/
theorem of_output_of_representatives
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ}
    {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (R : ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (O.X n))
    (A : PaperFacingVariableTerminalOutput.Output O direction modelWidth H)
    (hGamma : A.Gamma = fun n => ev (R n).q)
    (hstage : ∀ n, ∃ q : ℝ, Nonempty
      (PathMetric.PhysicalRearLimitStageComponents
        (R n).q (MarkedShift.shiftData q (R (n + 1)).q))) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      0 < L ∧
      Function.Periodic (Gamma 0) L ∧
      InjOn (Gamma 0) (Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  let X : ℕ → Data := fun n => (R n).q
  have htube : ∀ n, IsTubeMember (R n).c 0 (R n).dlt (X n) :=
    fun n => (R n).tube
  have hC2 : ∀ n, ContDiff ℝ (2 : ℕ) (ev (X n)) := fun n =>
    PaperMainTheoremC2Projection.contDiff_two_ev_of_tube
      (R n).c_pos (R n).tube
  have hsmoothX : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ev (X n)) := by
    -- The tube constants may vary by row, but each induction step only needs
    -- the next row's own positive tube.  Normalize the general bootstrap to
    -- the retained representatives directly.
    have hfinite : ∀ r n, ContDiff ℝ (r + 2 : ℕ) (ev (X n)) := by
      intro r
      induction r with
      | zero =>
          intro n
          simpa using hC2 n
      | succ r ih =>
          intro n
          obtain ⟨q, ⟨S⟩⟩ := hstage n
          have hfront : ContDiff ℝ (r + 2 : ℕ)
              (ev (MarkedShift.shiftData q (X (n + 1)))) :=
            SelectedRearAllOrdersRegularity.contDiff_ev_shiftData
              (R (n + 1)).c_pos (R (n + 1)).tube (ih (n + 1)) q
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            SelectedRearOneStepRegularity.contDiff_succ_ev_of_stage_of_front
              r S hfront
    intro n
    exact contDiff_infty.2 fun m =>
      (hfinite m n).of_le (by exact_mod_cast Nat.le_add_right m 2)
  let L := MarkedReparam.totalLength fun u => (O.X 0).2.1 u
  have hL : L = perim (R 0).q := by
    exact (R 0).physical_length
  have hinj : InjOn (A.Gamma 0) (Ico 0 L) := by
    rw [hGamma, hL]
    exact PaperMainTheoremC2Projection.injOn_ev_simple_period
      (R 0).c_pos (R 0).dlt_pos (R 0).tube
  have hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A.Gamma n) := by
    rw [hGamma]
    exact hsmoothX
  exact ⟨A.Gamma, L, A.physical_length_pos, A.physical_periodic, hinj,
    A.oval, hsmooth, A.range_orbit, A.noncircle⟩

end PaperMainTheoremSmoothProjection
