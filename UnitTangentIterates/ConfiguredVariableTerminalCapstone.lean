import UnitTangentIterates.GenericVariableTerminalCapstone
import UnitTangentIterates.ConstructedPulseWidth
import UnitTangentIterates.ConstructedRowDefectLargeSeparation
import UnitTangentIterates.ConfiguredRowDefectProvider
import UnitTangentIterates.RichFamilyRetainedPhysicalRows
import UnitTangentIterates.CurveDistance

/-!
# Configured variable-terminal capstone shell

This file specializes the generic variable-terminal capstone to the honest
configured row defect and the large-separation scalar output.  The recursive
base/map providers remain named inputs.  All scalar row-tail, width, model
tube, and closing bookkeeping is performed here.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace ConfiguredVariableTerminalCapstone

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
open ConfiguredApproximateDefectPathRowwise
open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open ConstructedRowDefectLargeSeparation
open VariableTerminalRowTubeAdapter

/-- The exact marked-distance conversion constant of configured row `n`,
computed using the common path-class ceilings retained by the recursive
construction.  These may be larger than the canonical model ceilings. -/
def rowConversion (D : ConstructedConfiguredSequenceWeighted.Data)
    (P1 G1 Cg : ℕ → ℝ) (n : ℕ) : ℝ :=
  c2ConstVar (rowP0 D n) (P1 n) D.kstar (G1 n) (Cg n)

/-- The rowwise upper-speed ceiling after reserving the native shadow radius. -/
def rowUpper (D : ConstructedConfiguredSequenceWeighted.Data)
    (A : ℕ → ℝ) (K : ℝ) (n : ℕ) : ℝ :=
  2 * D.Hs n + rowRadius A D K n

/-- Physical rows retained by the provider-level recursive construction.
Row zero is the configured front and every successor is the actual physical
base stored by the corresponding rich stage. -/
def retainedPhysicalRows
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (BS : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (MS : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt) :
    ℕ → ℕ → Data
  | n, 0 => Q n
  | n, k + 1 => ((chosenStep BS MS k).richStage n).terminalBase

@[simp] theorem retainedPhysicalRows_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (BS : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (MS : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt) (n : ℕ) :
    retainedPhysicalRows BS MS n 0 = Q n := rfl

@[simp] theorem retainedPhysicalRows_succ
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (BS : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (MS : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt) (n k : ℕ) :
    retainedPhysicalRows BS MS n (k + 1) =
      ((chosenStep BS MS k).richStage n).terminalBase := rfl

/-- The genuinely unconstructed fields after the configured scalar and model
data have been fixed.  In particular the physical rows are retained through
the typed configured package rather than through unrelated tube callbacks. -/
structure Residual
    (D : ConstructedConfiguredSequenceWeighted.Data) (K Cw kh cb db : ℝ)
    (direction : ℕ → ℂ) (P1 G1 Cg : ℕ → ℝ)
    (L : ConstructedRowDefectLargeSeparation.Output
      D (rowConversion D P1 G1 Cg) K Cw)
    (Q : ℕ → Data)
    (BS : BaseStageProvider Q
      (ConfiguredRowDefectProvider.error (shift D L.N) K)
      (rowP0 (shift D L.N)) (shiftSequence P1 L.N)
      (fun _ => (shift D L.N).kstar) (shiftSequence G1 L.N)
      (shiftSequence Cg L.N)
      (rowUpper (shift D L.N)
        (shiftSequence (rowConversion D P1 G1 Cg) L.N) K)
      ((shift D L.N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2))
    (MS : MapStageProvider Q
      (ConfiguredRowDefectProvider.error (shift D L.N) K)
      (rowP0 (shift D L.N)) (shiftSequence P1 L.N)
      (fun _ => (shift D L.N).kstar) (shiftSequence G1 L.N)
      (shiftSequence Cg L.N)
      (rowUpper (shift D L.N)
        (shiftSequence (rowConversion D P1 G1 Cg) L.N) K)
      ((shift D L.N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2)) : Type where
  conversion_shift : ∀ n,
    rowConversion (shift D L.N) (shiftSequence P1 L.N)
      (shiftSequence G1 L.N) (shiftSequence Cg L.N) n =
        shiftSequence (rowConversion D P1 G1 Cg) L.N n
  model_data : ∀ n,
    perim (Q n) = 2 * (shift D L.N).Hs n ∧
    ev (Q n) = TwoCapPairsAssembly.front
      ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
      ((shift D L.N).Hs n)
  model_budget :
    PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q 1 K
      (rowDefect (shift D L.N)) ((shift D L.N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model)
      (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2)
      (ConfiguredInductiveTubeBudget.accBound (shift D L.N).model)
      (ConfiguredInductiveTubeBudget.rowRho (shift D L.N).model 1 K
        (rowDefect (shift D L.N)))
  base_harnack : ∀ n, VariableMarkedTube.ArclengthHarnackCertificate (Q n)
  physical_cb_pos : 0 < cb
  physical_dlt_pos : 0 < db
  physical : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
    (retainedPhysicalRows BS MS) (fun n k => columns BS MS k n) cb db
  finite : FinitePullbackPhysicalRearKinematics kh (retainedPhysicalRows BS MS)
  Xphysical : ℕ → Data
  physical_limit : ∀ n, Tendsto
    (retainedPhysicalRows BS MS n)
    atTop (nhds (Xphysical n))

/-- Configured data and one native large-separation output feed the generic
variable-terminal capstone. -/
theorem conclude
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {K Cw kh cb db : ℝ} {direction : ℕ → ℂ}
    (P1 G1 Cg : ℕ → ℝ)
    (hK : 1 ≤ K) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hthreshold : K * Real.exp
      (-((D.model.beta / 4) * D.deltaStep)) < 1)
    (hCw : 0 ≤ Cw) (hdirection : ∀ n, ‖direction n‖ = 1)
    (hwidth : ∀ n, Width.width
      (range (TwoCapPairsAssembly.front (D.kappas n) D.model.thetaBase (D.Hs n)))
      (direction n) ≤ Cw)
    (L : ConstructedRowDefectLargeSeparation.Output
      D (rowConversion D P1 G1 Cg) K Cw)
    (Q : ℕ → Data)
    (BS : BaseStageProvider Q
      (ConfiguredRowDefectProvider.error (shift D L.N) K)
      (rowP0 (shift D L.N)) (shiftSequence P1 L.N)
      (fun _ => (shift D L.N).kstar) (shiftSequence G1 L.N)
      (shiftSequence Cg L.N)
      (rowUpper (shift D L.N)
        (shiftSequence (rowConversion D P1 G1 Cg) L.N) K)
      ((shift D L.N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2))
    (MS : MapStageProvider Q
      (ConfiguredRowDefectProvider.error (shift D L.N) K)
      (rowP0 (shift D L.N)) (shiftSequence P1 L.N)
      (fun _ => (shift D L.N).kstar) (shiftSequence G1 L.N)
      (shiftSequence Cg L.N)
      (rowUpper (shift D L.N)
        (shiftSequence (rowConversion D P1 G1 Cg) L.N) K)
      ((shift D L.N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2))
    (R : Residual D K Cw kh cb db direction P1 G1 Cg L Q BS MS) :
    Nonempty (
      Σ (F : RichFamily Q
        (ConfiguredRowDefectProvider.error (shift D L.N) K)
        (rowP0 (shift D L.N)) (shiftSequence P1 L.N)
        (fun _ => (shift D L.N).kstar) (shiftSequence G1 L.N)
        (shiftSequence Cg L.N)
        (rowUpper (shift D L.N)
          (shiftSequence (rowConversion D P1 G1 Cg) L.N) K)
        ((shift D L.N).Hs 0)
        (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2)),
      Σ (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput Q F.P
        (ConfiguredRowDefectProvider.error (shift D L.N) K)
        (rowP0 (shift D L.N)) (shiftSequence P1 L.N)
        (fun _ => (shift D L.N).kstar) (shiftSequence G1 L.N)
        (shiftSequence Cg L.N)
        (rowUpper (shift D L.N)
          (shiftSequence (rowConversion D P1 G1 Cg) L.N) K)
        ((shift D L.N).Hs 0)
        (ConfiguredInductiveTubeBudget.chordBase (shift D L.N).model / 2)),
        PaperFacingVariableTerminalOutput.Output O (direction L.N) Cw
          ((shift D L.N).Hs 0)) := by
  let D' := shift D L.N
  let P1' : ℕ → ℝ := shiftSequence P1 L.N
  let G1' : ℕ → ℝ := shiftSequence G1 L.N
  let Cg' : ℕ → ℝ := shiftSequence Cg L.N
  let A : ℕ → ℝ := shiftSequence (rowConversion D P1 G1 Cg) L.N
  let e : ℕ → ℕ → ℝ := ConfiguredRowDefectProvider.error D' K
  let rad : ℕ → ℝ := rowRadius A D' K
  let rho : ℕ → ℝ := rowRhoVariable D'.model rad
  let Cup : ℕ → ℝ := rowUpper D' A K
  let defect : RowDefectProvider e := ConfiguredRowDefectProvider.provider D' hK (by
    simpa [D'] using hthreshold)
  have hrad0 : ∀ n, 0 ≤ rad n := by
    intro n
    dsimp [rad, rowRadius]
    exact mul_nonneg (by
      have hc : 0 ≤ rowConversion D' P1' G1' Cg' n :=
        c2ConstVar_nonneg _ _ _ _ _
      rw [R.conversion_shift n] at hc
      simpa [A] using hc)
      (ShadowingTails.tail_nonneg (defect.nonnegative n) 0)
  have hspeed : ∀ n, rad n ≤ D'.Hs 0 := by
    intro n
    simpa [rad, A, D'] using L.speed_tail n
  have hH0 : 0 < D'.Hs 0 := D'.separation_zero_pos
  have hkstar : 0 < D'.model.kstar :=
    ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D'.model
  have hchord : 0 < ConfiguredInductiveTubeBudget.chordBase D'.model := by
    rw [ConstructedConfiguredInductiveTubeBudget.chordBase_eq_min D'.model hkstar]
    exact lt_min hH0 (div_pos Real.pi_pos (mul_pos (by norm_num) hkstar))
  have hbase : ∀ n, IsTubeMember (2 * D'.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase D'.model) (Q n) := by
    intro n
    let hq := R.model_budget.model_mem n
    exact
      { hasDerivAt_curve := hq.hasDerivAt_curve
        hasDerivAt_vel := hq.hasDerivAt_vel
        periodic := hq.periodic
        speed_const := hq.speed_const
        speed_lb := fun u => by
          rw [norm_vel_eq_perim hq u, (R.model_data n).1]
          exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num)
        curv_lb := hq.curv_lb
        chord := hq.chord }
  have hrho0 : ∀ n, 0 < rho n := by
    intro n
    dsimp [rho, rowRhoVariable]
    apply lt_min
    · norm_num
    · exact div_pos hH0 (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
        (mul_pos (sq_pos_of_pos (mul_pos (by norm_num) (D'.model.separation_pos n)))
          hkstar) (hrad0 n)))
  have haccRadius : ∀ n,
      (ConfiguredInductiveTubeBudget.accBound D'.model n + rad n) * rho n ≤
        (2 * D'.Hs 0 - rad n) / 2 := by
    intro n
    have hden : 0 < ConfiguredInductiveTubeBudget.accBound D'.model n + rad n :=
      add_pos_of_pos_of_nonneg (mul_pos
        (sq_pos_of_pos (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar)
        (hrad0 n)
    have hmin := min_le_right (1 / 2 : ℝ)
      (D'.Hs 0 / (2 * (ConfiguredInductiveTubeBudget.accBound D'.model n + rad n)))
    have hm : (ConfiguredInductiveTubeBudget.accBound D'.model n + rad n) * rho n ≤
        D'.Hs 0 / 2 := by
      calc
        _ ≤ (ConfiguredInductiveTubeBudget.accBound D'.model n + rad n) *
            (D'.Hs 0 / (2 * (ConfiguredInductiveTubeBudget.accBound D'.model n + rad n))) :=
          mul_le_mul_of_nonneg_left hmin hden.le
        _ = D'.Hs 0 / 2 := by field_simp
    linarith [hspeed n]
  have hchord_le : ConfiguredInductiveTubeBudget.chordBase D'.model ≤ D'.Hs 0 := by
    rw [ConstructedConfiguredInductiveTubeBudget.chordBase_eq_min D'.model hkstar]
    exact min_le_left _ _
  let RB : RowBudget Q (rowP0 D') P1' (fun _ => D'.kstar)
      G1' Cg' (fun _ => 2 * D'.Hs 0)
      (fun _ => ConfiguredInductiveTubeBudget.chordBase D'.model)
      (ConfiguredInductiveTubeBudget.accBound D'.model) rad rho Cup
      (D'.Hs 0) (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) :=
    { radius_nonnegative := hrad0
      local_speed_positive := fun n => by linarith [hspeed n, hH0]
      target_speed := fun n => by linarith [hspeed n]
      acceleration_nonnegative := fun n =>
        (R.model_budget.acc_nonneg n)
      rho_positive := hrho0
      rho_half := fun n => min_le_left _ _
      acceleration_radius := haccRadius
      chord_nonnegative := (half_pos hchord).le
      chord_speed := by
        intro n
        linarith [hchord_le, hspeed n]
      chord_margin := by
        intro n
        convert L.chord_tail n using 1 <;>
          simp only [D', A, rad, rho] <;> ring
      upper_speed := by
        intro n
        simp only [Cup, rowUpper]
        rw [(R.model_data n).1] }
  have hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤
      ShadowingTails.tail (e n) 0 := by
    intro n k
    simpa [ShadowingTails.tail] using
      (defect.summable n).sum_le_tsum (Finset.range k)
        (fun i _ => defect.nonnegative n i)
  have hradius : ∀ n,
      c2ConstVar (rowP0 D' n) (P1' n) D'.kstar
        (G1' n) (Cg' n) * ShadowingTails.tail (e n) 0 ≤ rad n := by
    intro n
    change rowConversion D' P1' G1' Cg' n *
      ShadowingTails.tail (e n) 0 ≤ rad n
    rw [R.conversion_shift n]
    exact le_rfl
  have hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)) := by
    apply CurveDistance.isBounded_range_of_periodic
    · exact continuous_iff_continuousAt.2 fun u =>
        ((hbase 0).hasDerivAt_curve u).continuousAt
    · exact (hbase 0).periodic
    · norm_num
  have hQwidth : Width.width (range (⇑(Q 0).1)) (direction L.N) ≤ Cw := by
    rw [← MarkedSpace.range_ev (mul_pos (by norm_num) hH0) (hbase 0),
      (R.model_data 0).2]
    simpa [D'] using hwidth L.N
  have hQlength : 2 * D'.Hs 0 ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u) := by
    rw [VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube (hbase 0),
      (R.model_data 0).1]
  apply GenericVariableTerminalCapstone.exists_paperFacingOutput defect BS MS RB
    hbase R.model_budget.model_acc hpartial hradius R.base_harnack
    R.physical_cb_pos R.physical_dlt_pos hkh0 hkh1 R.physical
    R.finite R.physical_limit (by intro n; rfl) (by intro n k; rfl) hH0
    (hdirection L.N) hQbounded hQwidth hQlength
  intro O
  have hs : PaperFacingVariableTerminalOutput.shadowSize O = rad 0 := by
    change rowConversion D' P1' G1' Cg' 0 * ShadowingTails.tail (e 0) 0 =
      A 0 * ShadowingTails.tail (rowError D' K 0) 0
    rw [R.conversion_shift 0]
    congr 2
  rw [hs]
  simpa [D', A, rad] using L.width_gap

/-- Epsilon-facing configured shell.  The constructed pulse supplies the
strict configured datum, a unit direction at every possible shift, and the
uniform model-width bound.  The native large-separation theorem then chooses
the common shift and all scalar row budgets.  The sole scalar premise left at
this layer is the explicit growth estimate for the canonical row conversion
constant. -/
theorem exists_widthData_and_largeSeparationOutput_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (D : ConstructedConfiguredSequenceWeighted.Data)
      (direction : ℕ → ℂ) (Cw : ℝ),
      0 ≤ Cw ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (D.kappas n)
          D.model.thetaBase (D.Hs n))) (direction n) ≤ Cw) ∧
      ∀ (P1 G1 Cg : ℕ → ℝ) {C0 gamma K : ℝ},
        0 ≤ C0 → gamma < D.model.beta / 4 →
        (∀ n, rowConversion D P1 G1 Cg n ≤
          C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) →
        1 ≤ K →
        K * Real.exp (-((D.model.beta / 4) * D.deltaStep)) < 1 →
        Nonempty (ConstructedRowDefectLargeSeparation.Output
          D (rowConversion D P1 G1 Cg) K Cw) := by
  obtain ⟨y, yp, center, D, direction, Am, Hstar, Cw, hAm, -, hCw,
    -, -, hdir, hwidth, -, -⟩ :=
    ConstructedPulseWidth.exists_strict_sequence_and_uniform_width_of_eps
      heps heps10
  have hCw0 : 0 ≤ Cw := by
    rw [hCw]
    positivity
  refine ⟨D, direction, Cw, hCw0, hdir, ?_, ?_⟩
  · simpa only using hwidth
  · intro P1 G1 Cg C0 gamma K hC0 hgamma hgrowth hK hthreshold
    exact ConstructedRowDefectLargeSeparation.exists_output D
      (rowConversion D P1 G1 Cg)
      (fun n => c2ConstVar_nonneg _ _ _ _ _) hC0 hgamma hgrowth hK hCw0
      hthreshold

end ConfiguredVariableTerminalCapstone
