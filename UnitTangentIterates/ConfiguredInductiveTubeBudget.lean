import UnitTangentIterates.InductiveLocalPullbackTube
import UnitTangentIterates.SelectedInverseWeakTube
import UnitTangentIterates.ModelChordScaled
import UnitTangentIterates.TwoCapModelOrbit
import UnitTangentIterates.CurvatureFromMarkedDistance

/-!
# Configured model constructor for the inductive tube budget

The configured model sequence constructs the marked fronts, their strict speed
margin, a uniform floor-free chord constant, and an explicit acceleration
bound.  Zero-margin structure of every selected-inverse pullback follows from
`SelectedInverseMap.pullback_selInv_weak_mem`.  The row radius is paired with
an explicit `rho`; only the two genuine tail-smallness comparisons remain.
-/

noncomputable section

open Set Function Real MarkedSpace
open UnconditionalAssembly TwoCapPairsAssembly

namespace ConfiguredInductiveTubeBudget

def chordCoeff {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps) : ℝ :=
  min (1 / 2) (Real.pi / (12 * model.kstar * Hs 0))

def chordBase {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps) : ℝ :=
  chordCoeff model * (2 * Hs 0)

def accBound {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps) (n : ℕ) : ℝ :=
  (2 * Hs n) ^ 2 * model.kstar

def rowRho {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (C K : ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (1 / 2)
    (Hs 0 / (2 * (accBound model n +
      PullbackTubeTailBudget.radius C K d n)))

/-- Construct the entire inductive budget from a configured model sequence.
Nonnegative curvature is already part of every retained paper configuration,
and total turning `pi` forces the uniform upper bound `kstar` to be positive.
The two residual inequalities say respectively that the weighted
row tail fits inside the model speed reserve and inside the chord reserve at
the explicit local scale `rowRho`. -/
theorem exists_budget_of_strict_configuredModelSequence
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    {kh C K : ℝ} {d : ℕ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hspeedTail : ∀ n,
      PullbackTubeTailBudget.radius C K d n ≤ Hs 0)
    (hchordTail : ∀ n,
      2 * PullbackTubeTailBudget.radius C K d n ≤
        (chordBase model / 2) * rowRho model C K d n) :
    ∃ Q : ℕ → Data,
      (∀ n, perim (Q n) = 2 * Hs n ∧
        ev (Q n) = front (kappas n) model.thetaBase (Hs n)) ∧
      PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
        (SelectedInverseMap.selInv kh) Q C K d
        (Hs 0) (chordBase model) (chordBase model / 2)
        (accBound model) (rowRho model C K d) := by
  have hH : ∀ n, 0 < Hs n := model.separation_pos
  have hk0 : ∀ n s, 0 ≤ kappas n s := by
    intro n s
    rw [model.curvature_eq n]
    exact (model.configs n).KP_nonneg s
  have hkap0 : 0 < model.kstar := by
    by_contra hnot
    have hkle : model.kstar ≤ 0 := le_of_not_gt hnot
    have hzero : kappas 0 = 0 := by
      funext s
      exact le_antisymm ((model.curvature_upper 0 s).trans hkle) (hk0 0 s)
    have hturn := model.total_turning 0
    rw [hzero] at hturn
    have hz : (0 : ℝ) = Real.pi := by simpa using hturn
    exact Real.pi_ne_zero hz.symm
  have hcoeff0 : 0 < chordCoeff model := by
    dsimp [chordCoeff]
    apply lt_min
    · norm_num
    · exact div_pos Real.pi_pos
        (mul_pos (mul_pos (by norm_num) hkap0) (hH 0))
  have hbase0 : 0 < chordBase model := by
    exact mul_pos hcoeff0 (mul_pos (by norm_num) (hH 0))
  have hchord := chord_arc_front_scaled
    (theta0 := fun _ => model.thetaBase)
    hH model.separation_mono model.curvature_continuous model.curvature_periodic
    model.total_turning hk0 model.curvature_upper hkap0
  obtain ⟨Q, hQ⟩ := TwoCapModelOrbit.exists_model_orbit
    (theta0 := fun _ => model.thetaBase)
    hH model.separation_mono model.curvature_continuous model.curvature_periodic
    hk0 model.curvature_upper model.total_turning hchord
  have hQweak : ∀ n, IsTubeMember 0 0 0 (Q n) := by
    intro n
    exact (hQ n).1.mono (mul_nonneg (by norm_num) (hH 0).le) hbase0.le
  have hweak : ∀ n k, IsTubeMember 0 0 0
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k) :=
    SelectedInverseMap.pullback_selInv_weak_mem hkh0 hkh1 hQweak
  have hradius0 : ∀ n, 0 ≤ PullbackTubeTailBudget.radius C K d n := by
    intro n
    apply ShadowingTails.tail_nonneg
    intro k
    exact mul_nonneg hC (mul_nonneg (pow_nonneg hK k) (hd (n + k)))
  have hacc0 : ∀ n, 0 < accBound model n := by
    intro n
    exact mul_pos (sq_pos_of_pos (mul_pos (by norm_num) (hH n))) hkap0
  have hrho0 : ∀ n, 0 < rowRho model C K d n := by
    intro n
    dsimp [rowRho]
    apply lt_min
    · norm_num
    · exact div_pos (hH 0) (mul_pos (by norm_num)
        (add_pos_of_pos_of_nonneg (hacc0 n) (hradius0 n)))
  have hrhoHalf : ∀ n, rowRho model C K d n ≤ 1 / 2 := by
    intro n
    exact min_le_left _ _
  have haccRadius : ∀ n,
      (accBound model n + PullbackTubeTailBudget.radius C K d n) *
          rowRho model C K d n ≤ Hs 0 / 2 := by
    intro n
    have hsumpos : 0 < accBound model n +
        PullbackTubeTailBudget.radius C K d n :=
      add_pos_of_pos_of_nonneg (hacc0 n) (hradius0 n)
    have hr := min_le_right (1 / 2 : ℝ)
      (Hs 0 / (2 * (accBound model n +
        PullbackTubeTailBudget.radius C K d n)))
    have hm := mul_le_mul_of_nonneg_left hr hsumpos.le
    simpa [rowRho] using hm.trans_eq (by field_simp)
  have hbase_le_H : chordBase model ≤ Hs 0 := by
    have hc := min_le_left (1 / 2 : ℝ)
      (Real.pi / (12 * model.kstar * Hs 0))
    dsimp [chordBase, chordCoeff]
    nlinarith [hH 0]
  have hmodelMem : ∀ n, IsTubeMember
      (Hs 0 + PullbackTubeTailBudget.radius C K d n) 0
      (chordBase model) (Q n) := by
    intro n
    apply (hQ n).1.mono
    · linarith [hspeedTail n]
    · exact le_rfl
  have hmodelAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ accBound model n := by
    intro n u
    have hp := (hQ n).1
    have hL : perim (Q n) = 2 * Hs n := (hQ n).2.1
    have hv : ‖(Q n).2.1 u‖ = 2 * Hs n := by
      rw [norm_vel_eq_perim hp u, hL]
    have hvpos : 0 < ‖(Q n).2.1 u‖ := by
      rw [hv]
      exact mul_pos (by norm_num) (hH n)
    have hcurv0 : 0 ≤ CurvatureFromMarkedDistance.dataCurv (Q n) u := by
      unfold CurvatureFromMarkedDistance.dataCurv
      exact div_nonneg (by simpa using hp.curv_lb u) (pow_nonneg (norm_nonneg _) 3)
    have hcurvle : CurvatureFromMarkedDistance.dataCurv (Q n) u ≤ model.kstar := by
      unfold CurvatureFromMarkedDistance.dataCurv
      rw [div_le_iff₀ (pow_pos hvpos 3)]
      exact (hQ n).2.2.2 u
    rw [CurvatureFromMarkedDistance.norm_acc_eq hp hvpos,
      abs_of_nonneg hcurv0, hv]
    calc
      CurvatureFromMarkedDistance.dataCurv (Q n) u * (2 * Hs n) ^ 2 ≤
          model.kstar * (2 * Hs n) ^ 2 :=
        mul_le_mul_of_nonneg_right hcurvle (sq_nonneg (2 * Hs n))
      _ = accBound model n := by simp [accBound, mul_comm]
  refine ⟨Q, fun n => ⟨(hQ n).2.1, (hQ n).2.2.1⟩, ?_⟩
  exact
    { c_pos := hH 0
      radius_nonneg := hradius0
      model_mem := hmodelMem
      weak_mem := hweak
      model_acc := hmodelAcc
      acc_nonneg := fun n => (hacc0 n).le
      rho_pos := hrho0
      rho_half := hrhoHalf
      acc_radius := haccRadius
      chord_nonneg := div_nonneg hbase0.le (by norm_num)
      chord_speed := by nlinarith [hbase_le_H]
      chord_margin := by
        intro n
        have := hchordTail n
        convert this using 1 <;> ring }

end ConfiguredInductiveTubeBudget
