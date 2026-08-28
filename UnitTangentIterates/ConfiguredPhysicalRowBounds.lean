import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration
import UnitTangentIterates.ConfiguredInductiveTubeBudget

/-!
# Configured physical row bounds

Finite selected-inverse pullbacks do not have a common perimeter at fixed
row.  Their marked tail distance from the configured model instead gives
uniform lower and upper perimeter bounds, as well as the required physical
acceleration bound.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed
open UnconditionalAssembly TwoCapPairsAssembly

namespace ConfiguredPhysicalRowBounds

open RichFamilyPhysicalMarkingIntegration
open VariableMarkedTubeLocalStability
open VariableMarkedTube

/-- Weighted consecutive increments imply the marked row-radius estimate
used internally by the inductive tube proof.  This public form is useful for
all later geometric row bounds. -/
theorem pullback_dist_model_le_radius
    {B : Data → Data} {Q : ℕ → Data} {C K : ℝ} {d : ℕ → ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : ∀ n, Summable (fun k => K ^ k * d (n + k)))
    (hstep : ∀ n k,
      dist (TubePullbackLimit.pullback B Q n k)
          (TubePullbackLimit.pullback B Q n (k + 1)) ≤
        C * (K ^ k * d (n + k))) :
    ∀ n k, dist (Q n) (TubePullbackLimit.pullback B Q n k) ≤
      PullbackTubeTailBudget.radius C K d n := by
  intro n k
  have he0 : ∀ j, 0 ≤ C * (K ^ j * d (n + j)) := by
    intro j
    exact mul_nonneg hC (mul_nonneg (pow_nonneg hK j) (hd (n + j)))
  have hprefix : dist (Q n) (TubePullbackLimit.pullback B Q n k) ≤
      ∑ j ∈ Finset.range k, C * (K ^ j * d (n + j)) := by
    induction k with
    | zero => simp [TubePullbackLimit.pullback]
    | succ k ih =>
        calc
          dist (Q n) (TubePullbackLimit.pullback B Q n (k + 1)) ≤
              dist (Q n) (TubePullbackLimit.pullback B Q n k) +
                dist (TubePullbackLimit.pullback B Q n k)
                  (TubePullbackLimit.pullback B Q n (k + 1)) :=
            dist_triangle _ _ _
          _ ≤ (∑ j ∈ Finset.range k, C * (K ^ j * d (n + j))) +
                C * (K ^ k * d (n + k)) := add_le_add ih (hstep n k)
          _ = ∑ j ∈ Finset.range (k + 1), C * (K ^ j * d (n + j)) := by
            rw [Finset.sum_range_succ]
  have hs : Summable (fun j => C * (K ^ j * d (n + j))) :=
    (hsum n).mul_left C
  exact hprefix.trans (by
    simpa [PullbackTubeTailBudget.radius, ShadowingTails.tail] using
      hs.sum_le_tsum (Finset.range k) (fun j _ => he0 j))

/-- Two row-radius estimates with the same configured center give the direct
physical-to-terminal estimate needed for marking compactness. -/
theorem endpoint_dist_of_model_radii
    {Q : ℕ → Data} {B P : ℕ → ℕ → Data} {rB rP : ℕ → ℝ}
    (hB : ∀ n k, dist (Q n) (B n k) ≤ rB n)
    (hP : ∀ n k, dist (Q n) (P n k) ≤ rP n) :
    ∀ n k, dist (B n k) (P n k) ≤ rB n + rP n := by
  intro n k
  calc
    dist (B n k) (P n k) ≤ dist (B n k) (Q n) + dist (Q n) (P n k) :=
      dist_triangle _ _ _
    _ ≤ rB n + rP n :=
      add_le_add (by simpa [dist_comm] using hB n k) (hP n k)

/-- Shifted form matching a stage whose canonical physical rear is stored at
depth `k+1` while the terminal family is indexed by the stage number `k`. -/
theorem endpoint_dist_shifted_of_model_radii
    {Q : ℕ → Data} {B P : ℕ → ℕ → Data} {rB rP : ℕ → ℝ}
    (hB : ∀ n k, dist (Q n) (B n k) ≤ rB n)
    (hP : ∀ n k, dist (Q n) (P n k) ≤ rP n) :
    ∀ n k, dist (B n (k + 1)) (P n k) ≤ rB n + rP n := by
  intro n k
  calc
    dist (B n (k + 1)) (P n k) ≤
        dist (B n (k + 1)) (Q n) + dist (Q n) (P n k) :=
      dist_triangle _ _ _
    _ ≤ rB n + rP n :=
      add_le_add (by simpa [dist_comm] using hB n (k + 1)) (hP n k)

/-- Configured physical rows together with the aligned selected-rear
kinematics.  The only terminal-family input is its marked row-radius estimate
from the physical pullback. -/
structure Package
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (kh C K : ℝ) (d : ℕ → ℝ) (Q : ℕ → Data)
    (P : ℕ → ℕ → Data) (rend : ℕ → ℝ)
    (c dlt : ℝ) where
  bounds : PhysicalRowBounds
    (fun n k => TubePullbackLimit.pullback
      (SelectedInverseMap.selInv kh) Q n k) P c dlt
  finite : FinitePullbackPhysicalRearKinematics kh
    (fun n k => TubePullbackLimit.pullback
      (SelectedInverseMap.selInv kh) Q n k)
  c_pos : 0 < c

/-- The configured inductive budget discharges every physical field of
`PhysicalRowBounds`.  Perimeters are bounded by `c` below and by the model
perimeter plus the marked tail above; accelerations are bounded by the model
curvature ceiling plus the same tail. -/
def package_of_configured_inductive_budget
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    {kh C K : ℝ} {d : ℕ → ℝ} {Q : ℕ → Data}
    {P : ℕ → ℕ → Data} {rend rho : ℕ → ℝ}
    {c d0 dlt : ℝ}
    (hQperim : ∀ n, perim (Q n) = 2 * Hs n)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : ∀ n, Summable (fun k => K ^ k * d (n + k)))
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q C K d c d0 dlt
      (ConfiguredInductiveTubeBudget.accBound model) rho)
    (hstep : ∀ n k,
      dist (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k)
          (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n (k + 1)) ≤
        C * (K ^ k * d (n + k)))
    (hrend : ∀ n, 0 ≤ rend n)
    (hendpoint : ∀ n k,
      dist (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k)
        (P n k) ≤ rend n)
    (finite : FinitePullbackPhysicalRearKinematics kh
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k)) :
    Package model kh C K d Q P rend c dlt := by
  have htail : ∀ n k,
      dist (Q n) (TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) ≤
        PullbackTubeTailBudget.radius C K d n :=
    pullback_dist_model_le_radius hC hK hd hsum hstep
  refine ⟨?_, finite, R.c_pos⟩
  let rad : ℕ → ℝ := fun n => PullbackTubeTailBudget.radius C K d n
  let A : ℕ → ℝ := ConfiguredInductiveTubeBudget.accBound model
  refine
    { Lmin := fun _ => c
      Lmax := fun n => 2 * Hs n + rad n
      Ab := fun n => A n + rad n
      r := rend
      Lmin_pos := fun _ => R.c_pos
      Ab_nonneg := fun n => add_nonneg (R.acc_nonneg n) (R.radius_nonneg n)
      r_nonneg := hrend
      physical_tube := fun n k => R.pullback_mem_of_dist n k (htail n k)
      physical_perim_lower := ?_
      physical_perim_upper := ?_
      physical_acc := ?_
      endpoint_dist := hendpoint }
  · intro n k
    let Z := TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k
    have hZ := R.pullback_mem_of_dist n k (htail n k)
    calc
      c ≤ ‖Z.2.1 0‖ := hZ.speed_lb 0
      _ = perim Z := norm_vel_eq_perim hZ 0
  · intro n k
    let Z := TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k
    have habs : |perim Z - perim (Q n)| ≤ rad n := by
      exact (MarkedSpace.abs_perim_sub_le_dist Z (Q n)).trans (by
        simpa [Z, rad, dist_comm] using htail n k)
    have hle := (abs_le.mp habs).2
    rw [hQperim n] at hle
    change perim Z ≤ 2 * Hs n + rad n
    linarith
  · intro n k u
    let Z := TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k
    have hdiff : ‖Z.2.2 u - (Q n).2.2 u‖ ≤ rad n := by
      exact (dist_acc_apply_le Z (Q n) u).trans (by
        simpa [Z, rad, dist_comm] using htail n k)
    calc
      ‖Z.2.2 u‖ = ‖(Z.2.2 u - (Q n).2.2 u) + (Q n).2.2 u‖ := by ring
      _ ≤ ‖Z.2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := norm_add_le _ _
      _ ≤ rad n + A n := add_le_add hdiff (R.model_acc n u)
      _ = A n + rad n := add_comm _ _

/-- Configured package with the physical-to-terminal distance derived by
triangulating the two independently proved row tails through `Q n`. -/
def package_of_configured_model_and_terminal_tails
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    {kh C K : ℝ} {d : ℕ → ℝ} {Q : ℕ → Data}
    {P : ℕ → ℕ → Data} {rP rho : ℕ → ℝ}
    {c d0 dlt : ℝ}
    (hQperim : ∀ n, perim (Q n) = 2 * Hs n)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : ∀ n, Summable (fun k => K ^ k * d (n + k)))
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q C K d c d0 dlt
      (ConfiguredInductiveTubeBudget.accBound model) rho)
    (hstep : ∀ n k,
      dist (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k)
          (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n (k + 1)) ≤
        C * (K ^ k * d (n + k)))
    (hrP : ∀ n, 0 ≤ rP n)
    (hPtail : ∀ n k, dist (Q n) (P n k) ≤ rP n)
    (finite : FinitePullbackPhysicalRearKinematics kh
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k)) :
    Package model kh C K d Q P
      (fun n => PullbackTubeTailBudget.radius C K d n + rP n) c dlt := by
  have hBtail := pullback_dist_model_le_radius hC hK hd hsum hstep
  apply package_of_configured_inductive_budget model hQperim hC hK hd hsum R
    hstep
  · intro n
    exact add_nonneg (R.radius_nonneg n) (hrP n)
  · exact endpoint_dist_of_model_radii hBtail hPtail
  · exact finite

/-- All-row oriented representatives obtained directly from a configured
physical package and the normalized physical-to-terminal markings. -/
def orientedRepresentatives_of_package
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    {model : ConfiguredModelSequence kappas Hs eps}
    {kh C K : ℝ} {d : ℕ → ℝ} {Q : ℕ → Data}
    {P : ℕ → ℕ → Data} {rend Ct : ℕ → ℝ}
    {c dlt ct dt : ℝ}
    (Z : Package model kh C K d Q P rend c dlt)
    (M : DirectPhysicalTerminalMarkingFamily
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) P)
    (hct : 0 < ct) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hdlt : 0 < dlt)
    (hterminalTube : ∀ n k, IsVariableTubeMember ct (Ct n) 0 dt (P n k))
    {X Y : ℕ → Data}
    (hX : ∀ n, Tendsto
      (fun k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) atTop (nhds (X n)))
    (hY : ∀ n, Tendsto (P n) atTop (nhds (Y n))) :
    ∀ n, OrientedArclengthRepresentative (Y n) :=
  RichFamilyPhysicalMarkingIntegration.orientedRepresentativesDirect M Z.bounds
    hct hkh0 hkh1 Z.c_pos hdlt hterminalTube Z.finite hX hY

end ConfiguredPhysicalRowBounds
