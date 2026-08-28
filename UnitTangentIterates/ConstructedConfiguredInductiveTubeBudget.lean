import UnitTangentIterates.ConfiguredInductiveTubeBudget
import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.CanonicalConfiguredModelCapstone
import UnitTangentIterates.MainThresholds

/-!
# Constructed scalar budget for the local pullback induction

The canonical marked defect admits a row-uniform bound

`radius n <= T * exp (-beta * Hs n)`.

The configured sequence can be shifted beyond an arbitrary separation without
changing any analytic constant.  Since `H^2 exp (-beta H)` tends to zero, one
shift makes the row tail fit both the speed reserve and the chord reserve at
every row.  Thus the two scalar callbacks of
`ConfiguredInductiveTubeBudget` are discharged by the epsilon construction.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Real Filter CurvatureStabilityL1
open UnconditionalAssembly
open PathMetric.WeightedMarkedDefectThreshold

namespace ConstructedConfiguredInductiveTubeBudget

namespace WeightedData

open ConstructedConfiguredSequenceWeighted

/-- Discarding a finite prefix preserves all fields of the weighted configured
sequence, including the quantitative one-step separation bound. -/
def shift (D : Data) (N : ℕ) : Data := by
  have hmono : Monotone D.Hs :=
    monotone_nat_of_le_succ fun n =>
      (le_add_of_nonneg_right D.deltaStep_pos.le).trans (D.separation_step n)
  have hstep : ∀ n, D.Hs (N + n) + D.deltaStep ≤ D.Hs (N + (n + 1)) := by
    intro n
    simpa [Nat.add_assoc] using D.separation_step (N + n)
  have hlinear : ∀ n : ℕ,
      D.Hs (N + 0) + n * D.deltaStep ≤ D.Hs (N + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep n
        push_cast
        push_cast at ih
        nlinarith
  exact
    { kappas := fun n => D.kappas (N + n)
      Hs := fun n => D.Hs (N + n)
      deltaStep := D.deltaStep
      kd := D.kd
      kstar := D.kstar
      matchCoefficient := D.matchCoefficient
      beta := D.beta
      deltaStep_pos := D.deltaStep_pos
      beta_pos := D.beta_pos
      matchCoefficient_nonneg := D.matchCoefficient_nonneg
      kd_nonneg := D.kd_nonneg
      kstar_nonneg := D.kstar_nonneg
      separation_zero_pos := by simpa using D.model.separation_pos N
      separation_lower := fun n => by
        simpa using hmono (Nat.le_add_right N n)
      separation_linear := by simpa using hlinear
      separation_step := by simpa [Nat.add_assoc] using hstep
      model := by
        simpa using
          UnitTangentIterates.CanonicalConfiguredModelCapstone.shiftConfiguredModelSequence
            D.model N hmono
      model_kd := D.model_kd
      model_kstar := D.model_kstar
      model_KP_C2 := by
        intro n
        simpa using D.model_KP_C2 (N + n)
      model_kH_C2 := by
        intro n
        simpa using D.model_kH_C2 (N + n)
      phase := D.phase
      model_current_curvature_eq_next_shift := by
        intro n s
        simpa [Nat.add_assoc] using
          D.model_current_curvature_eq_next_shift (N + n) s
      model_curvature_pos := by
        intro n s
        simpa using D.model_curvature_pos (N + n) s }

@[simp] theorem shift_deltaStep (D : Data) (N : ℕ) :
    (shift D N).deltaStep = D.deltaStep := rfl

@[simp] theorem shift_beta (D : Data) (N : ℕ) :
    (shift D N).beta = D.beta := rfl

/-- Discarding a finite prefix preserves the actual front/rear half ceiling,
not only the coarse weighted data. -/
def shiftActualHalf (E : DataWithActualHalf) (N : ℕ) : DataWithActualHalf where
  data := shift E.data N
  steering_le_half := by
    simpa [shift] using E.steering_le_half
  front_le_half := by
    intro n s
    simpa [shift] using E.front_le_half (N + n) s
  rear_le_half := by
    intro n s
    simpa [shift] using E.rear_le_half (N + n) s

@[simp] theorem shiftActualHalf_data (E : DataWithActualHalf) (N : ℕ) :
    (shiftActualHalf E N).data = shift E.data N := rfl

/-- Every weighted configured sequence has a tail beginning beyond an arbitrary
scalar threshold. -/
theorem exists_shift_above (D : Data) (Hmin : ℝ) :
    ∃ N : ℕ, Hmin ≤ (shift D N).Hs 0 := by
  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_ge ((Hmin - D.Hs 0) / D.deltaStep)
  refine ⟨N, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hN D.deltaStep_pos.le
  rw [div_mul_cancel₀ _ D.deltaStep_pos.ne'] at hmul
  have hgrow := D.separation_linear N
  dsimp [shift]
  linarith

end WeightedData

/-- The separation-independent coefficient in the row-tail estimate. -/
def rowTailCoefficient
    (C K Cm kstar kd P0 beta deltaStep : ℝ) : ℝ :=
  C * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) * (1 + kstar) /
    (1 - K * Real.exp (-(beta * deltaStep)))

/-- Zeroth-row form of the canonical weighted-tail estimate, with an arbitrary
nonnegative path increment constant `C`. -/
theorem radius_zero_le_exp
    {C K Cm kstar kd P0 H0 beta deltaStep : ℝ} {Hs : ℕ → ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hCm : 0 ≤ Cm)
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hP0 : 0 < P0)
    (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1) :
    PullbackTubeTailBudget.radius C K
        (canonicalMarkedDefect Cm 1 kstar kd beta Hs) 0 ≤
      rowTailCoefficient C K Cm kstar kd P0 beta deltaStep *
        Real.exp (-(beta * H0)) := by
  let q : ℝ := Real.exp (-(beta * deltaStep))
  let A : ℝ := Real.sqrt (4 * kd * Cm) + 4 * Cm / P0
  let R : ℝ := K * q
  let d : ℕ → ℝ := canonicalMarkedDefect Cm 1 kstar kd beta Hs
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hR0 : 0 ≤ R := mul_nonneg hK hq0
  have hR1 : R < 1 := by simpa [R, q] using hthreshold
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg (by positivity) hP0.le)
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, canonicalMarkedDefect]
    exact mul_nonneg
      (mul_nonneg (l1Modulus_nonneg _ _ _) (sq_nonneg (1 : ℝ)))
      (by simpa using add_nonneg zero_le_one hkstar)
  have hexp : ∀ n : ℕ, Real.exp (-(beta * Hs (n + 1))) ≤
      Real.exp (-(beta * H0)) * q ^ n := by
    intro n
    have hs : Real.exp (-(beta * Hs (n + 1))) ≤
        Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep))) := by
      apply Real.exp_le_exp.mpr
      have h := hgrow (n + 1)
      push_cast at h
      nlinarith
    have heq : Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep))) =
        Real.exp (-(beta * H0)) * q ^ (n + 1) := by
      dsimp [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      congr 1
      ring
    have hq1 : q < 1 := by
      dsimp [q]
      exact Real.exp_lt_one_iff.mpr (by nlinarith)
    have hp : q ^ (n + 1) ≤ q ^ n := by
      rw [pow_succ]
      nlinarith [pow_nonneg hq0 n]
    exact hs.trans (heq.le.trans
      (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le))
  have hdgeo : ∀ n, d n ≤
      A * Real.exp (-(beta * H0)) * (1 + kstar) * q ^ n := by
    intro n
    have hmod := ModelOrbitDefectMarked.l1Modulus_le_exp
      (Cm := Cm) (kd := kd) (P0 := P0) (beta := 2 * beta)
      (Pp := Hs n) (H := Hs (n + 1))
      (by positivity) hCm hkd hP0 (hPle n)
      (le_trans hP0.le (hPle (n + 1)))
    have hmod' : l1Modulus (2 * kd)
        (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n) ≤
        A * Real.exp (-(beta * Hs (n + 1))) := by
      simpa [A] using hmod
    dsimp [d, canonicalMarkedDefect]
    calc
      l1Modulus (2 * kd)
            (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n) * 1 ^ 2 *
          (1 + kstar * 1)
          ≤ (A * Real.exp (-(beta * Hs (n + 1)))) * (1 + kstar) := by
            simpa using mul_le_mul_of_nonneg_right hmod' (by positivity)
      _ ≤ (A * (Real.exp (-(beta * H0)) * q ^ n)) * (1 + kstar) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hexp n) hA0) (by positivity)
      _ = A * Real.exp (-(beta * H0)) * (1 + kstar) * q ^ n := by ring
  have hactual : Summable (fun n => C * (K ^ n * d n)) := by
    have hs := summable_weighted_canonicalMarkedDefect
      hK hbeta hdelta hCm (by norm_num : 0 ≤ (1 : ℝ)) hkstar hkd hP0 hPle
      hgrow hthreshold
    simpa [d, PathMetric.WeightedRecursiveDefect.weightedDefect] using
      hs.mul_left C
  have hmajor : Summable (fun n : ℕ =>
      (C * (A * Real.exp (-(beta * H0)) * (1 + kstar))) * R ^ n) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left _
  have hterm : ∀ n, C * (K ^ n * d n) ≤
      (C * (A * Real.exp (-(beta * H0)) * (1 + kstar))) * R ^ n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hdgeo n) (pow_nonneg hK n)
    calc
      C * (K ^ n * d n) ≤ C * (K ^ n *
          (A * Real.exp (-(beta * H0)) * (1 + kstar) * q ^ n)) :=
        mul_le_mul_of_nonneg_left h hC
      _ = (C * (A * Real.exp (-(beta * H0)) * (1 + kstar))) * R ^ n := by
        dsimp [R]
        rw [mul_pow]
        ring
  have hsumle := hactual.tsum_le_tsum hterm hmajor
  have hgeom : (∑' n : ℕ,
      (C * (A * Real.exp (-(beta * H0)) * (1 + kstar))) * R ^ n) =
      C * (A * Real.exp (-(beta * H0)) * (1 + kstar)) / (1 - R) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1]
    rw [div_eq_mul_inv]
  dsimp [PullbackTubeTailBudget.radius, ShadowingTails.tail]
  simp only [zero_add]
  rw [hgeom] at hsumle
  calc
    ∑' n : ℕ, C * (K ^ n * canonicalMarkedDefect Cm 1 kstar kd beta Hs n)
        ≤ C * (A * Real.exp (-(beta * H0)) * (1 + kstar)) / (1 - R) := by
          simpa [d] using hsumle
    _ = rowTailCoefficient C K Cm kstar kd P0 beta deltaStep *
          Real.exp (-(beta * H0)) := by
          simp only [rowTailCoefficient, A, R, q]
          field_simp

/-- The same estimate at every row.  The one-step separation inequality is
used from the current row, rather than only from row zero. -/
theorem radius_le_row_exp
    {C K Cm kstar kd P0 beta deltaStep : ℝ} {Hs : ℕ → ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hCm : 0 ≤ Cm)
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hP0 : 0 < P0)
    (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hPle : ∀ n, P0 ≤ Hs n)
    (hstep : ∀ n, Hs n + deltaStep ≤ Hs (n + 1))
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1) (n : ℕ) :
    PullbackTubeTailBudget.radius C K
        (canonicalMarkedDefect Cm 1 kstar kd beta Hs) n ≤
      rowTailCoefficient C K Cm kstar kd P0 beta deltaStep *
        Real.exp (-(beta * Hs n)) := by
  let Hs' : ℕ → ℝ := fun k => Hs (n + k)
  have hPle' : ∀ k, P0 ≤ Hs' k := fun k => hPle (n + k)
  have hstep' : ∀ k, Hs' k + deltaStep ≤ Hs' (k + 1) := by
    intro k
    simpa [Hs', Nat.add_assoc] using hstep (n + k)
  have hlinear' : ∀ k : ℕ, Hs' 0 + k * deltaStep ≤ Hs' k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep' k
        push_cast
        push_cast at ih
        nlinarith
  have h := radius_zero_le_exp hC hK hCm hkstar hkd hP0 hbeta hdelta
    hPle' hlinear' hthreshold
  simpa [PullbackTubeTailBudget.radius, Hs', Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

/-- The floor-free chord constant is exactly the minimum of the speed-scale
branch and the curvature-scale branch. -/
theorem chordBase_eq_min
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hk : 0 < model.kstar) :
    ConfiguredInductiveTubeBudget.chordBase model =
      min (Hs 0) (Real.pi / (6 * model.kstar)) := by
  have hH : 0 ≤ Hs 0 := (model.separation_pos 0).le
  unfold ConfiguredInductiveTubeBudget.chordBase
    ConfiguredInductiveTubeBudget.chordCoeff
  rw [min_mul_of_nonneg _ _ (mul_nonneg (by norm_num) hH)]
  congr 1
  · ring
  · field_simp [hk.ne', (model.separation_pos 0).ne']
    ring

/-- Nonnegative configured curvature together with total turning `pi` forces
the retained upper curvature constant to be strictly positive. -/
theorem configured_kstar_pos
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps) :
    0 < model.kstar := by
  have hk0 : ∀ s, 0 ≤ kappas 0 s := by
    intro s
    rw [model.curvature_eq 0]
    exact (model.configs 0).KP_nonneg s
  by_contra hnot
  have hkle : model.kstar ≤ 0 := le_of_not_gt hnot
  have hzero : kappas 0 = 0 := by
    funext s
    exact le_antisymm ((model.curvature_upper 0 s).trans hkle) (hk0 s)
  have hturn := model.total_turning 0
  rw [hzero] at hturn
  have hz : (0 : ℝ) = Real.pi := by simpa using hturn
  exact Real.pi_ne_zero hz.symm

/-- **The constructed sequence admits the complete inductive tube budget after
discarding a finite prefix.**  No scalar smallness callback remains.  The only
transport restriction is the mathematically sharp weighted threshold
`K * exp (-beta * deltaStep) < 1`; in particular, `K <= 1` is not assumed. -/
theorem exists_shifted_inductiveTubeBudget
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (Hrequired : ℝ)
    {kh C K : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hthreshold : K * Real.exp (-(D.beta * D.deltaStep)) < 1) :
    ∃ (N : ℕ) (Q : ℕ → MarkedSpace.Data),
      Hrequired ≤ (WeightedData.shift D N).Hs 0 ∧
      (∀ n, MarkedSpace.perim (Q n) = 2 * (WeightedData.shift D N).Hs n ∧
        MarkedSpace.ev (Q n) = TwoCapPairsAssembly.front
          ((WeightedData.shift D N).kappas n)
          (WeightedData.shift D N).model.thetaBase
          ((WeightedData.shift D N).Hs n)) ∧
      PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
        (SelectedInverseMap.selInv kh) Q C K
        (canonicalMarkedDefect (WeightedData.shift D N).matchCoefficient 1
          (WeightedData.shift D N).kstar (WeightedData.shift D N).kd
          (WeightedData.shift D N).beta (WeightedData.shift D N).Hs)
        ((WeightedData.shift D N).Hs 0)
        (ConfiguredInductiveTubeBudget.chordBase
          (WeightedData.shift D N).model)
        (ConfiguredInductiveTubeBudget.chordBase
          (WeightedData.shift D N).model / 2)
        (ConfiguredInductiveTubeBudget.accBound
          (WeightedData.shift D N).model)
        (ConfiguredInductiveTubeBudget.rowRho
          (WeightedData.shift D N).model C K
          (canonicalMarkedDefect (WeightedData.shift D N).matchCoefficient 1
            (WeightedData.shift D N).kstar (WeightedData.shift D N).kd
            (WeightedData.shift D N).beta (WeightedData.shift D N).Hs)) := by
  let T : ℝ := rowTailCoefficient C K D.matchCoefficient D.kstar D.kd
    (D.Hs 0) D.beta D.deltaStep
  have hden : 0 < 1 - K * Real.exp (-(D.beta * D.deltaStep)) := by
    linarith
  have hT0 : 0 ≤ T := by
    dsimp [T, rowTailCoefficient]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hC (add_nonneg (Real.sqrt_nonneg _)
          (div_nonneg
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) D.matchCoefficient_nonneg)
            D.separation_zero_pos.le)))
        (add_nonneg zero_le_one D.kstar_nonneg)) hden.le
  have hkpos : 0 < D.model.kstar := configured_kstar_pos D.model
  let b0 : ℝ := min 1 (Real.pi / (6 * D.model.kstar))
  have hb0 : 0 < b0 := by
    dsimp [b0]
    exact lt_min zero_lt_one
      (div_pos Real.pi_pos (mul_pos (by norm_num) hkpos))
  let E : ℝ := 32 * D.model.kstar * T + 8 * T ^ 2
  have hE0 : 0 ≤ E := by
    dsimp [E]
    positivity
  have htail := MainThresholds.tendsto_tail_zero D.beta_pos
  have hTlim := htail.const_mul T
  have hElim := htail.const_mul E
  simp only [mul_zero] at hTlim hElim
  have htarget : 0 < min 1 (b0 / 8) := by
    exact lt_min zero_lt_one (div_pos hb0 (by norm_num))
  have hevT : ∀ᶠ H : ℝ in atTop,
      T * ((1 + H) ^ 2 * Real.exp (-D.beta * H)) < min 1 (b0 / 8) :=
    (tendsto_order.1 hTlim).2 _ htarget
  have hevE : ∀ᶠ H : ℝ in atTop,
      E * ((1 + H) ^ 2 * Real.exp (-D.beta * H)) < b0 :=
    (tendsto_order.1 hElim).2 _ hb0
  obtain ⟨HT, hHT⟩ := Filter.eventually_atTop.1 hevT
  obtain ⟨HE, hHE⟩ := Filter.eventually_atTop.1 hevE
  let Hmin : ℝ := max Hrequired (max 1 (max HT HE))
  obtain ⟨N, hN⟩ := WeightedData.exists_shift_above D Hmin
  let D' := WeightedData.shift D N
  have hstart : Hmin ≤ D'.Hs 0 := by simpa [D'] using hN
  have hrequired : Hrequired ≤ D'.Hs 0 :=
    (le_max_left Hrequired (max 1 (max HT HE))).trans hstart
  have hstart1 : 1 ≤ D'.Hs 0 :=
    (le_max_of_le_right (le_max_left 1 (max HT HE))).trans hstart
  have hstartT : HT ≤ D'.Hs 0 :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left HT HE))).trans hstart
  have hstartE : HE ≤ D'.Hs 0 :=
    (le_max_of_le_right (le_max_of_le_right (le_max_right HT HE))).trans hstart
  let d : ℕ → ℝ := canonicalMarkedDefect D'.matchCoefficient 1
    D'.kstar D'.kd D'.beta D'.Hs
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, canonicalMarkedDefect]
    exact mul_nonneg
      (mul_nonneg (l1Modulus_nonneg _ _ _) (sq_nonneg (1 : ℝ)))
      (by simpa using add_nonneg zero_le_one D'.kstar_nonneg)
  have hPle : ∀ n, D.Hs 0 ≤ D'.Hs n := by
    intro n
    exact D.separation_lower (N + n)
  have hrow : ∀ n, PullbackTubeTailBudget.radius C K d n ≤
      T * Real.exp (-D.beta * D'.Hs n) := by
    intro n
    have h := radius_le_row_exp
      (C := C) (K := K) (Cm := D.matchCoefficient) (kstar := D.kstar)
      (kd := D.kd) (P0 := D.Hs 0) (beta := D.beta)
      (deltaStep := D.deltaStep) (Hs := D'.Hs)
      hC hK D.matchCoefficient_nonneg D.kstar_nonneg D.kd_nonneg
      D.separation_zero_pos D.beta_pos D.deltaStep_pos hPle
      D'.separation_step hthreshold n
    simpa [d, D', T, neg_mul] using h
  have hlarge : ∀ n, 1 ≤ D'.Hs n := fun n =>
    hstart1.trans (D'.separation_lower n)
  have hsmallT : ∀ n,
      T * ((1 + D'.Hs n) ^ 2 * Real.exp (-D.beta * D'.Hs n)) <
        min 1 (b0 / 8) := fun n =>
    hHT _ (hstartT.trans (D'.separation_lower n))
  have hsmallE : ∀ n,
      E * ((1 + D'.Hs n) ^ 2 * Real.exp (-D.beta * D'.Hs n)) < b0 :=
    fun n => hHE _ (hstartE.trans (D'.separation_lower n))
  have hexp1 : ∀ n, Real.exp (-D.beta * D'.Hs n) ≤ 1 := by
    intro n
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr D.beta_pos.le)
        (le_trans zero_le_one (hlarge n)))
  have htail_le_poly : ∀ n,
      T * Real.exp (-D.beta * D'.Hs n) ≤
        T * ((1 + D'.Hs n) ^ 2 * Real.exp (-D.beta * D'.Hs n)) := by
    intro n
    apply mul_le_mul_of_nonneg_left _ hT0
    have hsquare : 1 ≤ (1 + D'.Hs n) ^ 2 := by
      nlinarith [hlarge n]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hsquare
  have hspeed : ∀ n, PullbackTubeTailBudget.radius C K d n ≤ D'.Hs 0 := by
    intro n
    have hpoly := htail_le_poly n
    have hs := hsmallT n
    have hone : min 1 (b0 / 8) ≤ 1 := min_le_left _ _
    exact (hrow n).trans (hpoly.trans (le_trans hs.le (hone.trans hstart1)))
  have hbaseLower : b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model := by
    rw [chordBase_eq_min D'.model (configured_kstar_pos D'.model)]
    apply min_le_min
    · exact hstart1
    · exact le_rfl
  have hradius0 : ∀ n, 0 ≤ PullbackTubeTailBudget.radius C K d n := by
    intro n
    apply ShadowingTails.tail_nonneg
    intro k
    exact mul_nonneg hC (mul_nonneg (pow_nonneg hK k) (hd0 (n + k)))
  have hchord : ∀ n,
      2 * PullbackTubeTailBudget.radius C K d n ≤
        (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) *
          ConfiguredInductiveTubeBudget.rowRho D'.model C K d n := by
    intro n
    let r := PullbackTubeTailBudget.radius C K d n
    let H := D'.Hs n
    let A := ConfiguredInductiveTubeBudget.accBound D'.model n
    have hr0 : 0 ≤ r := hradius0 n
    have hH1 : 1 ≤ H := hlarge n
    have he0 : 0 < Real.exp (-D.beta * H) := Real.exp_pos _
    have hrT : r ≤ T * Real.exp (-D.beta * H) := hrow n
    have hrSmall : r ≤ b0 / 8 := by
      exact hrT.trans ((htail_le_poly n).trans
        ((hsmallT n).le.trans (min_le_right _ _)))
    have hAeq : A = 4 * D'.model.kstar * H ^ 2 := by
      simp [A, H, ConfiguredInductiveTubeBudget.accBound]
      ring
    have hk' : D'.model.kstar = D.model.kstar := rfl
    have hA0 : 0 ≤ A := by rw [hAeq]; positivity
    have hpoly : H ^ 2 ≤ (1 + H) ^ 2 := by nlinarith [hH1]
    have he1 : Real.exp (-D.beta * H) ≤ 1 := by simpa [H] using hexp1 n
    have he_sq : Real.exp (-D.beta * H) ^ 2 ≤
        (1 + H) ^ 2 * Real.exp (-D.beta * H) := by
      calc
        Real.exp (-D.beta * H) ^ 2 ≤ Real.exp (-D.beta * H) := by
          nlinarith [he0.le, he1]
        _ ≤ (1 + H) ^ 2 * Real.exp (-D.beta * H) :=
          le_mul_of_one_le_left he0.le (by nlinarith [hH1])
    have hHexp : H ^ 2 * Real.exp (-D.beta * H) ≤
        (1 + H) ^ 2 * Real.exp (-D.beta * H) :=
      mul_le_mul_of_nonneg_right hpoly he0.le
    have hprod : 8 * r * (A + r) ≤
        ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := by
      have hfirst : 8 * r * (A + r) ≤
          8 * (T * Real.exp (-D.beta * H)) *
            (A + T * Real.exp (-D.beta * H)) := by
        have hm := mul_le_mul hrT (add_le_add_left hrT A)
          (add_nonneg hr0 hA0)
          (mul_nonneg hT0 he0.le)
        calc
          8 * r * (A + r) = 8 * (r * (r + A)) := by ring
          _ ≤ 8 * ((T * Real.exp (-D.beta * H)) *
              (T * Real.exp (-D.beta * H) + A)) :=
            mul_le_mul_of_nonneg_left hm (by norm_num)
          _ = 8 * (T * Real.exp (-D.beta * H)) *
              (A + T * Real.exp (-D.beta * H)) := by ring
      have hmajor :
          8 * (T * Real.exp (-D.beta * H)) *
              (A + T * Real.exp (-D.beta * H)) ≤
            E * ((1 + H) ^ 2 * Real.exp (-D.beta * H)) := by
        rw [hAeq, hk']
        have h1 := mul_le_mul_of_nonneg_left hHexp
          (mul_nonneg
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hkpos.le) hT0)
        have h2 := mul_le_mul_of_nonneg_left he_sq
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg T))
        dsimp [E]
        nlinarith
      have hb : E * ((1 + H) ^ 2 * Real.exp (-D.beta * H)) ≤ b0 :=
        (hsmallE n).le
      have hbH : b0 ≤
          ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := by
        calc
          b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model := hbaseLower
          _ ≤ ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 :=
            le_mul_of_one_le_right
              (le_trans hb0.le hbaseLower) hstart1
      exact hfirst.trans (hmajor.trans (hb.trans hbH))
    unfold ConfiguredInductiveTubeBudget.rowRho
    by_cases hbranch : (1 / 2 : ℝ) ≤
        D'.Hs 0 / (2 * (ConfiguredInductiveTubeBudget.accBound D'.model n + r))
    · rw [min_eq_left hbranch]
      have := hbaseLower
      dsimp [r] at hrSmall ⊢
      nlinarith
    · rw [min_eq_right (le_of_not_ge hbranch)]
      have hApos : 0 < A := by
        rw [hAeq]
        exact mul_pos (mul_pos (by norm_num) hkpos) (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hH1))
      have hdenpos : 0 < 2 * (A + r) :=
        mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hApos hr0)
      have heq :
          (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) *
              (D'.Hs 0 / (2 * (A + r))) =
            ((ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0) /
              (2 * (A + r)) := by ring
      rw [show ConfiguredInductiveTubeBudget.accBound D'.model n = A from rfl, heq]
      rw [le_div_iff₀ hdenpos]
      change 2 * r * (2 * (A + r)) ≤
        (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0
      calc
        2 * r * (2 * (A + r)) = (8 * r * (A + r)) / 2 := by ring
        _ ≤ (ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0) / 2 :=
          div_le_div_of_nonneg_right hprod (by norm_num)
        _ = (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0 := by
          ring
  obtain ⟨Q, hQ, hbudget⟩ :=
    ConfiguredInductiveTubeBudget.exists_budget_of_strict_configuredModelSequence
      D'.model hkh0 hkh1 hC hK hd0 hspeed hchord
  exact ⟨N, Q, by simpa [D'] using hrequired,
    by simpa [D'] using hQ, by simpa [D', d] using hbudget⟩

/-- Epsilon-level entry point.  It returns one retained constructed datum; for
every admissible transport factor and path constant, a finite tail of that
same datum carries the complete inductive tube budget. -/
theorem exists_eventually_budgeted_data_of_eps {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ D : ConstructedConfiguredSequenceWeighted.Data,
      ∀ {kh C K : ℝ}, 0 ≤ kh → kh < 1 → 0 ≤ C → 0 ≤ K →
        K * Real.exp (-(D.beta * D.deltaStep)) < 1 →
        ∃ (N : ℕ) (Q : ℕ → MarkedSpace.Data),
          PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
            (SelectedInverseMap.selInv kh) Q C K
            (canonicalMarkedDefect (WeightedData.shift D N).matchCoefficient 1
              (WeightedData.shift D N).kstar (WeightedData.shift D N).kd
              (WeightedData.shift D N).beta (WeightedData.shift D N).Hs)
            ((WeightedData.shift D N).Hs 0)
            (ConfiguredInductiveTubeBudget.chordBase (WeightedData.shift D N).model)
            (ConfiguredInductiveTubeBudget.chordBase (WeightedData.shift D N).model / 2)
            (ConfiguredInductiveTubeBudget.accBound (WeightedData.shift D N).model)
            (ConfiguredInductiveTubeBudget.rowRho (WeightedData.shift D N).model C K
              (canonicalMarkedDefect (WeightedData.shift D N).matchCoefficient 1
                (WeightedData.shift D N).kstar (WeightedData.shift D N).kd
                (WeightedData.shift D N).beta (WeightedData.shift D N).Hs)) := by
  obtain ⟨D⟩ := ConstructedConfiguredSequenceWeighted.exists_data_of_eps heps heps10
  refine ⟨D, ?_⟩
  intro kh C K hkh0 hkh1 hC hK hthreshold
  obtain ⟨N, Q, -, -, hbudget⟩ :=
    exists_shifted_inductiveTubeBudget D 0 hkh0 hkh1 hC hK hthreshold
  exact ⟨N, Q, hbudget⟩

end ConstructedConfiguredInductiveTubeBudget
