import Mathlib
import UnitTangentIterates.PinchedPathPiece

/-!
# From the local estimate to a global Lipschitz bound

`SelInvLipUniversal.dist_selInv_le_lipUniversal_cost` compares the selected
inverses of the two ends of an admissible path only when the cost of the path is
below two explicit thresholds; the pinched pseudometric of
`PinchedPathMetric.lean` inherits that restriction
(`dist_selInv_le_pinchedDist` asks the distance to be small).

The restriction is removed here by subdividing the path.  An admissible path
restricted to a subinterval of its time is again an admissible path
(`PinchedPathPiece.piece`), joining the two slice data of
`PinchedSliceData.lean`, and the costs of the pieces of a partition add up to
the cost of the path.  Applying the local estimate to each piece of a uniform
partition fine enough for the two thresholds, and chaining the triangle
inequality of the marked metric, gives

`dist (selInv κ̂ q) (selInv κ̂ p) ≤ L · cost Γ`

for *every* admissible path, hence

`dist (selInv κ̂ q) (selInv κ̂ p) ≤ L · pinchedDist κ̂ p q`

with no smallness condition (`dist_selInv_le_pinchedDist_uniformLip`).  What the
statement asks in exchange is a bound `L`, valid for all admissible curves, for
the universal Lipschitz constant of the estimate — whose two arguments are the
perimeters of the two images, and hence vary with the pair.

Main results: `dist_selInv_le_cost_uniformLip`,
`dist_selInv_le_pinchedDist_uniformLip`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist
  RearJacobiSourceCost SelInvLipUniversal GaugeMarkedDataOfRearFamily

variable {kminP kh khat L : ℝ} {p q : Data}

/-- The uniform partition of the time interval of a path. -/
def partTime (T : ℝ) (N i : ℕ) : ℝ := T * i / N

theorem partTime_zero (T : ℝ) (N : ℕ) : partTime T N 0 = 0 := by simp [partTime]

theorem partTime_last {T : ℝ} {N : ℕ} (hN : 0 < N) : partTime T N N = T := by
  have hne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [partTime, mul_div_assoc, div_self hne, mul_one]

theorem partTime_mono {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) {i j : ℕ} (hij : i ≤ j) :
    partTime T N i ≤ partTime T N j := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  rw [partTime, partTime, div_le_div_iff_of_pos_right hNpos]
  exact mul_le_mul_of_nonneg_left this hT.le

theorem partTime_lt {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) (i : ℕ) :
    partTime T N i < partTime T N (i + 1) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hlt : (i : ℝ) < (i + 1 : ℕ) := by push_cast; linarith
  rw [partTime, partTime, div_lt_div_iff_of_pos_right hNpos]
  exact mul_lt_mul_of_pos_left hlt hT

theorem partTime_sub {T : ℝ} {N : ℕ} (hN : 0 < N) (i : ℕ) :
    partTime T N (i + 1) - partTime T N i = T / N := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [partTime, partTime, div_sub_div_same]
  push_cast
  rw [show T * ((i : ℝ) + 1) - T * i = T by ring]

/-- **The global estimate along one admissible path.**  Subdividing the path
finely enough, the local estimate applies to each piece, and the triangle
inequality adds the pieces up. -/
theorem dist_selInv_le_cost_uniformLip (Γ : NormalPath p q)
    (hΓ : IsPinchedPath kminP kh Γ)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP) (hkhat : rearKappa1 kh ≤ khat)
    (hL : ∀ a b : Data, IsPinchedCurve kminP kh a → IsPinchedCurve kminP kh b →
      (∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) → (∀ u, HasDerivAt (⇑b.1) (b.2.1 u) u) →
      selInvLipUniversal kminP kh khat (perim (SelectedInverseMap.selInv kh a))
        (perim (SelectedInverseMap.selInv kh b)) ≤ L) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p) ≤ L * cost Γ := by
  set C : ℝ := selInvCostConstUniversal kminP kh khat with hCdef
  -- a bound for the cost density on the time interval
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Γ.T)).exists_bound_of_continuousOn
    Γ.cont_m.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, Γ.T_pos.le⟩)
  -- a partition fine enough for the two smallness thresholds
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((M * Γ.T) * (1 + |C|) + 1)
  have hNpos : 0 < N := by
    by_contra hcon
    push_neg at hcon
    interval_cases N
    · simp at hNgt
      nlinarith [abs_nonneg C, mul_nonneg hM0 Γ.T_pos.le]
  have hNR : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  set tt : ℕ → ℝ := fun i => partTime Γ.T N i with htt
  have htt0 : tt 0 = 0 := partTime_zero _ _
  have httN : tt N = Γ.T := partTime_last hNpos
  have httlt : ∀ i, tt i < tt (i + 1) := fun i => partTime_lt Γ.T_pos hNpos i
  have httmem : ∀ i ≤ N, tt i ∈ Icc (0 : ℝ) Γ.T := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← htt0]; exact partTime_mono Γ.T_pos hNpos (Nat.zero_le i)
    · rw [← httN]; exact partTime_mono Γ.T_pos hNpos hi
  -- the marked data of the partition
  set f : ℕ → Data := fun i => pinchedSliceData hΓ (tt i) with hf
  have hf0 : f 0 = p := by rw [hf]; simp only [htt0]; exact pinchedSliceData_zero hΓ hpd hpd2
  have hfN : f N = q := by rw [hf]; simp only [httN]; exact pinchedSliceData_final hΓ hqd hqd2
  -- the cost of the piece between two consecutive times
  have hcost_piece : ∀ i, cost (piece hΓ (httlt i)) = ∫ s in (tt i)..(tt (i + 1)), Γ.m s :=
    fun i => cost_piece hΓ (httlt i)
  have hcost_nonneg : ∀ i, 0 ≤ cost (piece hΓ (httlt i)) := fun i => (piece hΓ (httlt i)).cost_nonneg
  have hcost_le : ∀ i < N, cost (piece hΓ (httlt i)) ≤ M * (Γ.T / N) := by
    intro i hi
    have hsub : ∀ s ∈ uIoc (tt i) (tt (i + 1)), ‖Γ.m s‖ ≤ M := by
      intro s hs
      rw [uIoc_of_le (httlt i).le] at hs
      have h1 : (0 : ℝ) ≤ s := lt_of_le_of_lt (httmem i (le_of_lt hi)).1 hs.1 |>.le
      have h2 : s ≤ Γ.T := le_trans hs.2 (httmem (i + 1) hi).2
      exact hM s ⟨h1, h2⟩
    have hnorm : ‖∫ s in (tt i)..(tt (i + 1)), Γ.m s‖ ≤ M * |tt (i + 1) - tt i| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hsub
    rw [hcost_piece i]
    calc ∫ s in (tt i)..(tt (i + 1)), Γ.m s ≤ ‖∫ s in (tt i)..(tt (i + 1)), Γ.m s‖ :=
          le_abs_self _
      _ ≤ M * |tt (i + 1) - tt i| := hnorm
      _ = M * (Γ.T / N) := by
          rw [partTime_sub hNpos i, abs_of_nonneg (div_nonneg Γ.T_pos.le hNR.le)]
  have hfine : M * (Γ.T / N) ≤ 1 / (1 + |C|) := by
    have habs : (0 : ℝ) < 1 + |C| := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hNR habs]
    have h1 : M * Γ.T * (1 + |C|) + 1 < N := hNgt
    nlinarith
  have hcost1 : ∀ i < N, cost (piece hΓ (httlt i)) ≤ 1 := by
    intro i hi
    have habs : (0 : ℝ) < 1 + |C| := by positivity
    have h1 : (1 : ℝ) / (1 + |C|) ≤ 1 := by
      rw [div_le_one habs]; linarith [abs_nonneg C]
    exact le_trans (le_trans (hcost_le i hi) hfine) h1
  have hsmall : ∀ i < N, C * cost (piece hΓ (httlt i)) ≤ 1 := by
    intro i hi
    have habs : (0 : ℝ) < 1 + |C| := by positivity
    have hc : cost (piece hΓ (httlt i)) ≤ 1 / (1 + |C|) :=
      le_trans (hcost_le i hi) hfine
    have hC : C ≤ |C| := le_abs_self C
    have hstep : C * cost (piece hΓ (httlt i)) ≤ |C| * (1 / (1 + |C|)) := by
      rcases le_or_gt C 0 with hCneg | hCpos
      · have : C * cost (piece hΓ (httlt i)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hCneg (hcost_nonneg i)
        have : (0 : ℝ) ≤ |C| * (1 / (1 + |C|)) := by positivity
        linarith [this, mul_nonpos_of_nonpos_of_nonneg hCneg (hcost_nonneg i)]
      · exact mul_le_mul hC hc (hcost_nonneg i) (abs_nonneg C)
    have hfin : |C| * (1 / (1 + |C|)) ≤ 1 := by
      rw [mul_one_div, div_le_one habs]; linarith
    linarith
  -- the local estimate on each piece
  have hstep : ∀ i < N, dist (SelectedInverseMap.selInv kh (f i))
      (SelectedInverseMap.selInv kh (f (i + 1))) ≤ L * cost (piece hΓ (httlt i)) := by
    intro i hi
    have hP := isPinchedPath_piece hΓ (httlt i)
    have hbound := dist_selInv_le_lipUniversal_cost (piece hΓ (httlt i))
      (fun u => hasDerivAt_pinchedSliceData hΓ (tt i) u)
      (fun u => hasDerivAt_pinchedSliceData' hΓ (tt i) u)
      (fun u => hasDerivAt_pinchedSliceData hΓ (tt (i + 1)) u)
      (fun u => hasDerivAt_pinchedSliceData' hΓ (tt (i + 1)) u)
      hkh1 hP.smooth hP.speed hP.per hP.normal hkminP hP.kmin hP.kmax hP.short hP.slit
      hP.rest (hcost1 i hi) hkhat (hsmall i hi)
    have hLi : selInvLipUniversal kminP kh khat
        (perim (SelectedInverseMap.selInv kh (f i)))
        (perim (SelectedInverseMap.selInv kh (f (i + 1)))) ≤ L :=
      hL _ _ (isPinchedCurve_pinchedSliceData hΓ (tt i))
        (isPinchedCurve_pinchedSliceData hΓ (tt (i + 1)))
        (fun u => hasDerivAt_pinchedSliceData hΓ (tt i) u)
        (fun u => hasDerivAt_pinchedSliceData hΓ (tt (i + 1)) u)
    have hmul : selInvLipUniversal kminP kh khat
        (perim (SelectedInverseMap.selInv kh (f i)))
        (perim (SelectedInverseMap.selInv kh (f (i + 1)))) * cost (piece hΓ (httlt i))
          ≤ L * cost (piece hΓ (httlt i)) :=
      mul_le_mul_of_nonneg_right hLi (hcost_nonneg i)
    rw [dist_comm]
    exact le_trans hbound hmul
  -- chaining
  have hchain : dist (SelectedInverseMap.selInv kh (f 0)) (SelectedInverseMap.selInv kh (f N))
      ≤ ∑ i ∈ Finset.range N, dist (SelectedInverseMap.selInv kh (f i))
          (SelectedInverseMap.selInv kh (f (i + 1))) :=
    dist_le_range_sum_dist (fun i => SelectedInverseMap.selInv kh (f i)) N
  have hsum_le : ∑ i ∈ Finset.range N, dist (SelectedInverseMap.selInv kh (f i))
      (SelectedInverseMap.selInv kh (f (i + 1)))
      ≤ ∑ i ∈ Finset.range N, L * cost (piece hΓ (httlt i)) :=
    Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.1 hi))
  have hcosts : ∑ i ∈ Finset.range N, cost (piece hΓ (httlt i)) = cost Γ := by
    have hadj : ∑ i ∈ Finset.range N, (∫ s in (tt i)..(tt (i + 1)), Γ.m s)
        = ∫ s in (tt 0)..(tt N), Γ.m s :=
      intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => Γ.cont_m.intervalIntegrable _ _)
    calc ∑ i ∈ Finset.range N, cost (piece hΓ (httlt i))
        = ∑ i ∈ Finset.range N, ∫ s in (tt i)..(tt (i + 1)), Γ.m s :=
          Finset.sum_congr rfl (fun i _ => hcost_piece i)
      _ = ∫ s in (tt 0)..(tt N), Γ.m s := hadj
      _ = cost Γ := by rw [htt0, httN]; rfl
  have hfinal : ∑ i ∈ Finset.range N, L * cost (piece hΓ (httlt i)) = L * cost Γ := by
    rw [← Finset.mul_sum, hcosts]
  have hres : dist (SelectedInverseMap.selInv kh (f 0)) (SelectedInverseMap.selInv kh (f N))
      ≤ L * cost Γ :=
    calc dist (SelectedInverseMap.selInv kh (f 0)) (SelectedInverseMap.selInv kh (f N))
        ≤ ∑ i ∈ Finset.range N, dist (SelectedInverseMap.selInv kh (f i))
            (SelectedInverseMap.selInv kh (f (i + 1))) := hchain
      _ ≤ ∑ i ∈ Finset.range N, L * cost (piece hΓ (httlt i)) := hsum_le
      _ = L * cost Γ := hfinal
  rw [hf0, hfN] at hres
  rw [dist_comm]
  exact hres

/-- **The selected inverse is globally Lipschitz for the pinched pseudometric**,
with no smallness condition on the distance, as soon as the universal constant
of the estimate is bounded uniformly over the admissible curves. -/
theorem dist_selInv_le_pinchedDist_uniformLip
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP) (hkhat : rearKappa1 kh ≤ khat)
    (hL : ∀ a b : Data, IsPinchedCurve kminP kh a → IsPinchedCurve kminP kh b →
      (∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) → (∀ u, HasDerivAt (⇑b.1) (b.2.1 u) u) →
      selInvLipUniversal kminP kh khat (perim (SelectedInverseMap.selInv kh a))
        (perim (SelectedInverseMap.selInv kh b)) ≤ L)
    (hne : (pinchedSet kminP kh p q).Nonempty) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ L * pinchedDist kminP kh p q := by
  have hkh0 : 0 ≤ kh := by
    obtain ⟨c, Γ, -, hΓ⟩ := hne
    exact le_trans hkminP.le (le_trans (hΓ.kmin 0 0) (hΓ.kmax 0 0))
  have hL0 : 0 ≤ L := by
    obtain ⟨c, Γ, -, hΓ⟩ := hne
    exact le_trans (selInvLipUniversal_nonneg hkminP hkh0 hkh1)
      (hL _ _ (isPinchedCurve_start hΓ) (isPinchedCurve_start hΓ) hpd hpd)
  refine le_mul_of_near hL0 (fun ε hε => ?_)
  obtain ⟨c, ⟨Γ, hc, hΓ⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show pinchedDist kminP kh p q < pinchedDist kminP kh p q + ε by linarith)
  refine ⟨cost Γ, by rw [hc]; linarith, ?_⟩
  exact dist_selInv_le_cost_uniformLip Γ hΓ hpd hpd2 hqd hqd2 hkh1 hkminP hkhat hL

end PinchedPath
