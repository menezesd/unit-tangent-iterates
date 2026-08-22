import Mathlib
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Non-expansiveness modulo the marking, from a bound on every shift

`SelectedInverseRearOwnShift.pathDistShift_selInv_le` bounds the distance
modulo the marking of the two marked selected inverses of the ends of *one*
normal path by the cost of that path.  The distance modulo the marking of the
two fronts, however, is an infimum over the shifts of the second front, so a
bound in terms of `MarkedShift.pathDistShift` of the fronts needs the bound for
the paths joining `p` to *every* shift of `q`, together with the fact that
shifting the marking of the front only shifts the marking of the image — which
is the equivariance of `SelectedInverseShiftEquivariance.lean`.

That last step is carried out here.  The pseudodistance modulo the marking does
not see a shift of either argument (`pathDistShift_shiftData_right`), so the
equivariance makes the left-hand side of the bound independent of the shift
(`pathDistShift_selInv_shiftData`), and taking the infimum over the shifts
turns a bound valid for every shift into

`pathDistShift (selInv κ̂ p) (selInv κ̂ q) ≤ K · pathDistShift p q`,

the non-expansiveness statement in the pseudodistance taken modulo the marking
(`pathDistShift_selInv_le_pathDistShift`, and
`pathDistShift_selInv_le_pathDistShift_of_tube`, where the equivariance is
supplied by the tube hypotheses rather than assumed).

Nothing here supplies the bound for the individual shifts: that is the
hypothesis `hbound`, which is exactly the conclusion of
`SelectedInverseRearOwnShift.pathDistShift_selInv_le` for the path joining `p`
to the shifted curve.
-/

noncomputable section

open Set Function MarkedSpace MarkedShift RearTrack

namespace SelectedInverseQuotient

/-! ### The pseudodistance modulo the marking ignores a shift -/

/-- **A shift of the second curve does not change the pseudodistance modulo the
marking.** -/
theorem pathDistShift_shiftData_right (b : ℝ) (p q : Data) :
    pathDistShift p (shiftData b q) = pathDistShift p q := by
  refine le_antisymm (le_ciInf fun c => ?_) (le_ciInf fun c => ?_)
  · have h : shiftData c q = shiftData (c - b) (shiftData b q) := by
      rw [shiftData_add]
      ring_nf
    rw [h]
    exact pathDistShift_le _ _ _
  · rw [shiftData_add]
    exact pathDistShift_le _ _ _

/-- **A shift of the first curve does not change the pseudodistance modulo the
marking** either. -/
theorem pathDistShift_shiftData_left (b : ℝ) (p q : Data) :
    pathDistShift (shiftData b p) q = pathDistShift p q := by
  rw [pathDistShift_comm, pathDistShift_shiftData_right, pathDistShift_comm]

/-- **The selected inverse of a shifted curve is at the same distance modulo
the marking**, by the equivariance of the selected inverse. -/
theorem pathDistShift_selInv_shiftData {kap b : ℝ} {x q : Data}
    (hequiv : ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b q)
      = shiftData cc (SelectedInverseMap.selInv kap q)) :
    pathDistShift x (SelectedInverseMap.selInv kap (shiftData b q))
      = pathDistShift x (SelectedInverseMap.selInv kap q) := by
  obtain ⟨cc, hcc⟩ := hequiv
  rw [hcc, pathDistShift_shiftData_right]

/-! ### From a bound for every shift to the bound modulo the marking -/

/-- **Non-expansiveness modulo the marking.**  If the two marked selected
inverses are at distance at most `K` times the path pseudodistance of `p` to
*each* shift of `q`, then they are at distance at most `K` times the
pseudodistance of `p` and `q` modulo the marking. -/
theorem pathDistShift_selInv_le_pathDistShift {kap K : ℝ} {p q : Data} (hK : 0 ≤ K)
    (hequiv : ∀ b : ℝ, ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b q)
      = shiftData cc (SelectedInverseMap.selInv kap q))
    (hbound : ∀ b : ℝ,
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ K * PathMetric.pathDist p (shiftData b q)) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ K * pathDistShift p q := by
  have hstep : ∀ b : ℝ,
      pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
        ≤ K * PathMetric.pathDist p (shiftData b q) := by
    intro b
    have h := hbound b
    rwa [pathDistShift_selInv_shiftData (hequiv b)] at h
  rcases eq_or_lt_of_le hK with rfl | hKpos
  · have h0 := hstep 0
    have hnn := pathDistShift_nonneg
      (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
    simp only [zero_mul] at h0 ⊢
    linarith
  · have hle : pathDistShift (SelectedInverseMap.selInv kap p)
        (SelectedInverseMap.selInv kap q) / K ≤ pathDistShift p q := by
      refine le_ciInf fun b => ?_
      rw [div_le_iff₀ hKpos]
      have := hstep b
      linarith [mul_comm K (PathMetric.pathDist p (shiftData b q))]
    rw [div_le_iff₀ hKpos] at hle
    linarith [mul_comm (pathDistShift p q) K]

/-- **Non-expansiveness modulo the marking, from the bound on every normal
path.**  The bound of `SelectedInverseRearOwnShift.pathDistShift_selInv_le` is
stated for a single normal path and its cost; if it holds for every normal path
from `p` to every shift of `q`, the pseudodistance modulo the marking of the two
marked selected inverses is at most `K` times that of `p` and `q`. -/
theorem pathDistShift_selInv_le_of_forall_cost {kap K : ℝ} {p q : Data} (hK : 0 ≤ K)
    (hequiv : ∀ b : ℝ, ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b q)
      = shiftData cc (SelectedInverseMap.selInv kap q))
    (hne : ∀ b : ℝ, Nonempty (PathMetric.NormalPath p (shiftData b q)))
    (hcost : ∀ (b : ℝ) (Γ : PathMetric.NormalPath p (shiftData b q)),
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ K * PathMetric.NormalPath.cost Γ) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ K * pathDistShift p q :=
  pathDistShift_selInv_le_pathDistShift hK hequiv
    (fun b => pathDistShift_le_of_forall_cost hK (hne b) (hcost b))

/-- **Non-expansiveness modulo the marking, with the equivariance discharged.**
For a member `q` of the tube whose rear tracks are embedded — the global
topological fact carried as a hypothesis throughout this project, here for
every shift of the marking — the equivariance of the selected inverse is
automatic, so a bound for every shift already gives the bound in the
pseudodistance modulo the marking. -/
theorem pathDistShift_selInv_le_pathDistShift_of_tube {c kmin dlt kap K : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1) (hK : 0 ≤ K) {p q : Data}
    (hq : IsTubeMember c kmin dlt q)
    (hub : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kap * ‖q.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ dl) (Ico 0 (perim q)))
    (hinjRb : ∀ b : ℝ, ∀ Θ K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev (shiftData b q)) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K' s) s) →
      Function.Periodic dl (perim (shiftData b q)) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev (shiftData b q)) Θ dl) (Ico 0 (perim (shiftData b q))))
    (hbound : ∀ b : ℝ,
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ K * PathMetric.pathDist p (shiftData b q)) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ K * pathDistShift p q :=
  pathDistShift_selInv_le_pathDistShift hK
    (fun b => SelectedInverseShiftEquivariance.selInv_shiftData hc hkmin hkap1 hq hub hinjR b
      (hinjRb b))
    hbound

end SelectedInverseQuotient
