import Mathlib
import UnitTangentIterates.SelectedInverseQuotient
import UnitTangentIterates.PathMetricSlowTest
import UnitTangentIterates.GaugePathDistVariable

/-!
# Non-expansiveness modulo the marking, tested on slow paths only

`SelectedInverseQuotient.pathDistShift_selInv_le_of_forall_cost` turns a bound
by the cost of *every* normal path from `p` to every shift of `q` into the
non-expansiveness statement

`pathDistShift (selInv κ̂ p) (selInv κ̂ q) ≤ K · pathDistShift p q`.

The estimates of this project do not hold for every path with a constant
independent of it: the constant of the rear path-distance bound degrades with
the size of the normal velocity along the path.  What the `*Speed` files of this
project provide is the bound along the paths of duration one whose cost density
is at most a fixed `M`; by `PathMetric.exists_unitTime_bounded_speed` those
paths already realize the pseudodistance, so nothing is lost.

This file assembles the two facts.  Two reductions are needed:

* only the shifts of `q` that are *close* to `p` matter, since the
  pseudodistance modulo the marking is an infimum over the shifts
  (`pathDistShift_le_mul_of_near_shifts`);
* for each such shift, only the slow paths need be tested
  (`MarkedShift.pathDistShift_le_of_forall_bounded_cost`).

Main result: `pathDistShift_selInv_le_pathDistShift_slow`, where the constant
`K` no longer depends on the path.
-/

noncomputable section

open Set Function MarkedSpace MarkedShift PathMetric

namespace SelectedInverseQuotientSpeed

/-! ### Only the nearby shifts matter -/

/-- **A bound over the shifts that are close.**  If `D ≤ K · pathDist p (q + b)`
for every shift `b` of `q` at pseudodistance less than `β` from `p`, and `β`
exceeds the pseudodistance of `p` and `q` modulo the marking, then
`D ≤ K · pathDistShift p q`.  The far shifts carry no information: they are not
seen by the infimum. -/
theorem pathDistShift_le_mul_of_near_shifts {K beta D : ℝ} {p q : Data} (hK : 0 ≤ K)
    (hbeta : pathDistShift p q < beta)
    (hbound : ∀ b : ℝ, pathDist p (shiftData b q) < beta →
      D ≤ K * pathDist p (shiftData b q)) :
    D ≤ K * pathDistShift p q := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set d : ℝ := pathDistShift p q with hd
  set r : ℝ := min (ε / (K + 1)) (beta - d) with hr
  have hKpos : 0 < K + 1 := by linarith
  have hrpos : 0 < r := lt_min (by positivity) (by linarith)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, pathDist p (shiftData b q) < d + r := by
    have := exists_lt_of_ciInf_lt (f := fun b : ℝ => pathDist p (shiftData b q))
      (show pathDistShift p q < d + r by rw [hd]; linarith)
    simpa [pathDistShift] using this
  have hblt : pathDist p (shiftData b q) < beta := by
    have : r ≤ beta - d := min_le_right _ _
    linarith
  have h1 : D ≤ K * pathDist p (shiftData b q) := hbound b hblt
  have h2 : K * pathDist p (shiftData b q) ≤ K * (d + r) :=
    mul_le_mul_of_nonneg_left hb.le hK
  have h3 : K * r ≤ ε := by
    have hle : r ≤ ε / (K + 1) := min_le_left _ _
    have hKr : K * r ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hle hK
    have h4 : K * (ε / (K + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hKpos]
      nlinarith
    linarith
  nlinarith

/-! ### The non-expansiveness statement -/

/-- **Non-expansiveness modulo the marking, with a constant independent of the
path.**

Assume that for every shift of `q` and every normal path of duration one from
`p` to it whose cost density is at most `(3/2)β`, the two marked selected
inverses are at distance at most `K` times the cost of that path — this is what
the rear path-distance bound with the constant fixed by the speed of the path
(`SelectedInverseRearOwnShiftSpeed.pathDistShift_selInv_le_speed`) provides,
with `K` a function of the tube constants alone.  Then

`pathDistShift (selInv κ̂ p) (selInv κ̂ q) ≤ K · pathDistShift p q`,

provided `β` exceeds the pseudodistance of `p` and `q` modulo the marking. -/
theorem pathDistShift_selInv_le_pathDistShift_slow {kap K beta : ℝ} {p q : Data}
    (hK : 0 ≤ K) (hbeta : pathDistShift p q < beta)
    (hequiv : ∀ b : ℝ, ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b q)
      = shiftData cc (SelectedInverseMap.selInv kap q))
    (hne : ∀ b : ℝ, Nonempty (NormalPath p (shiftData b q)))
    (hcost : ∀ (b : ℝ) (Γ : NormalPath p (shiftData b q)), Γ.T = 1 →
      (∀ t, Γ.m t ≤ (3 / 2) * beta) →
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ K * NormalPath.cost Γ) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ K * pathDistShift p q := by
  refine pathDistShift_le_mul_of_near_shifts hK hbeta fun b hb => ?_
  have h := MarkedShift.pathDistShift_le_of_forall_bounded_cost hK hb (hne b)
    (fun Γ hT hm => hcost b Γ hT hm)
  rwa [SelectedInverseQuotient.pathDistShift_selInv_shiftData (hequiv b)] at h

/-- **The same, phrased on the normal speed.**  The cost density of a normal
path dominates its normal speed, so it is enough to test the paths of duration
one along which the curve moves at speed at most `(3/2)β`. -/
theorem pathDistShift_selInv_le_pathDistShift_slow_speed {kap K beta : ℝ} {p q : Data}
    (hK : 0 ≤ K) (hbeta : pathDistShift p q < beta)
    (hequiv : ∀ b : ℝ, ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b q)
      = shiftData cc (SelectedInverseMap.selInv kap q))
    (hne : ∀ b : ℝ, Nonempty (NormalPath p (shiftData b q)))
    (hcost : ∀ (b : ℝ) (Γ : NormalPath p (shiftData b q)), Γ.T = 1 →
      (∀ t u, |Γ.eta t u| ≤ (3 / 2) * beta) →
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ K * NormalPath.cost Γ) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ K * pathDistShift p q :=
  pathDistShift_selInv_le_pathDistShift_slow hK hbeta hequiv hne
    (fun b Γ hT hm => hcost b Γ hT fun t u => le_trans (Γ.abs_eta_le t u) (hm t))

/-! ### The constant of the chain, made explicit -/

open GaugePathDistVariable in
/-- **The uniform constant of the rear path-distance bound.**  The gauge
constant of `GaugePathDistVariable.gaugeJacobiConst` at the duration `T = 1`,
with the two Jacobi constants of the chain evaluated at the sup bound `M` of
the front normal velocity, which the `*Speed` files supply from the cost density
of the path.  It depends only on the pinching `κ̂ = kh`, on the bounds `P0 ≤ P ≤
P1` for the arclength period along the tube, on `M` and on the rear perimeter
`Q`. -/
def selInvGaugeConst (P0 P1 kh M Q : ℝ) : ℝ :=
  gaugeJacobiConst P0 P1 kh
    (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
    ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
        * (kh / Real.sqrt (1 - kh ^ 2))
      + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) 1 Q

open GaugePathDistVariable in
theorem selInvGaugeConst_nonneg {P0 P1 kh M Q : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hQ : 0 < Q) :
    0 ≤ selInvGaugeConst P0 P1 kh M Q := by
  have hkh2 : (0:ℝ) < 1 - kh ^ 2 := by nlinarith
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hkh2
  refine gaugeJacobiConst_nonneg hP0 hP1 hkh0 hkh1 hQ ?_ zero_le_one
  have h1 : 0 ≤ M / Real.sqrt (1 - kh ^ 2) := by positivity
  have h2 : 0 ≤ kh / Real.sqrt (1 - kh ^ 2) := by positivity
  have h3 : 0 ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := by positivity
  have h4 : 0 ≤ (M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
      * (kh / Real.sqrt (1 - kh ^ 2)) := by positivity
  nlinarith

/-- **Non-expansiveness modulo the marking, with the constant of the chain
written out.**

The specialization of `pathDistShift_selInv_le_pathDistShift_slow` to the
constant that
`SelectedInverseRearOwnShiftSpeed.pathDistShift_selInv_le_speed` produces for a
normal path of duration one whose cost density is at most `M = (3/2)β`: it is
the gauge constant `selInvGaugeConst P0 P1 κ̂ M Q`, a function of the pinching,
of the bounds for the arclength period along the tube, of `β` and of the rear
perimeter `Q = perim (selInv κ̂ p)` — and of nothing else.  In particular it
does not depend on the path, which is what a Lipschitz estimate requires. -/
theorem pathDistShift_selInv_le_pathDistShift_gauge {kap P0 P1 beta : ℝ} {p q : Data}
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hbeta0 : 0 ≤ beta) (hQ : 0 < perim (SelectedInverseMap.selInv kap p))
    (hbeta : pathDistShift p q < beta)
    (hequiv : ∀ b : ℝ, ∃ cc : ℝ, SelectedInverseMap.selInv kap (shiftData b q)
      = shiftData cc (SelectedInverseMap.selInv kap q))
    (hne : ∀ b : ℝ, Nonempty (NormalPath p (shiftData b q)))
    (hcost : ∀ (b : ℝ) (Γ : NormalPath p (shiftData b q)), Γ.T = 1 →
      (∀ t, Γ.m t ≤ (3 / 2) * beta) →
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ selInvGaugeConst P0 P1 kap ((3 / 2) * beta)
            (perim (SelectedInverseMap.selInv kap p)) * NormalPath.cost Γ) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ selInvGaugeConst P0 P1 kap ((3 / 2) * beta)
          (perim (SelectedInverseMap.selInv kap p)) * pathDistShift p q :=
  pathDistShift_selInv_le_pathDistShift_slow
    (selInvGaugeConst_nonneg hP0 hP1 hkap0 hkap1 (by linarith) hQ) hbeta hequiv hne hcost

end SelectedInverseQuotientSpeed
