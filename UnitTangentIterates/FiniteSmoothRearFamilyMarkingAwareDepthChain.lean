import UnitTangentIterates.ConfiguredRecursiveEdgeBaseFacts
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.SummableNormalPathLimit

/-!
# One-dimensional marking-aware depth recursion

This is the invariant-indexed alternative to the triangular column recursion.
There is one marked curve at each depth.  A successor certificate produces the
next marked curve, retains ovality, and records the exact range form of the
unit-tangent relation.  Quantitative caps are kept in a separate proposition,
so the geometric recursion does not depend on a particular scalar budget.

The scalar row used by a step is definitionally its depth `k`.  Consequently a
configured adapter may use the row-`k` error and ceilings directly; no spatial
column index or predecessor convention occurs in this API.
-/

noncomputable section

open Filter Function Set Topology MarkedSpace

namespace FiniteSmoothRearFamilyMarkingAwareDepthChain

/-- The scalar row belonging to depth `k`. -/
def rowIndex (k : ℕ) : ℕ := k

@[simp] theorem rowIndex_eq (k : ℕ) : rowIndex k = k := rfl

/-- The single reachable marked state at a fixed recursion depth. -/
structure State (k : ℕ) where
  data : Data
  oval : MainTheoremConditional.IsOval (ev data)

/-- One exact successor of a reachable state. -/
structure Successor {k : ℕ} (S : State k) where
  next : State (k + 1)
  range_tangent :
    range (ev next.data) =
      range (UnitTangent.unitTangentMap (ev S.data))

/-- A total chooser only on reachable one-dimensional states.  Unlike the
column providers, this has no second spatial index. -/
structure Provider (base : State 0) where
  successor : ∀ k (S : State k), Successor S

namespace Provider

/-- The unique state selected at every depth. -/
def trajectory {base : State 0} (P : Provider base) : (k : ℕ) → State k
  | 0 => base
  | k + 1 => (P.successor k (trajectory P k)).next

@[simp] theorem trajectory_zero {base : State 0} (P : Provider base) :
    P.trajectory 0 = base := rfl

@[simp] theorem trajectory_succ {base : State 0} (P : Provider base) (k : ℕ) :
    P.trajectory (k + 1) = (P.successor k (P.trajectory k)).next := rfl

theorem trajectory_oval {base : State 0} (P : Provider base) (k : ℕ) :
    MainTheoremConditional.IsOval (ev (P.trajectory k).data) :=
  (P.trajectory k).oval

theorem trajectory_range_tangent {base : State 0} (P : Provider base) (k : ℕ) :
    range (ev (P.trajectory (k + 1)).data) =
      range (UnitTangent.unitTangentMap (ev (P.trajectory k).data)) := by
  simpa using (P.successor k (P.trajectory k)).range_tangent

end Provider

/-- Summable marked-distance control on the actual reachable successors.
The bound at depth `k` uses exactly scalar row `k`. -/
structure Cap {base : State 0} (P : Provider base) (error : ℕ → ℝ) : Prop where
  error_nonnegative : ∀ k, 0 ≤ error k
  error_summable : Summable error
  step_dist : ∀ k,
    dist (P.trajectory k).data (P.trajectory (k + 1)).data ≤ error (rowIndex k)

namespace Cap

theorem step_dist_at_row {base : State 0} {P : Provider base} {error : ℕ → ℝ}
    (C : Cap P error) (k : ℕ) :
    dist (P.trajectory k).data (P.trajectory (k + 1)).data ≤ error k := by
  simpa using C.step_dist k

/-- Finite telescoping of the consecutive row caps. -/
theorem dist_trajectory_le_sum
    {base : State 0} {P : Provider base} {error : ℕ → ℝ}
    (C : Cap P error) (m n : ℕ) :
    dist (P.trajectory m).data (P.trajectory (m + n)).data ≤
      ∑ i ∈ Finset.range n, error (m + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        dist (P.trajectory m).data (P.trajectory (m + (n + 1))).data
            ≤ dist (P.trajectory m).data (P.trajectory (m + n)).data +
                dist (P.trajectory (m + n)).data
                  (P.trajectory ((m + n) + 1)).data := by
              convert dist_triangle (P.trajectory m).data
                (P.trajectory (m + n)).data
                (P.trajectory (m + (n + 1))).data using 1 <;> omega
        _ ≤ (∑ i ∈ Finset.range n, error (m + i)) + error (m + n) :=
              add_le_add ih (C.step_dist_at_row (m + n))
        _ = ∑ i ∈ Finset.range (n + 1), error (m + i) := by
              rw [Finset.sum_range_succ]

/-- Summable row caps make the one-dimensional depth trajectory Cauchy. -/
theorem cauchy_trajectory
    {base : State 0} {P : Provider base} {error : ℕ → ℝ}
    (C : Cap P error) : CauchySeq (fun k => (P.trajectory k).data) := by
  apply cauchySeq_of_summable_dist
  exact Summable.of_nonneg_of_le (fun _ => dist_nonneg)
    C.step_dist_at_row C.error_summable

/-- Direct convergence of the depth trajectory, with the sharp summable-tail
bound inherited from its row caps. -/
theorem exists_limit
    {base : State 0} {P : Provider base} {error : ℕ → ℝ}
    (C : Cap P error) :
    ∃ limit : Data,
      Tendsto (fun k => (P.trajectory k).data) atTop (𝓝 limit) ∧
      ∀ k, dist (P.trajectory k).data limit ≤ ShadowingTails.tail error k := by
  obtain ⟨limit, hlimit, hdist⟩ :=
    ShadowingTails.exists_limit_of_summable_increments
      (Z := fun k => (P.trajectory k).data) (d := error) (C := 1)
      C.error_summable (fun k => by simpa using C.step_dist_at_row k)
  exact ⟨limit, hlimit, fun k => by simpa using hdist k⟩

/-- If all finite states lie in one closed marked tube, the direct chain limit
lies in that same tube. -/
theorem exists_limit_in_tube
    {base : State 0} {P : Provider base} {error : ℕ → ℝ}
    (C : Cap P error) {c kmin dlt : ℝ}
    (hmem : ∀ k, IsTubeMember c kmin dlt (P.trajectory k).data) :
    ∃ limit : Data, IsTubeMember c kmin dlt limit ∧
      Tendsto (fun k => (P.trajectory k).data) atTop (𝓝 limit) := by
  exact SummableNormalPathLimit.exists_limit_of_summable_dist
    hmem C.error_summable C.step_dist_at_row

end Cap

namespace Configured

open ConfiguredRecursiveEdgeBaseFacts

variable {MA NA : ℝ}

/-- The configured width-gap model is the exact depth-zero state. -/
def baseState (O : Output MA NA) : State 0 where
  data := O.Q 1
  oval := base_isOval O

/-- The ordinary curves of a selected depth chain. -/
def curves {O : Output MA NA} (P : Provider (baseState O)) : ℕ → ℝ → ℂ :=
  fun k => ev (P.trajectory k).data

@[simp] theorem curves_zero {O : Output MA NA} (P : Provider (baseState O)) :
    curves P 0 = ev (O.Q 1) := rfl

theorem curves_oval {O : Output MA NA} (P : Provider (baseState O)) (k : ℕ) :
    MainTheoremConditional.IsOval (curves P k) :=
  P.trajectory_oval k

theorem curves_range_tangent
    {O : Output MA NA} (P : Provider (baseState O)) (k : ℕ) :
    range (curves P (k + 1)) =
      range (UnitTangent.unitTangentMap (curves P k)) :=
  P.trajectory_range_tangent k

/-- Paper-facing theorem for the one-dimensional depth recursion.  Its
noncircle conclusion is the configured width gap at the exact initial state;
no false stability claim for arbitrary later states is needed. -/
theorem paperMain {O : Output MA NA} (P : Provider (baseState O)) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Periodic (Gamma 0) L ∧
      (∀ k, MainTheoremConditional.IsOval (Gamma k)) ∧
      (∀ k, range (Gamma (k + 1)) =
        range (UnitTangent.unitTangentMap (Gamma k))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  refine ⟨curves P, basePeriod O, basePeriod_pos O, ?_, ?_, ?_, ?_⟩
  · simpa using baseCurve_periodic O
  · exact curves_oval P
  · exact curves_range_tangent P
  · simpa [basePeriod_eq_perim] using base_not_circle O

end Configured

end FiniteSmoothRearFamilyMarkingAwareDepthChain

