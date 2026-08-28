import UnitTangentIterates.ArclengthScaledJacobiTransition
import UnitTangentIterates.SummableNormalPathLimit

/-!
# Finite-column compactness from stable physical components

The transported Jacobi path may end at a gauge-marked rear rather than the
canonical datum used by the next column.  Stable physical path components
control the first metric leg; a separately summable endpoint cap controls the
second.  Completeness is applied only after the triangle inequality, so no
normal path realizing the endpoint correction and no recursive construction
core are required.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric PathMetric.NormalPath

namespace FiniteColumnStablePhysicalComponentCompactness

open ArclengthScaledJacobiTransition
  NormalPathC2IncrementVariableSpeed

/-- The precise scalar consequence of a depth-uniform physical-component
bound needed for compactness.  The cost comparison remains explicit because
`NormalPath.cost` stores an arbitrary common majorant. -/
structure StablePhysicalComponents
    {p q : Data} (Gamma : NormalPath p q) (P C d : ℝ) : Prop where
  cost_le_components : cost Gamma ≤
    (physicalComponents P Gamma.eta).w +
      (physicalComponents P Gamma.eta).s0 +
      (physicalComponents P Gamma.eta).s1 +
      (physicalComponents P Gamma.eta).s2
  w_le : (physicalComponents P Gamma.eta).w ≤ C * d
  s0_le : (physicalComponents P Gamma.eta).s0 ≤ C * d
  s1_le : (physicalComponents P Gamma.eta).s1 ≤ C * d
  s2_le : (physicalComponents P Gamma.eta).s2 ≤ C * d

theorem StablePhysicalComponents.cost_le_four_mul
    {p q : Data} {Gamma : NormalPath p q} {P C d : ℝ}
    (H : StablePhysicalComponents Gamma P C d) :
    cost Gamma ≤ (4 * C) * d := by
  calc
    cost Gamma ≤ (physicalComponents P Gamma.eta).w +
        (physicalComponents P Gamma.eta).s0 +
        (physicalComponents P Gamma.eta).s1 +
        (physicalComponents P Gamma.eta).s2 := H.cost_le_components
    _ ≤ C * d + C * d + C * d + C * d :=
      add_le_add (add_le_add (add_le_add H.w_le H.s0_le) H.s1_le) H.s2_le
    _ = (4 * C) * d := by ring

/-- One finite-column path followed by its canonical endpoint cap gives the
direct canonical increment used by completeness. -/
theorem canonical_increment_le
    {p g pnext : Data} {Gamma : NormalPath p g}
    {P P0 P1 khat G1 Cg C K d b : ℝ}
    (hp : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpv : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hg : ∀ u, HasDerivAt (⇑g.1) (g.2.1 u) u)
    (hgv : ∀ u, HasDerivAt (⇑g.2.1) (g.2.2 u) u)
    (hgeom : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma)
    (H : StablePhysicalComponents Gamma P C d)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hconversion : c2ConstVar P0 P1 khat G1 Cg ≤ K)
    (hcap : dist g pnext ≤ b) :
    dist p pnext ≤ K * ((4 * C) * d) + b := by
  have hpath : dist p g ≤ K * ((4 * C) * d) := by
    calc
      dist p g ≤ c2ConstVar P0 P1 khat G1 Cg * cost Gamma :=
        dist_le_cost_variableSpeed Gamma hp hg hpv hgv hgeom
      _ ≤ c2ConstVar P0 P1 khat G1 Cg * ((4 * C) * d) :=
        mul_le_mul_of_nonneg_left H.cost_le_four_mul
          (c2ConstVar_nonneg _ _ _ _ _)
      _ ≤ K * ((4 * C) * d) :=
        mul_le_mul_of_nonneg_right hconversion
          (mul_nonneg (mul_nonneg (by norm_num) hC) hd)
  exact (dist_triangle p g pnext).trans (add_le_add hpath hcap)

/-- Rowwise hybrid compactness.  Stable physical components control paths to
the gauge endpoints and summable caps close those endpoints to the canonical
next column. -/
theorem exists_row_limit
    {p g : ℕ → Data} {Gamma : ∀ k, NormalPath (p k) (g k)}
    {period P0 P1 khat G1 Cg defect cap : ℕ → ℝ}
    {C K c kmin dlt : ℝ}
    (hmem : ∀ k, IsTubeMember c kmin dlt (p k))
    (hg : ∀ k u, HasDerivAt (⇑(g k).1) ((g k).2.1 u) u)
    (hgv : ∀ k u, HasDerivAt (⇑(g k).2.1) ((g k).2.2 u) u)
    (hgeom : ∀ k, IsVariableSpeedNormalPath
      (P0 k) (P1 k) (khat k) (G1 k) (Cg k) (Gamma k))
    (H : ∀ k, StablePhysicalComponents (Gamma k) (period k) C (defect k))
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hdefect : ∀ k, 0 ≤ defect k)
    (hconversion : ∀ k, c2ConstVar
      (P0 k) (P1 k) (khat k) (G1 k) (Cg k) ≤ K)
    (hcap : ∀ k, dist (g k) (p (k + 1)) ≤ cap k)
    (hsumDefect : Summable defect) (hsumCap : Summable cap) :
    ∃ x : Data, IsTubeMember c kmin dlt x ∧ Tendsto p atTop (𝓝 x) := by
  let transport : ℕ → ℝ := fun k => K * ((4 * C) * defect k)
  have hsumTransport : Summable transport := by
    simpa [transport, mul_assoc] using
      (hsumDefect.mul_left (4 * C)).mul_left K
  apply SummableNormalPathLimit.exists_limit_of_summable_gauge_canonical_increments
    hmem hsumTransport hsumCap
  · intro k
    have hcost := H k |>.cost_le_four_mul
    calc
      dist (p k) (g k) ≤
          c2ConstVar (P0 k) (P1 k) (khat k) (G1 k) (Cg k) *
            cost (Gamma k) :=
        dist_le_cost_variableSpeed (Gamma k)
          (hmem k).hasDerivAt_curve (hg k)
          (hmem k).hasDerivAt_vel (hgv k) (hgeom k)
      _ ≤ c2ConstVar (P0 k) (P1 k) (khat k) (G1 k) (Cg k) *
            ((4 * C) * defect k) :=
        mul_le_mul_of_nonneg_left hcost (c2ConstVar_nonneg _ _ _ _ _)
      _ ≤ transport k :=
        mul_le_mul_of_nonneg_right (hconversion k)
          (mul_nonneg (mul_nonneg (by norm_num) hC) (hdefect k))
  · exact hcap

/-- Simultaneous finite-column limits for every row. -/
structure LimitOutput
    (p : ℕ → ℕ → Data) (c kmin dlt : ℝ) where
  X : ℕ → Data
  limit_tube : ∀ n, IsTubeMember c kmin dlt (X n)
  row_limit : ∀ n, Tendsto (p n) atTop (𝓝 (X n))

theorem exists_limitOutput
    {p g : ℕ → ℕ → Data}
    {Gamma : ∀ n k, NormalPath (p n k) (g n k)}
    {period P0 P1 khat G1 Cg defect cap : ℕ → ℕ → ℝ}
    {componentConst conversionConst : ℕ → ℝ} {c kmin dlt : ℝ}
    (hmem : ∀ n k, IsTubeMember c kmin dlt (p n k))
    (hg : ∀ n k u, HasDerivAt (⇑(g n k).1) ((g n k).2.1 u) u)
    (hgv : ∀ n k u, HasDerivAt (⇑(g n k).2.1) ((g n k).2.2 u) u)
    (hgeom : ∀ n k, IsVariableSpeedNormalPath
      (P0 n k) (P1 n k) (khat n k) (G1 n k) (Cg n k) (Gamma n k))
    (H : ∀ n k, StablePhysicalComponents (Gamma n k) (period n k)
      (componentConst n) (defect n k))
    (hcomponent : ∀ n, 0 ≤ componentConst n)
    (hconversionConst : ∀ n, 0 ≤ conversionConst n)
    (hdefect : ∀ n k, 0 ≤ defect n k)
    (hconversion : ∀ n k, c2ConstVar
      (P0 n k) (P1 n k) (khat n k) (G1 n k) (Cg n k) ≤ conversionConst n)
    (hcap : ∀ n k, dist (g n k) (p n (k + 1)) ≤ cap n k)
    (hsumDefect : ∀ n, Summable (defect n))
    (hsumCap : ∀ n, Summable (cap n)) :
    Nonempty (LimitOutput p c kmin dlt) := by
  have hrow : ∀ n, ∃ x : Data,
      IsTubeMember c kmin dlt x ∧ Tendsto (p n) atTop (𝓝 x) := by
    intro n
    exact exists_row_limit (Gamma := Gamma n)
      (period := period n) (P0 := P0 n) (P1 := P1 n)
      (khat := khat n) (G1 := G1 n) (Cg := Cg n)
      (defect := defect n) (cap := cap n)
      (C := componentConst n) (K := conversionConst n)
      (hmem n) (hg n) (hgv n) (hgeom n) (H n)
      (hcomponent n) (hconversionConst n) (hdefect n)
      (hconversion n) (hcap n) (hsumDefect n) (hsumCap n)
  choose X hXtube hXlim using hrow
  exact ⟨⟨X, hXtube, hXlim⟩⟩

end FiniteColumnStablePhysicalComponentCompactness
