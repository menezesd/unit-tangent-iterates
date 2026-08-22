import Mathlib
import UnitTangentIterates.PathMetricRescale
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.StoppedCurvature

/-!
# The invariant tubes of the shadowing theorem

The proof of the theorem *Regularizing backward shadowing* of the paper *A
Noncircular Oval with Convex Unit-Tangent Iterates* is organized around a
sequence of **tubes**: `𝒟ₙ` is the set of curves that can be joined to the
`n`-th model `Qₙ` by an admissible path of size `aₙ`, and the two structural
steps are

* *invariance*: `𝔅(𝒟_{n+1}) ⊆ 𝒟ₙ`, which holds because the selected inverse
  does not increase the size of a path (`Lemma jacobi`) and because the defect
  path `Λₙ : Qₙ ⇝ 𝔅Q_{n+1}` supplied by *Curvature interpolation* has size
  `dₙ`, while `aₙ = dₙ + a_{n+1}`;
* *the curvature ceiling*: along every admissible path the curvature stays
  below `κ̂`, by the *Stopped curvature estimate*.

Both steps are formalized here in the project's own path pseudometric
(`UnitTangentIterates/PathMetric.lean`), where the size of a path is its cost — an
upper bound for `W + S₀ + S₁ + S₂` — and the tube is

```
  tube Q a = {C | ∃ Γ : NormalPath Q C, cost Γ ≤ a} .
```

Main results:

* `tube_invariance` — `B '' tube Q' a' ⊆ tube Q a` whenever `B` multiplies the
  cost of paths by at most `K`, a defect path `Q ⇝ B Q'` of cost at most `d`
  exists, and `d + K·a' ≤ a`;
* `pullback_mem_tube` — consequently the terminal pullbacks
  `Zₙ^{(N)} = B^{N-n}(Q_N)` all lie in `tube (Q n) (a n)`;
* `pullback_mem_tube_tail` — the same with the paper's own radii, the tails
  `aₙ = ∑_{m ≥ n} dₙ` of a summable defect sequence, for a map that does not
  increase the cost of paths;
* `norm_sub_pullback_le`, `pathDist_pullback_le` — the resulting uniform
  shadowing bounds: every pullback stays within `aₙ` of the model, both
  pointwise and in the path pseudodistance;
* `curvature_lt_of_cost` — the stopped curvature estimate in the cost form:
  along a normal path of duration one and cost `a` whose curvature obeys
  `κ_t = η_ss + κ²η`, an initial curvature at most `κ_b` and
  `(1 + κ_e²)·a < κ_e − κ_b` keep the curvature below `κ_e`.

What is *not* proved here is the hypothesis `hmap`: that the selected inverse
really takes normal paths to normal paths of controlled cost.  That is the
content of the paper's lemmas *Smooth dependence of the selected rear* and
*Inverse Jacobi estimates*; its scalar core is
`SelectedInverseLipschitz.exists_normalPath_of_selected_rears`.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace TubeInvariance

/-- **The tube of radius `a` around the marked curve `Q`**: the curves that can
be joined to `Q` by a normal path of cost at most `a`. -/
def tube (Q : Data) (a : ℝ) : Set Data := {C | ∃ Γ : NormalPath Q C, cost Γ ≤ a}

variable {Q C : Data} {a b : ℝ}

theorem mem_tube_iff : C ∈ tube Q a ↔ ∃ Γ : NormalPath Q C, cost Γ ≤ a := Iff.rfl

/-- The model is the centre of its own tube. -/
theorem self_mem_tube (Q : Data) (ha : 0 ≤ a) : Q ∈ tube Q a :=
  ⟨NormalPath.const Q, by simpa using ha⟩

theorem tube_mono (hab : a ≤ b) : tube Q a ⊆ tube Q b := fun _ ⟨Γ, hΓ⟩ => ⟨Γ, hΓ.trans hab⟩

/-- A member of the tube is within `a` of the model in the path
pseudodistance. -/
theorem pathDist_le_of_mem_tube (h : C ∈ tube Q a) : pathDist Q C ≤ a := by
  obtain ⟨Γ, hΓ⟩ := h
  exact (pathDist_le_cost Γ).trans hΓ

/-- A member of the tube is within `a` of the model at every point of the
normalized parameter. -/
theorem norm_sub_le_of_mem_tube (h : C ∈ tube Q a) (u : ℝ) : ‖C.1 u - Q.1 u‖ ≤ a := by
  obtain ⟨Γ, hΓ⟩ := h
  exact (Γ.norm_sub_le_cost u).trans hΓ

/-! ### Invariance of the tubes -/

/-- **Tube invariance.**  Let `B` take a normal path to a normal path of cost at
most `K` times as large, let `Λ` be a defect path from `Q` to `B Q'` of cost at
most `d`, and let `d + K·a' ≤ a`.  Then `B` maps the tube of radius `a'` around
`Q'` into the tube of radius `a` around `Q`.

This is the step `𝔅(𝒟_{n+1}) ⊆ 𝒟ₙ` of the shadowing theorem: the inverse image
of an admissible path is admissible, and concatenating it with the defect path
of *Curvature interpolation* returns to the model. -/
theorem tube_invariance {B : Data → Data} {Q Q' : Data} {K d a' : ℝ} (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K * cost Γ)
    (Λ : NormalPath Q (B Q')) (hΛ : cost Λ ≤ d)
    (hsum : d + K * a' ≤ a) :
    B '' tube Q' a' ⊆ tube Q a := by
  rintro _ ⟨C, ⟨Γ, hΓ⟩, rfl⟩
  obtain ⟨Δ, hΔ⟩ := hmap _ _ Γ
  refine ⟨Λ.concat Δ, ?_⟩
  have hstep : cost Δ ≤ K * a' := hΔ.trans (by nlinarith [mul_le_mul_of_nonneg_left hΓ hK])
  calc cost (Λ.concat Δ) = cost Λ + cost Δ := cost_concat Λ Δ
    _ ≤ d + K * a' := add_le_add hΛ hstep
    _ ≤ a := hsum

/-- **The terminal pullbacks stay in the tubes.**  If `B` multiplies the cost of
paths by at most `K`, if each model `Q n` is joined to `B (Q (n+1))` by a defect
path of cost at most `d n`, and if the radii satisfy `d n + K·a (n+1) ≤ a n`,
then `Zₙ^{(n+k)} = B^{k}(Q (n+k))` lies in the tube of radius `a n` around
`Q n`, for every `n` and `k`. -/
theorem pullback_mem_tube {B : Data → Data} {Q : ℕ → Data} {a d : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ n, 0 ≤ a n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K * cost Γ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))), cost Λ ≤ d n)
    (hrec : ∀ n, d n + K * a (n + 1) ≤ a n) :
    ∀ n k : ℕ, B^[k] (Q (n + k)) ∈ tube (Q n) (a n) := by
  intro n k
  induction k generalizing n with
  | zero => simpa using self_mem_tube (Q n) (ha n)
  | succ k ih =>
      obtain ⟨Λ, hΛ⟩ := hdefect n
      have hmem : B^[k] (Q ((n + 1) + k)) ∈ tube (Q (n + 1)) (a (n + 1)) := ih (n + 1)
      have hsub := tube_invariance (B := B) (Q := Q n) (Q' := Q (n + 1)) (K := K)
        (d := d n) (a' := a (n + 1)) (a := a n) hK hmap Λ hΛ (hrec n)
      have : B (B^[k] (Q ((n + 1) + k))) ∈ tube (Q n) (a n) := hsub ⟨_, hmem, rfl⟩
      have hidx : n + (k + 1) = (n + 1) + k := by omega
      rw [hidx, Function.iterate_succ_apply']
      exact this

/-- **The tubes of the shadowing theorem.**  For a map that does not increase
the cost of paths and a summable sequence of defects, the radii may be taken to
be the tails `aₙ = ∑_{m ≥ n} d m`, and every terminal pullback lies in the
corresponding tube. -/
theorem pullback_mem_tube_tail {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hK1 : K ≤ 1) (hs : Summable d) (hd : ∀ n, 0 ≤ d n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K * cost Γ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))), cost Λ ≤ d n) :
    ∀ n k : ℕ, B^[k] (Q (n + k)) ∈ tube (Q n) (ShadowingTails.tail d n) := by
  refine pullback_mem_tube hK (fun n => ShadowingTails.tail_nonneg hd n) hmap hdefect ?_
  intro n
  have htail := ShadowingTails.tail_succ hs n
  nlinarith [ShadowingTails.tail_nonneg hd (n + 1)]

/-- **The shadowing bound, pointwise.**  Under the hypotheses of
`pullback_mem_tube`, every pullback stays within `a n` of the model `Q n` at
every point of the normalized parameter. -/
theorem norm_sub_pullback_le {B : Data → Data} {Q : ℕ → Data} {a d : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ n, 0 ≤ a n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K * cost Γ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))), cost Λ ≤ d n)
    (hrec : ∀ n, d n + K * a (n + 1) ≤ a n) (n k : ℕ) (u : ℝ) :
    ‖(B^[k] (Q (n + k))).1 u - (Q n).1 u‖ ≤ a n :=
  norm_sub_le_of_mem_tube (pullback_mem_tube hK ha hmap hdefect hrec n k) u

/-- **The shadowing bound, in the path pseudodistance.** -/
theorem pathDist_pullback_le {B : Data → Data} {Q : ℕ → Data} {a d : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ n, 0 ≤ a n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K * cost Γ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))), cost Λ ≤ d n)
    (hrec : ∀ n, d n + K * a (n + 1) ≤ a n) (n k : ℕ) :
    pathDist (Q n) (B^[k] (Q (n + k))) ≤ a n :=
  pathDist_le_of_mem_tube (pullback_mem_tube hK ha hmap hdefect hrec n k)

/-! ### The curvature ceiling of the tube -/

/-- **The stopped curvature estimate in cost form.**  Along a normal path of
duration one whose curvature evolves by `κ_t = η_ss + κ²η` with
`η_ss = ∂_u²η`, if the curvature is nonnegative, at most `κ_b` at the initial
time, and if `(1 + κ_e²)·cost Γ < κ_e − κ_b`, then the curvature stays strictly
below `κ_e` for the whole path.

This is the step of the shadowing theorem that keeps the members of the tube
below the ceiling `κ̂`; the smallness hypothesis is the tube condition
`C_tube·a_{n+1} < κ̄ − κ₀` of `TubeConstants.lean`, with the constants of the
Jacobi estimates already absorbed into the cost. -/
theorem curvature_lt_of_cost {p q : Data} (Γ : NormalPath p q) (hT : Γ.T = 1)
    {kappa : ℝ → ℝ → ℝ} {ke kb : ℝ}
    (hbdd : ∀ t, BddAbove (Set.range fun u => |iteratedDeriv 2 (Γ.eta t) u|))
    (hderiv : ∀ t x, HasDerivAt (fun r => kappa r x)
      (iteratedDeriv 2 (Γ.eta t) x + (kappa t x) ^ 2 * Γ.eta t x) t)
    (hint : ∀ x, IntervalIntegrable
      (fun r => iteratedDeriv 2 (Γ.eta r) x + (kappa r x) ^ 2 * Γ.eta r x) volume 0 1)
    (hnonneg : ∀ r x, 0 ≤ kappa r x) (hinit : ∀ x, kappa 0 x ≤ kb)
    (hsmall : (1 + ke ^ 2) * cost Γ < ke - kb) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ u, kappa t u < ke := by
  have hcost : cost Γ = ∫ t in (0:ℝ)..1, Γ.m t := by rw [cost, hT]
  have hm2 : ∀ r x, |iteratedDeriv 2 (Γ.eta r) x| ≤ Γ.m r := fun r x =>
    (MarkedTopology.le_supNorm (hbdd r) x).trans (Γ.le_m_sup r 2 le_rfl)
  refine StoppedCurvature.stopped_curvature_path (kappa := kappa)
    (etass := fun t x => iteratedDeriv 2 (Γ.eta t) x) (eta := Γ.eta)
    (m0 := Γ.m) (m2 := Γ.m) (S0 := cost Γ) (S2 := cost Γ) (ke := ke) (kb := kb)
    hderiv hint Γ.abs_eta_le hm2
    (Γ.cont_m.intervalIntegrable 0 1) (Γ.cont_m.intervalIntegrable 0 1)
    hcost hcost hnonneg hinit ?_
  nlinarith [hsmall]

end TubeInvariance
