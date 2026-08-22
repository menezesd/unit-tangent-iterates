import Mathlib
import UnitTangentIterates.ShadowingTails

/-!
# The shadowing scheme, assembled

This file formalizes the *assembly* of the theorem *Regularizing backward
shadowing* of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

The proof of that theorem has two parts.  The first is the analytic part: the
selected inverse `𝓑` is defined on a tube of curves around the model, does not
increase the `L¹`-type defect functional `W`, and gains derivatives (the
estimates `S₀ ≤ C₀W`, `S₁ ≤ C₁(1+M₀)W`, ...).  Those estimates, the tube
constants and the propagation of the bounds are formalized in
`JacobiEstimates.lean`, `TubeConstants.lean` and `ShadowingTails.lean`.  The
second is the *scheme* itself: granting that `𝓑` is defined and non-expansive
for the defect metric, the terminal pullbacks

```
  Z_n^{(N)} = 𝓑^{N-n} Q_N
```

form a Cauchy sequence in `N`, their limits `X_n` form an **exact** inverse
orbit `X_n = 𝓑 X_{n+1}` (hence `𝒯X_n = X_{n+1}`), and they shadow the model
pseudo-orbit: `d(X_n, Q_n) ≤ r_n`, where `r_n = ∑_{m ≥ n} e_m`.

That second part is what this file proves, in the natural abstract setting: a
complete metric space `M` (the space of marked curves with the defect metric),
a non-expansive selected inverse `B : M → M`, and a pseudo-orbit `Q : ℕ → M`
with summable defects `dist (Q n) (B (Q (n+1))) ≤ e n`.  Every hypothesis is
one of the estimates established elsewhere in the project, and the conclusions
are exactly the clauses of the paper's theorem that concern the scheme:

* `exists_shadowing_orbit` : existence of the exact orbit together with the
  shadowing bound `dist (X n) (Q n) ≤ r n`;
* `unitTangent_of_shadowing_orbit` : the orbit is an orbit of the forward map,
  `T (X n) = X (n+1)`, whenever `T ∘ B = id` (the selected inverse is a right
  inverse of the unit-tangent transform);
* `lipschitz_functional_shadowing` : any `L`-Lipschitz functional (perimeter,
  width, ...) of the orbit is within `L r n` of that of the model — the clause
  `|Per(X_n) − 2L_n| ≤ C r_n`;
* `shadowing_orbit_unique` : uniqueness of the exact orbit among orbits that
  stay asymptotically close to the model — the paper's uniqueness clause;
* `exists_shadowing_orbit_all` : the four clauses in a single statement.

The defect metric itself (the marked geometric topology) is not constructed
here; see `MarkedTopology.lean` for its ingredients.
-/

noncomputable section

open Filter Topology

namespace ShadowingScheme

variable {M : Type*} [MetricSpace M] [CompleteSpace M]

omit [CompleteSpace M] in
/-- Iterating a non-expansive map keeps it non-expansive. -/
theorem dist_iterate_le {B : M → M} (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) :
    ∀ (k : ℕ) (x y : M), dist (B^[k] x) (B^[k] y) ≤ dist x y := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
      intro x y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (B x) (B y)) (hB x y)

/-- The terminal pullback of the model at level `n` and depth `k`:
`Z_n^{(n+k)} = 𝓑^k Q_{n+k}`. -/
def pullback (B : M → M) (Q : ℕ → M) (n k : ℕ) : M := B^[k] (Q (n + k))

omit [MetricSpace M] [CompleteSpace M] in
@[simp] theorem pullback_zero (B : M → M) (Q : ℕ → M) (n : ℕ) :
    pullback B Q n 0 = Q n := by simp [pullback]

omit [CompleteSpace M] in
/-- **The increment estimate.**  Consecutive terminal pullbacks differ by at
most the defect at the terminal level: this is where non-expansiveness of the
selected inverse is used. -/
theorem dist_pullback_succ {B : M → M} {Q : ℕ → M} {e : ℕ → ℝ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) (n k : ℕ) :
    dist (pullback B Q n k) (pullback B Q n (k + 1)) ≤ e (n + k) := by
  have hrw : pullback B Q n (k + 1) = B^[k] (B (Q (n + k + 1))) := by
    simp only [pullback, Function.iterate_succ_apply, Nat.add_assoc]
  rw [hrw, pullback]
  exact le_trans (dist_iterate_le hB k _ _) (hdef (n + k))

/-- **The shadowing scheme.**  Let `B` be a non-expansive selected inverse on a
complete metric space, and let `Q` be a pseudo-orbit whose defects
`dist (Q n) (B (Q (n+1)))` are bounded by a summable sequence `e`.  Then the
terminal pullbacks converge, their limits form an exact inverse orbit, and the
orbit shadows the model within the tail `r_n = ∑_{m ≥ n} e_m`. -/
theorem exists_shadowing_orbit {B : M → M} {Q : ℕ → M} {e : ℕ → ℝ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hcont : Continuous B)
    (hsum : Summable e) (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M,
      (∀ n, Tendsto (fun k => pullback B Q n k) atTop (𝓝 (X n))) ∧
      (∀ n, dist (X n) (Q n) ≤ ShadowingTails.tail e n) ∧
      (∀ n, B (X (n + 1)) = X n) := by
  have hstep : ∀ n, ∃ x : M, Tendsto (fun k => pullback B Q n k) atTop (𝓝 x) ∧
      dist (x) (Q n) ≤ ShadowingTails.tail e n := by
    intro n
    have hsum' : Summable fun k => e (n + k) := by
      have := (summable_nat_add_iff (f := e) n).2 hsum
      simpa [Nat.add_comm] using this
    obtain ⟨x, hx, hdx⟩ := ShadowingTails.exists_limit_of_summable_increments
      (Z := fun k => pullback B Q n k) (d := fun k => e (n + k)) (C := 1) hsum'
      (fun k => by simpa using dist_pullback_succ hB hdef n k)
    refine ⟨x, hx, ?_⟩
    have h0 := hdx 0
    rw [pullback_zero] at h0
    rw [dist_comm]
    simpa [ShadowingTails.tail] using h0
  choose X hX hdX using hstep
  refine ⟨X, hX, hdX, fun n => ?_⟩
  have h1 : Tendsto (fun k => B (pullback B Q (n + 1) k)) atTop (𝓝 (B (X (n + 1)))) :=
    (hcont.tendsto _).comp (hX (n + 1))
  have h2 : (fun k => B (pullback B Q (n + 1) k)) = fun k => pullback B Q n (k + 1) := by
    funext k
    have hidx : n + 1 + k = n + (k + 1) := by omega
    simp only [pullback, hidx, ← Function.iterate_succ_apply' B k]
  rw [h2] at h1
  have h3 : Tendsto (fun k => pullback B Q n (k + 1)) atTop (𝓝 (X n)) :=
    (hX n).comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 h3

omit [MetricSpace M] [CompleteSpace M] in
/-- **The orbit is an orbit of the forward map.**  If `T` is a left inverse of
the selected inverse — for the paper, `T = 𝒯` is the unit-tangent transform and
`B` picks the selected rear — then the shadowing orbit satisfies
`𝒯X_n = X_{n+1}`. -/
theorem unitTangent_of_shadowing_orbit {B T : M → M} {X : ℕ → M}
    (hT : ∀ x, T (B x) = x) (horb : ∀ n, B (X (n + 1)) = X n) (n : ℕ) :
    T (X n) = X (n + 1) := by
  rw [← horb n, hT]

omit [CompleteSpace M] in
/-- **Lipschitz functionals of the orbit stay close to those of the model.**
Applied to the perimeter this is the clause `|Per(X_n) − 2L_n| ≤ C r_n` of the
paper's theorem; applied to the Hausdorff distance to a fixed set it gives the
first half of the same display. -/
theorem lipschitz_functional_shadowing {X Q : ℕ → M} {Phi : M → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |Phi x - Phi y| ≤ L * dist x y) {r : ℕ → ℝ}
    (hshadow : ∀ n, dist (X n) (Q n) ≤ r n) (n : ℕ) :
    |Phi (X n) - Phi (Q n)| ≤ L * r n :=
  le_trans (hLip _ _) (by
    have := hshadow n
    nlinarith [dist_nonneg (x := X n) (y := Q n)])

omit [CompleteSpace M] in
/-- **Uniqueness of the shadowing orbit.**  Two exact inverse orbits that both
converge to the model pseudo-orbit coincide: non-expansiveness of `B` makes
their distance at level `n` bounded by their distance at every later level. -/
theorem shadowing_orbit_unique {B : M → M} {Q X Y : ℕ → M} {r : ℕ → ℝ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y)
    (hX : ∀ n, B (X (n + 1)) = X n) (hY : ∀ n, B (Y (n + 1)) = Y n)
    (hXQ : ∀ n, dist (X n) (Q n) ≤ r n) (hYQ : ∀ n, dist (Y n) (Q n) ≤ r n)
    (hr : Tendsto r atTop (𝓝 0)) : X = Y := by
  have hiter : ∀ (m n : ℕ), X n = B^[m] (X (n + m)) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
        intro n
        calc X n = B^[m] (X (n + m)) := ih n
          _ = B^[m] (B (X (n + m + 1))) := by rw [hX (n + m)]
          _ = B^[m + 1] (X (n + (m + 1))) := by
              rw [show n + (m + 1) = n + m + 1 from by omega, Function.iterate_succ_apply]
  have hiterY : ∀ (m n : ℕ), Y n = B^[m] (Y (n + m)) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
        intro n
        calc Y n = B^[m] (Y (n + m)) := ih n
          _ = B^[m] (B (Y (n + m + 1))) := by rw [hY (n + m)]
          _ = B^[m + 1] (Y (n + (m + 1))) := by
              rw [show n + (m + 1) = n + m + 1 from by omega, Function.iterate_succ_apply]
  funext n
  have hle : ∀ m, dist (X n) (Y n) ≤ 2 * r (n + m) := by
    intro m
    calc dist (X n) (Y n) = dist (B^[m] (X (n + m))) (B^[m] (Y (n + m))) := by
          rw [← hiter m n, ← hiterY m n]
      _ ≤ dist (X (n + m)) (Y (n + m)) := dist_iterate_le hB m _ _
      _ ≤ dist (X (n + m)) (Q (n + m)) + dist (Q (n + m)) (Y (n + m)) := dist_triangle _ _ _
      _ ≤ 2 * r (n + m) := by
          have h1 := hXQ (n + m)
          have h2 := hYQ (n + m)
          rw [dist_comm (Y (n + m))] at h2
          linarith
  have hlim : Tendsto (fun m => 2 * r (n + m)) atTop (𝓝 0) := by
    have : Tendsto (fun m => r (n + m)) atTop (𝓝 0) := by
      have := hr.comp (Filter.tendsto_add_atTop_nat n)
      simpa [Function.comp, Nat.add_comm] using this
    simpa using this.const_mul 2
  have : dist (X n) (Y n) ≤ 0 := ge_of_tendsto' hlim hle
  exact dist_le_zero.mp this

/-- **The scheme part of the theorem *Regularizing backward shadowing*, in one
statement.**  For a non-expansive selected inverse `B` with left inverse `T` and
a pseudo-orbit `Q` with summable defects, there is an exact orbit `X` of `T`
which shadows `Q` within the tails `r_n = ∑_{m ≥ n} e_m`, whose Lipschitz
functionals are within `L r_n` of those of the model, and which is the unique
exact inverse orbit shadowing `Q` at rate `r`. -/
theorem exists_shadowing_orbit_all {B T : M → M} {Q : ℕ → M} {e : ℕ → ℝ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hsum : Summable e)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M,
      (∀ n, B (X (n + 1)) = X n) ∧
      (∀ n, T (X n) = X (n + 1)) ∧
      (∀ n, dist (X n) (Q n) ≤ ShadowingTails.tail e n) ∧
      (∀ (Phi : M → ℝ) (L : ℝ), 0 ≤ L → (∀ x y, |Phi x - Phi y| ≤ L * dist x y) →
        ∀ n, |Phi (X n) - Phi (Q n)| ≤ L * ShadowingTails.tail e n) ∧
      (∀ Y : ℕ → M, (∀ n, B (Y (n + 1)) = Y n) →
        (∀ n, dist (Y n) (Q n) ≤ ShadowingTails.tail e n) → Y = X) := by
  obtain ⟨X, -, hshadow, horb⟩ := exists_shadowing_orbit hB hcont hsum hdef
  refine ⟨X, horb, fun n => unitTangent_of_shadowing_orbit hT horb n, hshadow,
    fun Phi L hL hLip n => lipschitz_functional_shadowing hL hLip hshadow n, ?_⟩
  intro Y hYorb hYQ
  exact shadowing_orbit_unique hB hYorb horb hYQ hshadow
    (ShadowingTails.tail_tendsto_zero (e := e))

end ShadowingScheme
