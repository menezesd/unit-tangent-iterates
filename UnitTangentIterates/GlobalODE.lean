import Mathlib

/-!
# Global solutions of a bounded, globally Lipschitz ODE

The normal-gauge reparametrization of the shadowing section requires solving
the flow equation `φ' = h(t, φ)` on the whole path parameter interval.
Mathlib's Picard–Lindelöf theorem produces solutions on a compact interval
under the local hypotheses of `IsPicardLindelof`; for a field which is
**globally** Lipschitz in the state and **globally bounded**, those hypotheses
hold on every compact interval (the radius of the ball may be taken as large as
the interval requires), and uniqueness (Grönwall) glues the solutions into a
single global one.

Main results:

* `exists_solution_Icc` — a solution on any compact interval;
* `exists_global_solution` — a solution defined on all of `ℝ`;
* `exists_global_solution_real` — the scalar case, in the form used for the
  normal-gauge flow;
* `dist_le_of_global_solutions` — Grönwall's two-sided bound: two global
  solutions separate at most exponentially, so the solution depends
  Lipschitz-continuously on its initial condition.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {K L : ℝ≥0}

/-- **Existence on a compact interval.**  A field which is globally Lipschitz
in the state, continuous in the time and globally bounded satisfies the
Picard–Lindelöf hypotheses on every compact interval, with a ball large enough
for the whole interval. -/
theorem exists_solution_Icc (hlip : ∀ t, LipschitzWith K (f t))
    (hcont : ∀ x, Continuous fun t => f t x) (hbd : ∀ t x, ‖f t x‖ ≤ L)
    (x₀ : E) (tmin tmax : ℝ) (t₀ : Icc tmin tmax) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  have hmax : (0:ℝ) ≤ max (tmax - (t₀:ℝ)) ((t₀:ℝ) - tmin) := by
    have h := t₀.2
    simp only [mem_Icc] at h
    exact le_max_of_le_left (by linarith [h.2])
  set a : ℝ≥0 := ⟨L * max (tmax - (t₀:ℝ)) ((t₀:ℝ) - tmin), by positivity⟩ with ha
  have hPL : IsPicardLindelof f t₀ x₀ a 0 L K := by
    constructor
    · intro t _; exact (hlip t).lipschitzOnWith
    · intro x _; exact (hcont x).continuousOn
    · intro t _ x _; exact hbd t x
    · simp [ha]
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

omit [CompleteSpace E] in
/-- **Global existence from solutions on an exhausting sequence of windows.**
Uniqueness (Grönwall) glues solutions on the intervals `[t₀ − n − 1, t₀ + n + 1]`
into a single solution on the whole line.  Only the Lipschitz constant is used;
how the solutions on the windows are produced is immaterial. -/
theorem exists_global_solution_of_windows (hlip : ∀ t, LipschitzWith K (f t))
    (t₀ : ℝ) (x₀ : E)
    (hloc : ∀ n : ℕ, ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc (t₀ - (n + 1 : ℝ)) (t₀ + (n + 1 : ℝ)),
        HasDerivWithinAt α (f t (α t)) (Icc (t₀ - (n + 1 : ℝ)) (t₀ + (n + 1 : ℝ))) t) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (f t (α t)) t := by
  choose α hα0 hαd using hloc
  -- on the interior the derivative is a genuine derivative
  have hderiv : ∀ (n : ℕ) (t : ℝ), |t - t₀| < (n : ℝ) + 1 →
      HasDerivAt (α n) (f t (α n t)) t := by
    intro n t ht
    rw [abs_lt] at ht
    have hIcc : Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1)) ∈ nhds t :=
      Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
    exact (hαd n t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt hIcc
  have hcontOn : ∀ n : ℕ, ContinuousOn (α n)
      (Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1))) := by
    intro n t ht
    exact (hαd n t ht).continuousWithinAt
  -- the solutions agree where they are both defined
  have hagree : ∀ m n : ℕ, m ≤ n →
      EqOn (α m) (α n) (Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1))) := by
    intro m n hmn
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith
    have hsub : Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1))
        ⊆ Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1)) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht0 : t₀ ∈ Ioo (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)) := by
      constructor <;> [linarith [Nat.cast_nonneg (α := ℝ) m];
        linarith [Nat.cast_nonneg (α := ℝ) m]]
    have hIoo : ∀ t ∈ Ioo (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)),
        |t - t₀| < (m : ℝ) + 1 := by
      intro t ht
      rw [abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ODE_solution_unique_of_mem_Icc (K := K) (s := fun _ => univ)
      (fun t _ => (hlip t).lipschitzOnWith) ht0 (hcontOn m)
      (fun t ht => hderiv m t (hIoo t ht)) (fun _ _ => trivial)
      ((hcontOn n).mono hsub)
      (fun t ht => hderiv n t (lt_of_lt_of_le (hIoo t ht) hmn')) (fun _ _ => trivial) ?_
    rw [hα0 m, hα0 n]
  -- the global solution
  set N : ℝ → ℕ := fun t => ⌈|t - t₀|⌉₊ with hN
  set φ : ℝ → E := fun t => α (N t) t with hφ
  have hNle : ∀ t : ℝ, |t - t₀| ≤ (N t : ℝ) := fun t => Nat.le_ceil _
  have hkey : ∀ (n : ℕ) (t : ℝ), |t - t₀| < (n : ℝ) + 1 → φ t = α n t := by
    intro n t ht
    have h1 : |t - t₀| ≤ ((min (N t) n : ℕ) : ℝ) + 1 := by
      rcases le_total (N t) n with h | h
      · simp only [min_eq_left h]
        linarith [hNle t]
      · simp only [min_eq_right h]
        linarith [ht.le]
    rw [abs_le] at h1
    have hmem' : t ∈ Icc (t₀ - (((min (N t) n : ℕ) : ℝ) + 1))
        (t₀ + (((min (N t) n : ℕ) : ℝ) + 1)) :=
      ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have ha1 := hagree (min (N t) n) (N t) (min_le_left _ _) hmem'
    have ha2 := hagree (min (N t) n) n (min_le_right _ _) hmem'
    show α (N t) t = α n t
    rw [← ha1, ha2]
  refine ⟨φ, ?_, ?_⟩
  · have : |t₀ - t₀| < ((0 : ℕ) : ℝ) + 1 := by simp
    rw [hkey 0 t₀ this, hα0 0]
  · intro t
    set n : ℕ := N t + 1 with hn
    have htn : |t - t₀| < (n : ℝ) + 1 := by
      have := hNle t
      push_cast [hn]
      linarith
    have heq : φ =ᶠ[nhds t] α n := by
      have hopen : Ioo (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1)) ∈ nhds t := by
        rw [abs_lt] at htn
        exact Ioo_mem_nhds (by linarith [htn.1]) (by linarith [htn.2])
      filter_upwards [hopen] with t' ht'
      refine hkey n t' ?_
      rw [abs_lt]
      exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    have hd := hderiv n t htn
    have hval : φ t = α n t := hkey n t htn
    rw [hval]
    exact hd.congr_of_eventuallyEq heq

/-- **Global existence.**  A field which is globally Lipschitz in the state,
continuous in the time and globally bounded has, for every initial condition, a
solution defined on the whole line. -/
theorem exists_global_solution (hlip : ∀ t, LipschitzWith K (f t))
    (hcont : ∀ x, Continuous fun t => f t x) (hbd : ∀ t x, ‖f t x‖ ≤ L)
    (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (f t (α t)) t := by
  refine exists_global_solution_of_windows hlip t₀ x₀ (fun n => ?_)
  have hmem : t₀ ∈ Icc (t₀ - (n + 1 : ℝ)) (t₀ + (n + 1 : ℝ)) := by
    constructor <;> [linarith [Nat.cast_nonneg (α := ℝ) n]; linarith [Nat.cast_nonneg (α := ℝ) n]]
  exact exists_solution_Icc hlip hcont hbd x₀ (t₀ - (n + 1 : ℝ)) (t₀ + (n + 1 : ℝ)) ⟨t₀, hmem⟩

omit [CompleteSpace E] in
/-- **Continuous dependence on the initial condition.**  Two global solutions
of the same globally Lipschitz field satisfy
`dist (α₁ t) (α₂ t) ≤ dist (α₁ t₀) (α₂ t₀) · e^{K|t - t₀|}`, on both sides of
the initial time. -/
theorem dist_le_of_global_solutions {α₁ α₂ : ℝ → E} (hlip : ∀ t, LipschitzWith K (f t))
    (h₁ : ∀ t, HasDerivAt α₁ (f t (α₁ t)) t) (h₂ : ∀ t, HasDerivAt α₂ (f t (α₂ t)) t)
    (t₀ t : ℝ) :
    dist (α₁ t) (α₂ t) ≤ dist (α₁ t₀) (α₂ t₀) * Real.exp (K * |t - t₀|) := by
  rcases le_total t₀ t with hle | hle
  · have hb := dist_le_of_trajectories_ODE (v := f) (K := K) (a := t₀) (b := t)
      (δ := dist (α₁ t₀) (α₂ t₀)) hlip
      (fun s _ => (h₁ s).continuousAt.continuousWithinAt)
      (fun s _ => (h₁ s).hasDerivWithinAt)
      (fun s _ => (h₂ s).continuousAt.continuousWithinAt)
      (fun s _ => (h₂ s).hasDerivWithinAt) le_rfl t ⟨hle, le_rfl⟩
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - t₀)]
  · -- reflect the time
    set g : ℝ → E → E := fun s x => -f (2 * t₀ - s) x with hg
    have hglip : ∀ s, LipschitzWith K (g s) := by
      intro s
      exact (hlip (2 * t₀ - s)).neg
    have hrefl : ∀ (β : ℝ → E), (∀ r, HasDerivAt β (f r (β r)) r) →
        ∀ s, HasDerivAt (fun s' => β (2 * t₀ - s')) (g s (β (2 * t₀ - s))) s := by
      intro β hβ s
      have hlin : HasDerivAt (fun s' : ℝ => 2 * t₀ - s') (-1) s := by
        simpa using (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s)
      have := (hβ (2 * t₀ - s)).scomp s hlin
      refine this.congr_deriv ?_
      simp [hg]
    have hb := dist_le_of_trajectories_ODE (v := g) (K := K) (a := t₀) (b := 2 * t₀ - t)
      (f := fun s => α₁ (2 * t₀ - s)) (g := fun s => α₂ (2 * t₀ - s))
      (δ := dist (α₁ t₀) (α₂ t₀)) hglip
      (fun s _ => (hrefl α₁ h₁ s).continuousAt.continuousWithinAt)
      (fun s _ => (hrefl α₁ h₁ s).hasDerivWithinAt)
      (fun s _ => (hrefl α₂ h₂ s).continuousAt.continuousWithinAt)
      (fun s _ => (hrefl α₂ h₂ s).hasDerivWithinAt)
      (by simp only [show 2 * t₀ - t₀ = t₀ by ring]; exact le_rfl)
      (2 * t₀ - t) ⟨by linarith, le_rfl⟩
    have hsimp : 2 * t₀ - (2 * t₀ - t) = t := by ring
    simp only [hsimp] at hb
    rwa [abs_of_nonpos (by linarith : t - t₀ ≤ 0), show -(t - t₀) = 2 * t₀ - t - t₀ by ring]

/-- **Global existence, scalar case.**  The form used for the normal-gauge
flow `φ' = -ξ/v`: a bounded, globally Lipschitz scalar field admits a solution
on the whole line for every initial condition. -/
theorem exists_global_solution_real {h : ℝ → ℝ → ℝ} {K L : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : ∀ x, Continuous fun t => h t x)
    (hbd : ∀ t x, |h t x| ≤ L) (t₀ x₀ : ℝ) :
    ∃ φ : ℝ → ℝ, φ t₀ = x₀ ∧ ∀ t, HasDerivAt φ (h t (φ t)) t :=
  exists_global_solution hlip hcont (fun t x => by simpa using hbd t x) t₀ x₀

end GlobalODE
