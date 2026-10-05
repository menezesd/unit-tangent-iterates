module

public import UnitTangentIterates.UDiff
public import UnitTangentIterates.Reduction

/-!
# Growth of the maximum of a family of periodic functions

Let `f t u` be periodic and continuous in `u`, and differentiable in `t` uniformly in `u` with
derivative `fd t u`.  If `fd t u ≤ c` at every point `u` where `f t` attains its maximum, then
`max f t` grows at most at rate `c` (a Danskin-type argument).  This is how we control the
curvature along a path of rears without reparametrizing the path.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology Set

/-- Reduction of the curve parameter to a period. -/
lemma exists_mem_Ico_periodic_eq {p : ℝ} (hp : 0 < p) (u : ℝ) :
    ∃ u' ∈ Ico 0 p, ∀ g : ℝ → ℝ, Function.Periodic g p → g u = g u' := by
  refine ⟨toIcoMod hp 0 u, by simpa using toIcoMod_mem_Ico hp 0 u, fun g hg => ?_⟩
  rw [← hg.sub_zsmul_eq (toIcoDiv hp 0 u)]; rfl

/-- A continuous periodic function is bounded. -/
lemma exists_abs_le_of_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : Continuous f)
    (hfp : Function.Periodic f p) : ∃ B, ∀ u, |f u| ≤ B := by
  obtain ⟨u₀, hu₀⟩ := exists_max_of_periodic hp hf.abs (fun u => by simp only [hfp u])
  exact ⟨|f u₀|, hu₀⟩

section

variable {f fd : ℝ → ℝ → ℝ} {p c : ℝ}

/-- The maximum of `f t`. -/
noncomputable def pmax (f : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := sSup (range (f t))

lemma pmax_spec (hp : 0 < p) (hfc : ∀ t, Continuous (f t))
    (hfp : ∀ t, Function.Periodic (f t) p) (t : ℝ) :
    (∀ v, f t v ≤ pmax f t) ∧ ∃ u, f t u = pmax f t := by
  obtain ⟨u₀, hu₀⟩ := exists_max_of_periodic hp (hfc t) (hfp t)
  have hg : IsGreatest (range (f t)) (f t u₀) := ⟨⟨u₀, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hu₀ v⟩
  have e : pmax f t = f t u₀ := hg.csSup_eq
  exact ⟨fun v => e ▸ hu₀ v, u₀, e.symm⟩

/-- **Local step**: right after time `x`, the maximum grows at rate at most `c + ε`. -/
lemma pmax_local (hp : 0 < p) (hfc : ∀ t, Continuous (f t))
    (hfp : ∀ t, Function.Periodic (f t) p) (hfdc : ∀ t, Continuous (fd t))
    (hfdp : ∀ t, Function.Periodic (fd t) p) (hd : ∀ t, UDiffAt f (fd t) t)
    (hmax : ∀ t u, (∀ v, f t v ≤ f t u) → fd t u ≤ c) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[>] x, pmax f y ≤ pmax f x + (c + ε) * (y - x) := by
  obtain ⟨Bd, hBd⟩ := exists_abs_le_of_periodic hp (hfdc x) (hfdp x)
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans (hBd 0)
  obtain ⟨hFle, u₀, hu₀⟩ := pmax_spec hp hfc hfp x
  -- the points of a period where `fd x` is large form a compact set
  set K := {u ∈ Icc 0 p | c + ε / 2 ≤ fd x u}
  have hK : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (hfdc x))
  -- a positive gap `γ` between `max f x` and the values of `f x` on `K`
  obtain ⟨γ, hγ, hγK⟩ : ∃ γ > 0, ∀ u ∈ K, f x u ≤ pmax f x - γ := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1, one_pos, fun u hu => by simp [hK0] at hu⟩
    obtain ⟨u₁, hu₁K, hu₁⟩ := hK.exists_isMaxOn hKne (hfc x).continuousOn
    have hlt : f x u₁ < pmax f x := by
      rcases (hFle u₁).lt_or_eq with h | h
      · exact h
      · exfalso
        have : fd x u₁ ≤ c := hmax x u₁ fun v => h ▸ hFle v
        linarith [hu₁K.2]
    exact ⟨pmax f x - f x u₁, by linarith, fun u hu => by
      have : f x u ≤ f x u₁ := hu₁ hu
      linarith⟩
  set r := γ / (Bd + |c| + ε + 1)
  have hr : 0 < r := by positivity
  have hnear : ∀ᶠ y in 𝓝 x, |y - x| ≤ r := eventually_abs_sub_le x hr
  filter_upwards [nhdsWithin_le_nhds ((hd x) (ε / 2) (by positivity)),
    nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with y hy hyr hyx
  have hyx' : 0 < y - x := sub_pos.2 hyx
  obtain ⟨uy, huy⟩ := (pmax_spec hp hfc hfp y).2
  rw [← huy]
  obtain ⟨u', hu', hper⟩ := exists_mem_Ico_periodic_eq hp uy
  rw [hper _ (hfp y)]
  have h1 := hy u'
  rw [abs_of_pos hyx'] at h1 hyr
  have h2 : f y u' ≤ f x u' + (y - x) * fd x u' + ε / 2 * (y - x) := by
    linarith [le_abs_self (f y u' - f x u' - (y - x) * fd x u')]
  by_cases hu'K : u' ∈ K
  · have h3 := hγK u' hu'K
    have h4 : (y - x) * fd x u' ≤ (y - x) * Bd :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hBd u')) hyx'.le
    have h5 : (y - x) * (Bd + |c| + ε + 1) ≤ γ := by
      exact (le_div_iff₀ (by positivity)).1 hyr
    have h6 : -|c| ≤ c := neg_abs_le c
    nlinarith
  · have hlt : fd x u' < c + ε / 2 := by
      by_contra h
      exact hu'K ⟨Ico_subset_Icc_self hu', not_lt.1 h⟩
    have h4 : (y - x) * fd x u' ≤ (y - x) * (c + ε / 2) :=
      mul_le_mul_of_nonneg_left hlt.le hyx'.le
    nlinarith [hFle u']

lemma continuous_pmax (hp : 0 < p) (hfc : ∀ t, Continuous (f t))
    (hfp : ∀ t, Function.Periodic (f t) p) (hfdc : ∀ t, Continuous (fd t))
    (hfdp : ∀ t, Function.Periodic (fd t) p) (hd : ∀ t, UDiffAt f (fd t) t) :
    Continuous (pmax f) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨Bd, hBd⟩ := exists_abs_le_of_periodic hp (hfdc x) (hfdp x)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(hd x).lip hBd, eventually_abs_sub_le x (r := ε / (2 * (Bd + 2)))
    (by have := (abs_nonneg _).trans (hBd 0); positivity)] with y hy hyr
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans (hBd 0)
  have hδ : (Bd + 1) * |y - x| ≤ ε / 2 := by
    calc (Bd + 1) * |y - x| ≤ (Bd + 2) * (ε / (2 * (Bd + 2))) := by
          gcongr; linarith
      _ = ε / 2 := by field_simp
  obtain ⟨hy1, uy, huy⟩ := pmax_spec hp hfc hfp y
  obtain ⟨hx1, ux, hux⟩ := pmax_spec hp hfc hfp x
  rw [Real.dist_eq, abs_lt]
  have a1 := hy ux
  have a2 := hy uy
  constructor
  · have := hy1 ux
    linarith [neg_abs_le (f y ux - f x ux)]
  · have := hx1 uy
    linarith [le_abs_self (f y uy - f x uy)]

/-- **Growth of the maximum.**  If `fd t u ≤ c` wherever `f t` is maximal, then for `t₀ ≤ t₁`
and `f t₀ ≤ B` we have `f t₁ ≤ B + c (t₁ - t₀)`. -/
theorem max_growth (hp : 0 < p) (hfc : ∀ t, Continuous (f t))
    (hfp : ∀ t, Function.Periodic (f t) p) (hfdc : ∀ t, Continuous (fd t))
    (hfdp : ∀ t, Function.Periodic (fd t) p) (hd : ∀ t, UDiffAt f (fd t) t)
    (hmax : ∀ t u, (∀ v, f t v ≤ f t u) → fd t u ≤ c) {t₀ t₁ B : ℝ} (h01 : t₀ ≤ t₁)
    (hB : ∀ v, f t₀ v ≤ B) (u : ℝ) : f t₁ u ≤ B + c * (t₁ - t₀) := by
  have hF := continuous_pmax hp hfc hfp hfdc hfdp hd
  have key : ∀ ε > 0, pmax f t₁ ≤ pmax f t₀ + (c + ε) * (t₁ - t₀) := by
    intro ε hε
    set s := {t | pmax f t ≤ pmax f t₀ + (c + ε) * (t - t₀)}
    have hs : IsClosed s := isClosed_le hF (by fun_prop)
    have hsub : Icc t₀ t₁ ⊆ s := by
      refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hs.inter isClosed_Icc)
        (by simp [s]) fun x hx => ?_
      filter_upwards [pmax_local hp hfc hfp hfdc hfdp hd hmax x hε] with y hy
      have hx1 : pmax f x ≤ pmax f t₀ + (c + ε) * (x - t₀) := hx.1
      show pmax f y ≤ pmax f t₀ + (c + ε) * (y - t₀)
      linarith
    exact hsub ⟨h01, le_rfl⟩
  have hB' : pmax f t₀ ≤ B := by
    obtain ⟨u₀, hu₀⟩ := (pmax_spec hp hfc hfp t₀).2
    rw [← hu₀]; exact hB u₀
  have h1 : pmax f t₁ ≤ pmax f t₀ + c * (t₁ - t₀) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have ht : 0 ≤ t₁ - t₀ := by linarith
    have := key (ε / (t₁ - t₀ + 1)) (by positivity)
    have h2 : ε / (t₁ - t₀ + 1) * (t₁ - t₀) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith
  linarith [(pmax_spec hp hfc hfp t₁).1 u]

end

end Ovals

end
