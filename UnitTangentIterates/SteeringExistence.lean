import Mathlib
import UnitTangentIterates.Shadowing

/-!
# Existence of the periodic steering solution on the closed strip

This file supplies the existence half of the lemma *Selected inverse on the
closed strip* of *A Noncircular Oval with Convex Unit-Tangent Iterates*:

> Let `F` be a regular convex `C²` closed curve with `0 ≤ K ≤ κ̂ < 1`.  There is
> a unique periodic steering solution `0 ≤ δ ≤ arcsin κ̂` of `δ_s = K − sin δ`.

The uniqueness half is `Shadowing.steering_unique`, and the trapping mechanism
(the vector field points into the strip) is in `LowCurvatureInverse`.  What was
missing — and is proved here — is that a periodic solution inside the strip
actually *exists*.  The argument is the one the paper indicates: the Poincaré
map of the strip is well defined and maps the strip into itself, so it has a
fixed point, and the corresponding solution extends periodically.

The steps are:

* `exists_clamped_solution` — Picard–Lindelöf existence, on `[0, S]`, of a
  solution of the *clamped* equation `δ' = K − sin (clamp δ)`, whose field is
  globally Lipschitz and bounded, so a solution exists on the whole interval;
* `le_of_deriv_nonpos_Icc`, `ge_of_deriv_nonneg_Icc` — barrier lemmas: a
  solution cannot cross a level at which the field points inward;
* `clamped_solution_mem_strip` — hence every solution of the clamped equation
  starting in `[0, arcsin κ̂]` stays there, where it solves the true equation;
* `sol_nonexpansive` — two solutions inside the strip never spread apart, so
  the Poincaré map is continuous (indeed non-expansive);
* `periodic_extension` — a solution on `[0, S]` with equal endpoint values
  extends to a genuine `S`-periodic solution on `ℝ`;
* `exists_periodic_steering` and `existsUnique_periodic_steering` — the
  resulting existence and uniqueness statement, with the lower bound
  `cos δ ≥ √(1 − κ̂²)` for the rear speed.
-/

noncomputable section

open Real Set

namespace SteeringExistence

/-! ### The clamped steering field -/

/-- The clamp of `x` to the interval `[0, a]`. -/
def clampAt (a x : ℝ) : ℝ := max (min x a) 0

theorem clampAt_lipschitz (a : ℝ) : LipschitzWith 1 (clampAt a) :=
  ((LipschitzWith.id).min_const a).max_const 0

theorem clampAt_of_mem {a x : ℝ} (hx : x ∈ Icc (0:ℝ) a) : clampAt a x = x := by
  simp [clampAt, min_eq_left hx.2, max_eq_left hx.1]

theorem clampAt_of_le {a x : ℝ} (ha : 0 ≤ a) (hx : a ≤ x) : clampAt a x = a := by
  simp [clampAt, min_eq_right hx, max_eq_left ha]

theorem clampAt_of_nonpos {a x : ℝ} (ha : 0 ≤ a) (hx : x ≤ 0) : clampAt a x = 0 := by
  simp [clampAt, min_eq_left (hx.trans ha), max_eq_right hx]

theorem sin_clampAt_lipschitz (a : ℝ) :
    LipschitzWith 1 (fun x : ℝ => Real.sin (clampAt a x)) := by
  simpa using (Real.lipschitzWith_sin.comp (clampAt_lipschitz a))

theorem clamped_field_lipschitz (c a : ℝ) :
    LipschitzWith 1 (fun x : ℝ => c - Real.sin (clampAt a x)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := (sin_clampAt_lipschitz a).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h ⊢
  calc |c - Real.sin (clampAt a x) - (c - Real.sin (clampAt a y))|
      = |Real.sin (clampAt a x) - Real.sin (clampAt a y)| := by rw [← abs_neg]; ring_nf
    _ ≤ |x - y| := h

/-! ### Existence for the clamped equation -/

/-- **Picard–Lindelöf existence for the clamped steering equation.**  The
clamped field `x ↦ K s − sin (clamp x)` is globally `1`-Lipschitz and bounded,
so for every initial value there is a solution on the whole interval `[0, S]`. -/
theorem exists_clamped_solution {K : ℝ → ℝ} (hK : Continuous K) {S : ℝ} (hS : 0 ≤ S) (a y : ℝ) :
    ∃ u : ℝ → ℝ, u 0 = y ∧
      ∀ s ∈ Icc 0 S, HasDerivWithinAt u (K s - Real.sin (clampAt a (u s))) (Icc 0 S) s := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := S)).exists_bound_of_continuousOn hK.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hS⟩)
  set f : ℝ → ℝ → ℝ := fun s x => K s - Real.sin (clampAt a x) with hf
  set L : NNReal := ⟨M + 1, by linarith⟩ with hL
  set A : NNReal := ⟨(M + 1) * S, by positivity⟩ with hA
  have ht0 : (0:ℝ) ∈ Icc (0:ℝ) S := ⟨le_rfl, hS⟩
  have hpl : IsPicardLindelof f (t₀ := (⟨0, ht0⟩ : Icc (0:ℝ) S)) (x₀ := y) A 0 L 1 := by
    constructor
    · exact fun t _ => (clamped_field_lipschitz (K t) a).lipschitzOnWith
    · exact fun x _ => (hK.sub continuous_const).continuousOn
    · intro t ht x _
      have h1 : ‖K t‖ ≤ M := hM t ht
      have h2 : |Real.sin (clampAt a x)| ≤ 1 := Real.abs_sin_le_one _
      rw [Real.norm_eq_abs] at h1
      simp only [hf, Real.norm_eq_abs]
      calc |K t - Real.sin (clampAt a x)| ≤ |K t| + |Real.sin (clampAt a x)| := abs_sub _ _
        _ ≤ M + 1 := by linarith
    · simp only [hA, hL, NNReal.coe_mk, sub_zero, NNReal.coe_zero]
      rw [max_eq_left hS]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-! ### Barriers -/

/-- **A solution cannot cross an upper barrier at which the field is
nonpositive** (version for a solution defined on `[0, S]`). -/
theorem le_of_deriv_nonpos_Icc {v w : ℝ → ℝ} {S a : ℝ}
    (hderiv : ∀ s ∈ Icc 0 S, HasDerivWithinAt v (w s) (Icc 0 S) s)
    (hsign : ∀ s ∈ Icc 0 S, a ≤ v s → w s ≤ 0)
    (h0 : v 0 ≤ a) : ∀ s ∈ Icc 0 S, v s ≤ a := by
  have hcont : ContinuousOn v (Icc 0 S) := fun s hs => (hderiv s hs).continuousWithinAt
  intro t ht
  by_contra hcon
  push_neg at hcon
  have hSt : t ≤ S := ht.2
  have h0t : 0 ≤ t := ht.1
  set T : Set ℝ := Icc 0 t ∩ v ⁻¹' Iic a with hT
  have hsub : Icc 0 t ⊆ Icc 0 S := Icc_subset_Icc le_rfl hSt
  have hTclosed : IsClosed T :=
    (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hTcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed inter_subset_left
  have hTne : T.Nonempty := ⟨0, ⟨⟨le_rfl, h0t⟩, h0⟩⟩
  have hmem : sSup T ∈ T := hTcompact.sSup_mem hTne
  set t0 := sSup T with ht0def
  have ht0t : t0 < t := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exact absurd (h ▸ hmem.2 : v t ≤ a) (not_le.mpr hcon)
  have hgt : ∀ u ∈ Ioo t0 t, a ≤ v u := by
    intro u hu
    by_contra hu'
    push_neg at hu'
    have huT : u ∈ T := ⟨⟨le_trans hmem.1.1 hu.1.le, hu.2.le⟩, hu'.le⟩
    exact absurd (le_csSup hTcompact.bddAbove huT) (not_le.mpr hu.1)
  have hsub2 : Icc t0 t ⊆ Icc 0 S := Icc_subset_Icc hmem.1.1 hSt
  have hderivAt : ∀ x ∈ Ioo t0 t, HasDerivAt v (w x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hmem.1.1 hx.1
    have hxS : x < S := lt_of_lt_of_le hx.2 hSt
    exact (hderiv x ⟨hx0.le, hxS.le⟩).hasDerivAt (Icc_mem_nhds hx0 hxS)
  have hanti : AntitoneOn v (Icc t0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hcont.mono hsub2) ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderivAt x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderivAt x hx).deriv]
      exact hsign x (hsub2 (Ioo_subset_Icc_self hx)) (hgt x hx)
  have hle := hanti (left_mem_Icc.mpr ht0t.le) (right_mem_Icc.mpr ht0t.le) ht0t.le
  exact absurd (le_trans hle hmem.2) (not_le.mpr hcon)

/-- The mirror statement: a solution cannot cross a lower barrier at which the
field is nonnegative. -/
theorem ge_of_deriv_nonneg_Icc {v w : ℝ → ℝ} {S c : ℝ}
    (hderiv : ∀ s ∈ Icc 0 S, HasDerivWithinAt v (w s) (Icc 0 S) s)
    (hsign : ∀ s ∈ Icc 0 S, v s ≤ c → 0 ≤ w s)
    (h0 : c ≤ v 0) : ∀ s ∈ Icc 0 S, c ≤ v s := by
  have hderiv' : ∀ s ∈ Icc 0 S, HasDerivWithinAt (fun t => -v t) (-w s) (Icc 0 S) s :=
    fun s hs => (hderiv s hs).neg
  have hsign' : ∀ s ∈ Icc 0 S, -c ≤ -v s → -w s ≤ 0 := by
    intro s hs h
    have : v s ≤ c := by linarith
    linarith [hsign s hs this]
  have := le_of_deriv_nonpos_Icc hderiv' hsign' (by linarith)
  intro s hs
  linarith [this s hs]

/-! ### The strip is invariant -/

/-- **The closed strip `[0, arcsin κ̂]` is invariant.**  A solution of the
clamped equation which starts in the strip stays in it: the field is `≥ 0` at
the lower barrier and `≤ 0` at the upper one. -/
theorem clamped_solution_mem_strip {u K : ℝ → ℝ} {S a : ℝ} (ha : 0 ≤ a)
    (hK0 : ∀ s, 0 ≤ K s) (hKa : ∀ s, K s ≤ Real.sin a)
    (hu : ∀ s ∈ Icc 0 S, HasDerivWithinAt u (K s - Real.sin (clampAt a (u s))) (Icc 0 S) s)
    (h0 : u 0 ∈ Icc 0 a) : ∀ s ∈ Icc 0 S, u s ∈ Icc 0 a := by
  have hup : ∀ s ∈ Icc 0 S, u s ≤ a := by
    refine le_of_deriv_nonpos_Icc hu (fun s _ hs => ?_) h0.2
    rw [clampAt_of_le ha hs]
    linarith [hKa s]
  have hlo : ∀ s ∈ Icc 0 S, 0 ≤ u s := by
    refine ge_of_deriv_nonneg_Icc hu (fun s _ hs => ?_) h0.1
    rw [clampAt_of_nonpos ha hs]
    simpa using hK0 s
  exact fun s hs => ⟨hlo s hs, hup s hs⟩

/-! ### Non-expansiveness inside the strip -/

/-- **Two steering solutions inside the strip never spread apart.**  This makes
the Poincaré map of the strip continuous. -/
theorem sol_nonexpansive {u1 u2 K : ℝ → ℝ} {S a : ℝ} (hapi : a ≤ π / 2)
    (h1 : ∀ s ∈ Icc 0 S, HasDerivWithinAt u1 (K s - Real.sin (u1 s)) (Icc 0 S) s)
    (h2 : ∀ s ∈ Icc 0 S, HasDerivWithinAt u2 (K s - Real.sin (u2 s)) (Icc 0 S) s)
    (hr1 : ∀ s ∈ Icc 0 S, u1 s ∈ Icc 0 a) (hr2 : ∀ s ∈ Icc 0 S, u2 s ∈ Icc 0 a) :
    ∀ s ∈ Icc 0 S, |u1 s - u2 s| ≤ |u1 0 - u2 0| := by
  intro s hs
  have hS : 0 ≤ S := le_trans hs.1 hs.2
  set g : ℝ → ℝ := fun t => (u1 t - u2 t) ^ 2 with hg
  have hderivAt : ∀ x ∈ Ioo (0:ℝ) S, HasDerivAt g
      (2 * (u1 x - u2 x) * (-(Real.sin (u1 x) - Real.sin (u2 x)))) x := by
    intro x hx
    have hmem : x ∈ Icc (0:ℝ) S := Ioo_subset_Icc_self hx
    have hd1 : HasDerivAt u1 (K x - Real.sin (u1 x)) x :=
      (h1 x hmem).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    have hd2 : HasDerivAt u2 (K x - Real.sin (u2 x)) x :=
      (h2 x hmem).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    have hpow := (hd1.sub hd2).pow 2
    simp only [hg]
    convert hpow using 1
    simp only [Pi.sub_apply]
    ring
  have hsign : ∀ x ∈ Ioo (0:ℝ) S,
      2 * (u1 x - u2 x) * (-(Real.sin (u1 x) - Real.sin (u2 x))) ≤ 0 := by
    intro x hx
    have hmem : x ∈ Icc (0:ℝ) S := Ioo_subset_Icc_self hx
    have hm1 := hr1 x hmem
    have hm2 := hr2 x hmem
    have hpi := Real.pi_pos
    have hI1 : u1 x ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hm1.1], le_trans hm1.2 hapi⟩
    have hI2 : u2 x ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hm2.1], le_trans hm2.2 hapi⟩
    have hmono := Real.strictMonoOn_sin.monotoneOn
    rcases le_total (u2 x) (u1 x) with h | h
    · nlinarith [hmono hI2 hI1 h]
    · nlinarith [hmono hI1 hI2 h]
  have hcont : ContinuousOn g (Icc 0 S) := by
    have c1 : ContinuousOn u1 (Icc 0 S) := fun t ht => (h1 t ht).continuousWithinAt
    have c2 : ContinuousOn u2 (Icc 0 S) := fun t ht => (h2 t ht).continuousWithinAt
    exact (c1.sub c2).pow 2
  have hanti : AntitoneOn g (Icc 0 S) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderivAt x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderivAt x hx).deriv]
      exact hsign x hx
  exact sq_le_sq.mp (hanti ⟨le_rfl, hS⟩ hs hs.1)

/-! ### Periodic extension of a solution with equal endpoint values -/

theorem toIcoMod_sub_int_mul {S : ℝ} (hS : 0 < S) (n : ℤ) (t : ℝ)
    (ht : t - n * S ∈ Ico (0:ℝ) S) : toIcoMod hS 0 t = t - n * S := by
  rw [toIcoMod_eq_iff hS]
  refine ⟨by simpa using ht, n, ?_⟩
  simp [zsmul_eq_mul]

/-- **Periodic extension.**  A solution of `δ' = K − sin δ` on `[0, S]` whose
endpoint values agree extends, by `S`-periodicity, to a solution on all of `ℝ`
(here `K` is `S`-periodic). -/
theorem periodic_extension {u K : ℝ → ℝ} {S : ℝ} (hS : 0 < S)
    (hKper : Function.Periodic K S)
    (hu : ∀ s ∈ Icc 0 S, HasDerivWithinAt u (K s - Real.sin (u s)) (Icc 0 S) s)
    (hend : u S = u 0) (s : ℝ) :
    HasDerivAt (fun t => u (toIcoMod hS 0 t)) (K s - Real.sin (u (toIcoMod hS 0 s))) s := by
  set n : ℤ := toIcoDiv hS 0 s with hn
  set x : ℝ := toIcoMod hS 0 s with hxdef
  have hx : x ∈ Ico (0:ℝ) S := by simpa using toIcoMod_mem_Ico hS 0 s
  have hsx : s = x + n * S := by
    have h := toIcoMod_add_toIcoDiv_zsmul hS 0 s
    rw [zsmul_eq_mul] at h
    exact h.symm
  have hKx : K x = K s := by
    have h := hKper.sub_int_mul_eq (x := s) n
    rw [show s - (n:ℝ) * S = x by linarith] at h
    exact h
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · -- junction case `x = 0`
    have hx0 : x = 0 := h0.symm
    have hsn : s = n * S := by rw [hsx, hx0]; ring
    have hs0 : s - (n:ℝ) * S = 0 := by rw [hsn]; ring
    have hKs : K s = K 0 := by rw [hsn]; exact hKper.int_mul_eq n
    have hgoal : K s - Real.sin (u x) = K 0 - Real.sin (u 0) := by rw [hKs, hx0]
    rw [hgoal]
    have hright : HasDerivWithinAt (fun t => u (toIcoMod hS 0 t)) (K 0 - Real.sin (u 0))
        (Ici s) s := by
      have hmaps : Set.MapsTo (fun t : ℝ => t - (n:ℝ) * S) (Icc s (s + S)) (Icc 0 S) :=
        fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hshift : HasDerivWithinAt (fun t : ℝ => t - (n:ℝ) * S) 1 (Icc s (s + S)) s :=
        ((hasDerivAt_id s).sub_const ((n:ℝ) * S)).hasDerivWithinAt
      have h0' : HasDerivWithinAt u (K 0 - Real.sin (u 0)) (Icc 0 S)
          ((fun t : ℝ => t - (n:ℝ) * S) s) := by
        simp only [hs0]; exact hu 0 ⟨le_rfl, hS.le⟩
      have hg : HasDerivWithinAt (fun t => u (t - (n:ℝ) * S)) (K 0 - Real.sin (u 0))
          (Icc s (s + S)) s := by simpa using h0'.scomp s hshift hmaps
      have hcongr : ∀ t ∈ Icc s (s + S), u (toIcoMod hS 0 t) = u (t - (n:ℝ) * S) := by
        intro t ht
        rcases lt_or_eq_of_le ht.2 with hlt | heq
        · rw [toIcoMod_sub_int_mul hS n t ⟨by linarith [ht.1], by linarith⟩]
        · have hz : toIcoMod hS 0 t = 0 := by
            rw [toIcoMod_sub_int_mul hS (n + 1) t ⟨by push_cast; linarith, by push_cast; linarith⟩]
            push_cast; linarith
          rw [hz, show t - (n:ℝ) * S = S by linarith, hend]
      exact (hg.congr hcongr (hcongr s ⟨le_rfl, by linarith⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE (by linarith))
    have hleft : HasDerivWithinAt (fun t => u (toIcoMod hS 0 t)) (K 0 - Real.sin (u 0))
        (Iic s) s := by
      have hmaps : Set.MapsTo (fun t : ℝ => t - ((n:ℝ) - 1) * S) (Icc (s - S) s) (Icc 0 S) :=
        fun t ht => ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
      have hshift : HasDerivWithinAt (fun t : ℝ => t - ((n:ℝ) - 1) * S) 1 (Icc (s - S) s) s :=
        ((hasDerivAt_id s).sub_const (((n:ℝ) - 1) * S)).hasDerivWithinAt
      have hsS : s - ((n:ℝ) - 1) * S = S := by rw [hsn]; ring
      have hval : K S - Real.sin (u S) = K 0 - Real.sin (u 0) := by
        rw [hend, show K S = K 0 by simpa using hKper 0]
      have h0' : HasDerivWithinAt u (K 0 - Real.sin (u 0)) (Icc 0 S)
          ((fun t : ℝ => t - ((n:ℝ) - 1) * S) s) := by
        simp only [hsS]; rw [← hval]; exact hu S ⟨hS.le, le_rfl⟩
      have hg : HasDerivWithinAt (fun t => u (t - ((n:ℝ) - 1) * S)) (K 0 - Real.sin (u 0))
          (Icc (s - S) s) s := by simpa using h0'.scomp s hshift hmaps
      have hcongr : ∀ t ∈ Icc (s - S) s, u (toIcoMod hS 0 t) = u (t - ((n:ℝ) - 1) * S) := by
        intro t ht
        rcases lt_or_eq_of_le ht.2 with hlt | heq
        · rw [toIcoMod_sub_int_mul hS (n - 1) t
            ⟨by push_cast; linarith [ht.1], by push_cast; linarith⟩]
          push_cast; ring_nf
        · subst heq
          rw [← hxdef, hx0, hsS, hend]
      exact (hg.congr hcongr (hcongr s ⟨by linarith, le_rfl⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE (by linarith))
    have hunion := hleft.union hright
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hunion
    exact hunion
  · -- interior case
    have hmemIoo : s ∈ Ioo ((n:ℝ) * S) ((n:ℝ) * S + S) := ⟨by linarith, by linarith [hx.2]⟩
    have hux : HasDerivAt u (K x - Real.sin (u x)) x :=
      (hu x ⟨hx.1, hx.2.le⟩).hasDerivAt (Icc_mem_nhds h0 hx.2)
    have hg : HasDerivAt (fun t => u (t - (n:ℝ) * S)) (K x - Real.sin (u x)) s := by
      have h : HasDerivAt u (K x - Real.sin (u x)) (s - (n:ℝ) * S) := by
        rw [show s - (n:ℝ) * S = x by linarith]; exact hux
      simpa using h.comp s ((hasDerivAt_id s).sub_const ((n:ℝ) * S))
    have heq : (fun t => u (toIcoMod hS 0 t)) =ᶠ[nhds s] (fun t => u (t - (n:ℝ) * S)) := by
      filter_upwards [Ioo_mem_nhds hmemIoo.1 hmemIoo.2] with t ht
      rw [toIcoMod_sub_int_mul hS n t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    rw [hKx] at hg
    exact hg.congr_of_eventuallyEq heq

/-! ### The periodic steering solution -/

/-- **Existence of the periodic steering solution on the closed strip.**  For a
continuous `S`-periodic front curvature with `0 ≤ K ≤ κ̂ ≤ 1` there is an
`S`-periodic solution of `δ_s = K − sin δ` with values in `[0, arcsin κ̂]`; its
cosine — the speed of the reconstructed rear track — is at least `√(1 − κ̂²)`. -/
theorem exists_periodic_steering {K : ℝ → ℝ} {S kap : ℝ} (hS : 0 < S) (hK : Continuous K)
    (hKper : Function.Periodic K S) (hkap0 : 0 ≤ kap) (hkap1 : kap ≤ 1)
    (hK0 : ∀ s, 0 ≤ K s) (hKk : ∀ s, K s ≤ kap) :
    ∃ delta : ℝ → ℝ, Function.Periodic delta S ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) := by
  set a : ℝ := Real.arcsin kap with hadef
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hkap0
  have hapi : a ≤ π / 2 := Real.arcsin_le_pi_div_two kap
  have hsina : Real.sin a = kap := Real.sin_arcsin (by linarith) hkap1
  -- a family of solutions of the clamped equation, one for each initial value
  obtain ⟨U, hU⟩ : ∃ U : ℝ → ℝ → ℝ, ∀ y, U y 0 = y ∧
      ∀ s ∈ Icc 0 S, HasDerivWithinAt (U y)
        (K s - Real.sin (clampAt a (U y s))) (Icc 0 S) s :=
    ⟨fun y => (exists_clamped_solution hK hS.le a y).choose,
      fun y => (exists_clamped_solution hK hS.le a y).choose_spec⟩
  -- inside the strip they solve the true equation
  have hstrip : ∀ y ∈ Icc 0 a, ∀ s ∈ Icc 0 S, U y s ∈ Icc 0 a := by
    intro y hy
    refine clamped_solution_mem_strip ha0 hK0 (fun s => by rw [hsina]; exact hKk s) (hU y).2 ?_
    rw [(hU y).1]; exact hy
  have htrue : ∀ y ∈ Icc 0 a, ∀ s ∈ Icc 0 S,
      HasDerivWithinAt (U y) (K s - Real.sin (U y s)) (Icc 0 S) s := by
    intro y hy s hs
    have h := (hU y).2 s hs
    rwa [clampAt_of_mem (hstrip y hy s hs)] at h
  -- the Poincaré map of the strip
  set P : ℝ → ℝ := fun y => U y S with hP
  have hmaps : Set.MapsTo P (Icc 0 a) (Icc 0 a) :=
    fun y hy => hstrip y hy S ⟨hS.le, le_rfl⟩
  have hlip : ∀ y ∈ Icc 0 a, ∀ z ∈ Icc 0 a, |P y - P z| ≤ |y - z| := by
    intro y hy z hz
    have h := sol_nonexpansive hapi (htrue y hy) (htrue z hz) (hstrip y hy) (hstrip z hz)
      S ⟨hS.le, le_rfl⟩
    rwa [(hU y).1, (hU z).1] at h
  have hcont : ContinuousOn P (Icc 0 a) := by
    refine LipschitzOnWith.continuousOn (K := 1) ?_
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    simpa [Real.dist_eq] using hlip y hy z hz
  obtain ⟨y, hy, hfix⟩ := Shadowing.exists_fixed_point_of_mapsTo ha0 hcont hmaps
  -- the corresponding solution closes up
  set u : ℝ → ℝ := U y with hu
  have hu0 : u 0 = y := (hU y).1
  have huS : u S = u 0 := by rw [hu0]; exact hfix
  have hode : ∀ s ∈ Icc 0 S, HasDerivWithinAt u (K s - Real.sin (u s)) (Icc 0 S) s :=
    htrue y hy
  have hurange : ∀ s ∈ Icc 0 S, u s ∈ Icc 0 a := hstrip y hy
  -- extend periodically
  refine ⟨fun t => u (toIcoMod hS 0 t), ?_, ?_, ?_, ?_⟩
  · intro t; simp [toIcoMod_add_right]
  · intro t
    have hm : toIcoMod hS 0 t ∈ Ico (0:ℝ) S := by simpa using toIcoMod_mem_Ico hS 0 t
    exact hurange _ ⟨hm.1, hm.2.le⟩
  · intro t
    have hm : toIcoMod hS 0 t ∈ Ico (0:ℝ) S := by simpa using toIcoMod_mem_Ico hS 0 t
    have hmem := hurange _ ⟨hm.1, hm.2.le⟩
    exact Shadowing.cos_ge_of_mem_strip hmem.1 hmem.2
  · exact fun s => periodic_extension hS hKper hode huS s

/-- **The lemma *Selected inverse on the closed strip*, existence and
uniqueness.**  For a continuous `S`-periodic front curvature with
`0 ≤ K ≤ κ̂ ≤ 1` there is exactly one `S`-periodic steering solution with
values in the closed strip `[0, arcsin κ̂]`. -/
theorem existsUnique_periodic_steering {K : ℝ → ℝ} {S kap : ℝ} (hS : 0 < S) (hK : Continuous K)
    (hKper : Function.Periodic K S) (hkap0 : 0 ≤ kap) (hkap1 : kap ≤ 1)
    (hK0 : ∀ s, 0 ≤ K s) (hKk : ∀ s, K s ≤ kap) :
    ∃! delta : ℝ → ℝ, Function.Periodic delta S ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) := by
  obtain ⟨d, hper, hrange, _, hode⟩ :=
    exists_periodic_steering hS hK hKper hkap0 hkap1 hK0 hKk
  have hstrip : ∀ (e : ℝ → ℝ), (∀ s, e s ∈ Icc 0 (Real.arcsin kap)) →
      ∀ s, e s ∈ Icc (-(π / 2)) (π / 2) := by
    intro e he s
    have h := he s
    exact ⟨by linarith [h.1, Real.pi_pos], le_trans h.2 (Real.arcsin_le_pi_div_two kap)⟩
  refine ⟨d, ⟨hper, hrange, hode⟩, ?_⟩
  rintro e ⟨hpere, hrangee, hodee⟩
  exact Shadowing.steering_unique hS hodee hode hpere hper (hstrip e hrangee) (hstrip d hrange)

end SteeringExistence
