import Mathlib
import UnitTangentIterates.JointC1
import UnitTangentIterates.ArclengthInverse

/-!
# Smoothness of a global inverse, and of a family of inverses

The family of rear tracks of a path of fronts is written in *its own* arclength
by composing with the inverse `σ(t, ·)` of the rear arclength `A(t, ·)` at the
same time `t`.  The path metric asks that family to be jointly `C¹`, so the
change of variable itself has to be jointly `C¹`, and that is what this file
provides.

* `contDiff_of_globalInverse` — a `Cⁿ` map with a two-sided inverse and an
  invertible derivative at every point has a `Cⁿ` inverse (the inverse function
  theorem, globalized: the local inverse produced by the theorem coincides with
  the given one near every point);
* `contDiff_one_inverse_family` — if `A` is a family with jointly continuous
  partial derivatives whose space derivative is bounded below by `c > 0`, and
  `σ(t, ·)` inverts `A(t, ·)` for every `t`, then `σ` is jointly `C¹`;
* `hasDerivAt_inverse_family` — its space derivative is `1 / ∂_s A`.
-/

noncomputable section

open Function Set Filter Topology

namespace GlobalInverseSmooth

/-! ### The global inverse function theorem -/

variable {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- **The inverse of a globally invertible `Cⁿ` map is `Cⁿ`.**  If `f` is `Cⁿ`
(`n ≥ 1`), has an invertible derivative at every point, and `g` is a two-sided
inverse of `f`, then `g` is `Cⁿ`. -/
theorem contDiff_of_globalInverse {n : WithTop ℕ∞} {f : E → F} {g : F → E}
    (hf : ContDiff 𝕂 n f) (hn : n ≠ 0)
    (hf' : ∀ x : E, ∃ e : E ≃L[𝕂] F, HasFDerivAt f (e : E →L[𝕂] F) x)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : ContDiff 𝕂 n g := by
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨e, he⟩ := hf' (g y)
  have hy : f (g y) = y := hfg y
  have hca : ContDiffAt 𝕂 n f (g y) := hf.contDiffAt
  have hstrict := hca.hasStrictFDerivAt' he hn
  have hloc : ContDiffAt 𝕂 n (hca.localInverse he hn) (f (g y)) := hca.to_localInverse he hn
  have heq : ∀ᶠ z in 𝓝 (f (g y)), g z = hstrict.localInverse f e (g y) z :=
    hstrict.localInverse_unique (Filter.Eventually.of_forall hgf)
  rw [← hy]
  exact hloc.congr_of_eventuallyEq heq

/-! ### A family of inverses -/

variable {A At a sf : ℝ → ℝ → ℝ} {c : ℝ}

/-- The derivative of `(t, s) ↦ (t, A t s)`, as a continuous linear
equivalence, when `∂_s A ≠ 0`. -/
def shearEquiv (b d : ℝ) (hd : d ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (JointC1.partialCLM b d))
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (JointC1.partialCLM (-b / d) (1 / d)))
    (by
      intro p
      have h : d ≠ 0 := hd
      apply Prod.ext <;>
        all_goals (simp [JointC1.partialCLM_apply, smul_eq_mul]; try field_simp; try ring))
    (by
      intro p
      have h : d ≠ 0 := hd
      apply Prod.ext <;>
        all_goals (simp [JointC1.partialCLM_apply, smul_eq_mul]; try field_simp; try ring))

@[simp] theorem shearEquiv_apply (b d : ℝ) (hd : d ≠ 0) (p : ℝ × ℝ) :
    shearEquiv b d hd p = (p.1, p.1 * b + p.2 * d) := by
  simp [shearEquiv, ContinuousLinearEquiv.equivOfInverse, JointC1.partialCLM_apply, smul_eq_mul]

/-- Each slice of the family is strictly monotone, hence injective. -/
theorem injective_slice (hc : 0 < c) (hAs : ∀ t s, HasDerivAt (A t) (a t s) s)
    (hca : ∀ t s, c ≤ a t s) (t : ℝ) : Function.Injective (A t) :=
  (ArclengthInverse.strictMono_of_deriv_ge hc (hAs t) (hca t)).injective

/-- The inverse of each slice is a two-sided inverse. -/
theorem leftInverse_slice (hc : 0 < c) (hAs : ∀ t s, HasDerivAt (A t) (a t s) s)
    (hca : ∀ t s, c ≤ a t s) (hsf : ∀ t x, A t (sf t x) = x) (t s : ℝ) :
    sf t (A t s) = s :=
  injective_slice hc hAs hca t (by rw [hsf t (A t s)])

/-- **A family of inverses of a `C¹` family is `C¹`.**  If the partial
derivatives of `A` are jointly continuous and the space derivative is bounded
below by `c > 0`, then the family `sf` of inverses of the slices `A t` is
jointly `C¹`. -/
theorem contDiff_one_inverse_family (hc : 0 < c)
    (hAt : ∀ t s, HasDerivAt (fun r => A r s) (At t s) t)
    (hAs : ∀ t s, HasDerivAt (A t) (a t s) s)
    (hAtc : Continuous (uncurry At)) (hac : Continuous (uncurry a))
    (hca : ∀ t s, c ≤ a t s) (hsf : ∀ t x, A t (sf t x) = x) :
    ContDiff ℝ 1 (uncurry sf) := by
  set f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, A p.1 p.2) with hfdef
  set g : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, sf q.1 q.2) with hgdef
  have hane : ∀ t s, a t s ≠ 0 := fun t s => ne_of_gt (lt_of_lt_of_le hc (hca t s))
  have hAC : ContDiff ℝ 1 (uncurry A) :=
    JointC1.contDiff_one_of_continuous_partials hAt hAs hAtc hac
  have hfC : ContDiff ℝ 1 f := contDiff_fst.prodMk hAC
  have hf' : ∀ p : ℝ × ℝ, ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivAt f (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rintro ⟨t, s⟩
    refine ⟨shearEquiv (At t s) (a t s) (hane t s), ?_⟩
    have hA := JointC1.hasFDerivAt_of_continuous_partials hAt hAs hAtc hac t s
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((t, s) : ℝ × ℝ))).prodMk hA
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    simp [shearEquiv, ContinuousLinearEquiv.equivOfInverse, JointC1.partialCLM_apply,
      smul_eq_mul]
  have hgf : ∀ p, g (f p) = p := by
    rintro ⟨t, s⟩
    simp only [hfdef, hgdef]
    rw [leftInverse_slice hc hAs hca hsf t s]
  have hfg : ∀ q, f (g q) = q := by
    rintro ⟨t, x⟩
    simp only [hfdef, hgdef]
    rw [hsf t x]
  have hgC : ContDiff ℝ 1 g :=
    contDiff_of_globalInverse hfC (by norm_num) hf' hgf hfg
  have : uncurry sf = fun q : ℝ × ℝ => (g q).2 := rfl
  rw [this]
  exact contDiff_snd.comp hgC

/-- The space derivative of the inverse family is `1 / ∂_s A`. -/
theorem hasDerivAt_inverse_family (hc : 0 < c)
    (hAs : ∀ t s, HasDerivAt (A t) (a t s) s)
    (hca : ∀ t s, c ≤ a t s) (hsf : ∀ t x, A t (sf t x) = x) (t x : ℝ) :
    HasDerivAt (sf t) (1 / a t (sf t x)) x :=
  ArclengthInverse.hasDerivAt_of_rightInverse hc (hAs t) (hca t) (hsf t) x

end GlobalInverseSmooth
