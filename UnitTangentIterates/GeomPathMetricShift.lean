import Mathlib
import UnitTangentIterates.GeomPathMetric
import UnitTangentIterates.MarkedShift
import UnitTangentIterates.GeomPathMetricMap

/-!
# The geometric path pseudodistance modulo the marking

`GeomPathMetric.lean` builds the geometric path pseudodistance `geomDist`, the
infimum of the cost over the normal paths whose slices are closed curves of
constant speed `P ∈ [P₀,P₁]` and curvature at most `κ̂`.  Like the marked metric
it sees the marking of its two arguments: two parametrizations of one oval that
differ by a shift of the base point are at positive distance.

This file quotients that out, exactly as `MarkedShift.lean` does for the path
pseudodistance.  Shifting the marking of every slice of a geometric normal path
by `b` gives a geometric normal path between the shifted ends with the same
cost — the geometric data is only composed with the translation — so the set of
geometric costs, and hence `geomDist` itself, is invariant under a common shift
of the markings.  The infimum over the shifts of the second argument,

```
  geomDistShift P₀ P₁ κ̂ p q = ⨅ b, geomDist P₀ P₁ κ̂ p (shiftData b q) ,
```

is therefore a pseudodistance on marked curves that only depends on the two
curves and not on where they are marked.

As everywhere in this project, the infimum of the empty set is zero, so a
statement about `geomDistShift` is only informative where the relevant sets of
geometric costs are nonempty; the results below carry that nonemptiness as an
explicit hypothesis, exactly as the corresponding results for `pathDistShift`
do in `MarkedShift.lean`.

Main definitions and results:

* `isGeomCurve_shiftData`, `isGeomNormalPath_shiftPathOf` — the geometric
  conditions are invariant under a shift of the marking;
* `geomSet_shiftData`, `geomDist_shiftData` — invariance of the cost set and of
  the pseudodistance;
* `geomDistShift` with `geomDistShift_nonneg`, `geomDistShift_le_geomDist`,
  `geomDistShift_self`, `geomDistShift_comm`, `geomDistShift_triangle`;
* `pathDistShift_le_geomDistShift` — the comparison with the path
  pseudodistance modulo the marking.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  MarkedShift GeomPathMetric

namespace GeomPathMetricShift

variable {p q r : Data}

/-! ### The geometric conditions are invariant under a shift of the marking -/

/-- **A shift of the marking of a geometric curve is a geometric curve.** -/
theorem isGeomCurve_shiftData {P0 P1 khat b : ℝ} (h : IsGeomCurve P0 P1 khat p) :
    IsGeomCurve P0 P1 khat (shiftData b p) := by
  obtain ⟨P, theta, kappa, hP0, hP1, hka, hX, hth⟩ := h
  refine ⟨P, fun u => theta (u + b), fun u => kappa (u + b), hP0, hP1,
    fun u => hka (u + b), ?_, ?_⟩
  · intro u
    have hfun : ⇑(shiftData b p).1 = fun u : ℝ => p.1 (u + b) := rfl
    rw [hfun]
    exact (hX (u + b)).comp_add_const u b
  · intro u
    exact (hth (u + b)).comp_add_const u b

/-- **A shift of the marking of a geometric normal path is a geometric normal
path.**  The geometric data of the shifted path is the geometric data of the
path composed with the translation, and the cost density is unchanged. -/
theorem isGeomNormalPath_shiftPathOf {P0 P1 khat b : ℝ} {p' q' : Data} {Γ : NormalPath p q}
    (hp : ∀ u, p'.1 u = p.1 (u + b)) (hq : ∀ u, q'.1 u = q.1 (u + b))
    (h : IsGeomNormalPath P0 P1 khat Γ) :
    IsGeomNormalPath P0 P1 khat (shiftPathOf b Γ hp hq) := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hP0, hP1, hka, hX, hth, hPd, hPdc, hPdb,
    htht, hetc, het, hkat, hktc, hkt⟩ := h
  refine ⟨P, Pd, fun t u => theta t (u + b), fun t u => kappa t (u + b),
    fun t u => etas t (u + b), fun t u => kt t (u + b), hP0, hP1,
    fun t u => hka t (u + b), ?_, ?_, hPd, hPdc, hPdb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u
    exact (hX t (u + b)).comp_add_const u b
  · intro t u
    exact (hth t (u + b)).comp_add_const u b
  · intro t u
    exact htht t (u + b)
  · intro u
    exact hetc (u + b)
  · intro t u
    exact het t (u + b)
  · intro t u
    exact hkat t (u + b)
  · intro u
    exact hktc (u + b)
  · intro t u
    exact hkt t (u + b)

/-- The same for the shift of a path together with both of its ends. -/
theorem isGeomNormalPath_shiftPath {P0 P1 khat b : ℝ} {Γ : NormalPath p q}
    (h : IsGeomNormalPath P0 P1 khat Γ) :
    IsGeomNormalPath P0 P1 khat (shiftPath b Γ) :=
  isGeomNormalPath_shiftPathOf (fun _ => rfl) (fun _ => rfl) h

/-! ### Invariance of the pseudodistance -/

/-- **The set of geometric costs is invariant under a common shift of the
markings.** -/
theorem geomSet_shiftData (P0 P1 khat b : ℝ) (p q : Data) :
    geomSet P0 P1 khat (shiftData b p) (shiftData b q) = geomSet P0 P1 khat p q := by
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨Γ, hΓ, rfl⟩
    exact ⟨shiftPathOf (-b) Γ (fun u => by simp) (fun u => by simp),
      isGeomNormalPath_shiftPathOf _ _ hΓ, rfl⟩
  · rintro x ⟨Γ, hΓ, rfl⟩
    exact ⟨shiftPath b Γ, isGeomNormalPath_shiftPath hΓ, rfl⟩

/-- **The geometric path pseudodistance is invariant under a common shift of the
markings.** -/
theorem geomDist_shiftData (P0 P1 khat b : ℝ) (p q : Data) :
    geomDist P0 P1 khat (shiftData b p) (shiftData b q) = geomDist P0 P1 khat p q := by
  rw [geomDist, geomDist, geomSet_shiftData]

/-! ### The pseudodistance modulo the marking -/

/-- **The geometric path pseudodistance taken modulo the marking**: the infimum
over the shifts of the marking of the second curve. -/
def geomDistShift (P0 P1 khat : ℝ) (p q : Data) : ℝ :=
  ⨅ b : ℝ, geomDist P0 P1 khat p (shiftData b q)

theorem bddBelow_geomDist_shift (P0 P1 khat : ℝ) (p q : Data) :
    BddBelow (range fun b : ℝ => geomDist P0 P1 khat p (shiftData b q)) :=
  ⟨0, by rintro x ⟨b, rfl⟩; exact geomDist_nonneg _ _ _ _ _⟩

theorem geomDistShift_nonneg (P0 P1 khat : ℝ) (p q : Data) :
    0 ≤ geomDistShift P0 P1 khat p q :=
  le_ciInf fun _ => geomDist_nonneg _ _ _ _ _

theorem geomDistShift_le (P0 P1 khat : ℝ) (p q : Data) (b : ℝ) :
    geomDistShift P0 P1 khat p q ≤ geomDist P0 P1 khat p (shiftData b q) :=
  ciInf_le (bddBelow_geomDist_shift P0 P1 khat p q) b

/-- The distance modulo the marking is at most the marked one. -/
theorem geomDistShift_le_geomDist (P0 P1 khat : ℝ) (p q : Data) :
    geomDistShift P0 P1 khat p q ≤ geomDist P0 P1 khat p q := by
  simpa using geomDistShift_le P0 P1 khat p q 0

@[simp] theorem geomDistShift_self_of_geomCurve {P0 P1 khat : ℝ}
    (h : IsGeomCurve P0 P1 khat p) : geomDistShift P0 P1 khat p p = 0 :=
  le_antisymm (by simpa [geomDist_self h] using geomDistShift_le_geomDist P0 P1 khat p p)
    (geomDistShift_nonneg P0 P1 khat p p)

theorem geomDistShift_comm (P0 P1 khat : ℝ) (p q : Data) :
    geomDistShift P0 P1 khat p q = geomDistShift P0 P1 khat q p := by
  have key : ∀ x y : Data, geomDistShift P0 P1 khat x y ≤ geomDistShift P0 P1 khat y x := by
    intro x y
    refine le_ciInf fun b => ?_
    have h1 : geomDist P0 P1 khat y (shiftData b x)
        = geomDist P0 P1 khat (shiftData (-b) y) (shiftData (-b) (shiftData b x)) :=
      (geomDist_shiftData P0 P1 khat (-b) y (shiftData b x)).symm
    have h2 : shiftData (-b) (shiftData b x) = x := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> simp
    rw [h1, h2, geomDist_comm]
    exact geomDistShift_le P0 P1 khat x y (-b)
  exact le_antisymm (key p q) (key q p)

/-- **The triangle inequality modulo the marking**, for curves joined by
geometric normal paths after a shift. -/
theorem geomDistShift_triangle {P0 P1 khat : ℝ} (hP0 : 0 < P0) {p q r : Data}
    (hpq : ∀ b : ℝ, (geomSet P0 P1 khat p (shiftData b q)).Nonempty)
    (hqr : ∀ b : ℝ, (geomSet P0 P1 khat q (shiftData b r)).Nonempty) :
    geomDistShift P0 P1 khat p r
      ≤ geomDistShift P0 P1 khat p q + geomDistShift P0 P1 khat q r := by
  have hstep : ∀ b₁ b₂ : ℝ, geomDistShift P0 P1 khat p r
      ≤ geomDist P0 P1 khat p (shiftData b₁ q) + geomDist P0 P1 khat q (shiftData b₂ r) := by
    intro b₁ b₂
    have hmid : geomDist P0 P1 khat (shiftData b₁ q) (shiftData (b₁ + b₂) r)
        = geomDist P0 P1 khat q (shiftData b₂ r) := by
      rw [← shiftData_add b₁ b₂ r, geomDist_shiftData]
    have hne2 : (geomSet P0 P1 khat (shiftData b₁ q) (shiftData (b₁ + b₂) r)).Nonempty := by
      rw [← shiftData_add b₁ b₂ r, geomSet_shiftData]
      exact hqr b₂
    have htri : geomDist P0 P1 khat p (shiftData (b₁ + b₂) r)
        ≤ geomDist P0 P1 khat p (shiftData b₁ q)
          + geomDist P0 P1 khat (shiftData b₁ q) (shiftData (b₁ + b₂) r) :=
      geomDist_triangle hP0 (hpq b₁) hne2
    rw [hmid] at htri
    exact le_trans (geomDistShift_le P0 P1 khat p r (b₁ + b₂)) htri
  have h1 : ∀ b₂ : ℝ, geomDistShift P0 P1 khat p r
      - geomDist P0 P1 khat q (shiftData b₂ r) ≤ geomDistShift P0 P1 khat p q := by
    intro b₂
    refine le_ciInf fun b₁ => ?_
    have := hstep b₁ b₂
    linarith
  have h2 : geomDistShift P0 P1 khat p r - geomDistShift P0 P1 khat p q
      ≤ geomDistShift P0 P1 khat q r := by
    refine le_ciInf fun b₂ => ?_
    have := h1 b₂
    linarith
  linarith

/-! ### Comparison with the path pseudodistance modulo the marking -/

/-- **The geometric pseudodistance modulo the marking dominates the path
pseudodistance modulo the marking.**  Every geometric normal path is a normal
path, so the infimum over the geometric ones is the larger. -/
theorem pathDistShift_le_geomDistShift {P0 P1 khat : ℝ} (hP0 : 0 ≤ P0) (p q : Data)
    (hne : ∀ b : ℝ, (geomSet P0 P1 khat p (shiftData b q)).Nonempty) :
    pathDistShift p q ≤ geomDistShift P0 P1 khat p q := by
  refine le_ciInf fun b => ?_
  refine le_trans (pathDistShift_le p q b) ?_
  exact le_trans
    (GeomPathDist.pathDist_le_geomPathDist ((hne b).mono (geomSet_subset_geomCostSet hP0 _ _)))
    (geomPathDist_le_geomDist hP0 (hne b))

/-! ### A Lipschitz criterion modulo the marking -/

/-- **A Lipschitz criterion for the geometric pseudodistance modulo the
marking.**  A map of marked curves which is equivariant for shifts of the
marking — every shift of `q` is sent to some shift of `F q` — and which takes
every geometric normal path to a geometric normal path of cost at most `C`
times as large is `C`-Lipschitz for `geomDistShift`. -/
theorem geomDistShift_le_mul_of_maps_geomPaths {P0 P1 khat C : ℝ} {F : Data → Data}
    (hC : 0 ≤ C) {p q : Data}
    (hequiv : ∀ b : ℝ, ∃ cc : ℝ, F (shiftData b q) = shiftData cc (F q))
    (h : ∀ (b : ℝ) (Γ : NormalPath p (shiftData b q)), IsGeomNormalPath P0 P1 khat Γ →
      ∃ Γ' : NormalPath (F p) (F (shiftData b q)),
        IsGeomNormalPath P0 P1 khat Γ' ∧ cost Γ' ≤ C * cost Γ)
    (hne : ∀ b : ℝ, (geomSet P0 P1 khat p (shiftData b q)).Nonempty) :
    geomDistShift P0 P1 khat (F p) (F q) ≤ C * geomDistShift P0 P1 khat p q := by
  have key : ∀ b : ℝ, geomDistShift P0 P1 khat (F p) (F q)
      ≤ C * geomDist P0 P1 khat p (shiftData b q) := by
    intro b
    obtain ⟨cc, hcc⟩ := hequiv b
    have hstep : geomDist P0 P1 khat (F p) (F (shiftData b q))
        ≤ C * geomDist P0 P1 khat p (shiftData b q) :=
      geomDist_le_mul_of_maps_geomPaths hC (h b) (hne b)
    have hle : geomDistShift P0 P1 khat (F p) (F q)
        ≤ geomDist P0 P1 khat (F p) (shiftData cc (F q)) :=
      geomDistShift_le P0 P1 khat (F p) (F q) cc
    rw [← hcc] at hle
    exact le_trans hle hstep
  rcases eq_or_lt_of_le hC with rfl | hCpos
  · simpa using key 0
  · have hdiv : geomDistShift P0 P1 khat (F p) (F q) / C ≤ geomDistShift P0 P1 khat p q := by
      refine le_ciInf fun b => ?_
      rw [div_le_iff₀ hCpos]
      have := key b
      linarith
    rw [div_le_iff₀ hCpos] at hdiv
    linarith

end GeomPathMetricShift
