import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The finite-dimensional cone of polynomials nonnegative on the half-line

Coefficients provide the Euclidean topology. The cone has nonempty interior
because it contains the open positive coefficient orthant. An interior point
is strictly positive at every finite nonnegative argument. This avoids treating
pointwise strict positivity alone as an open condition on an unbounded domain.
-/

namespace SPR.Segment.Interpolation

open Polynomial Set Finset

noncomputable section

/-- A coefficient vector represents a polynomial of degree at most `r`. -/
def poly (r : ℕ) (v : Fin (r + 1) → ℝ) : ℝ[X] :=
  ((degreeLTEquiv ℝ (r + 1)).symm v).val

@[simp] theorem poly_coeff (r : ℕ) (v : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    (poly r v).coeff i = v i :=
  congrFun ((degreeLTEquiv ℝ (r + 1)).apply_symm_apply v) i

theorem poly_degree (r : ℕ) (v : Fin (r + 1) → ℝ) :
    (poly r v).degree < r + 1 :=
  mem_degreeLT.mp ((degreeLTEquiv ℝ (r + 1)).symm v).property

theorem poly_eval (r : ℕ) (v : Fin (r + 1) → ℝ) (x : ℝ) :
    (poly r v).eval x = ∑ i : Fin (r + 1), v i * x ^ (i : ℕ) := by
  change (((degreeLTEquiv ℝ (r + 1)).symm v).val).eval x = _
  rw [eval_eq_sum_degreeLTEquiv ((degreeLTEquiv ℝ (r + 1)).symm v).property]
  simp

@[simp] theorem poly_add (r : ℕ) (u v : Fin (r + 1) → ℝ) :
    poly r (u + v) = poly r u + poly r v := by
  simp [poly]

@[simp] theorem poly_smul (r : ℕ) (c : ℝ) (v : Fin (r + 1) → ℝ) :
    poly r (c • v) = c • poly r v := by
  simp [poly]

@[simp] theorem poly_zero (r : ℕ) : poly r 0 = 0 := by
  simp [poly]

/-- Evaluation at one argument is a linear functional on the coefficient vector. -/
def evaluation (r : ℕ) (x : ℝ) : (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun v := (poly r v).eval x
  map_add' u v := by simp
  map_smul' c v := by simp

/-- The closed convex cone of half-line nonnegative polynomials in coefficient coordinates. -/
def nonnegativeCone (r : ℕ) : Set (Fin (r + 1) → ℝ) :=
  {v | ∀ x : ℝ, 0 ≤ x → 0 ≤ (poly r v).eval x}

theorem cone_zero (r : ℕ) : 0 ∈ nonnegativeCone r := by
  simp [nonnegativeCone]

theorem cone_smul {r : ℕ} {v : Fin (r + 1) → ℝ}
    (hv : v ∈ nonnegativeCone r) {c : ℝ} (hc : 0 ≤ c) :
    c • v ∈ nonnegativeCone r := by
  intro x hx
  simpa using mul_nonneg hc (hv x hx)

theorem cone_convex (r : ℕ) : Convex ℝ (nonnegativeCone r) := by
  intro u hu v hv a b ha hb hab x hx
  simpa using add_nonneg (mul_nonneg ha (hu x hx)) (mul_nonneg hb (hv x hx))

theorem cone_closed (r : ℕ) : IsClosed (nonnegativeCone r) := by
  have he : nonnegativeCone r =
      ⋂ (x : ℝ) (_ : 0 ≤ x), {v | 0 ≤ evaluation r x v} := by
    ext v
    simp [nonnegativeCone, evaluation]
  rw [he]
  exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
    isClosed_le continuous_const (evaluation r x).continuous_of_finiteDimensional))

/-- The open positive coefficient orthant is contained in the nonnegative cone. -/
theorem positive_coefficients_subset (r : ℕ) :
    {v : Fin (r + 1) → ℝ | ∀ i, 0 < v i} ⊆ nonnegativeCone r := by
  intro v hv x hx
  rw [poly_eval]
  exact sum_nonneg (fun i _ => mul_nonneg (hv i).le (pow_nonneg hx _))

theorem cone_interior_nonempty (r : ℕ) : (interior (nonnegativeCone r)).Nonempty := by
  have hopen : IsOpen {v : Fin (r + 1) → ℝ | ∀ i, 0 < v i} := by
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  exact ⟨fun _ => 1, interior_maximal (positive_coefficients_subset r) hopen
    (by simp)⟩

theorem cone_closure_interior (r : ℕ) :
    closure (interior (nonnegativeCone r)) = nonnegativeCone r := by
  rw [(cone_convex r).closure_interior_eq_closure_of_nonempty_interior
    (cone_interior_nonempty r), (cone_closed r).closure_eq]

/-- Interior membership gives a strict inequality for each evaluation functional. -/
theorem interior_eval_pos {r : ℕ} {v : Fin (r + 1) → ℝ}
    (hv : v ∈ interior (nonnegativeCone r)) {x : ℝ} (hx : 0 ≤ x) :
    0 < (poly r v).eval x := by
  have he : (evaluation r x).toContinuousLinearMap ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : (Fin (r + 1) → ℝ) →L[ℝ] ℝ =>
      f (Pi.single (0 : Fin (r + 1)) 1)) hz
    simp [evaluation, poly_eval, Pi.single_apply] at hh
  have hopen : IsOpen (evaluation r x '' interior (nonnegativeCone r)) :=
    (evaluation r x).toContinuousLinearMap.isOpenMap_of_ne_zero he _ isOpen_interior
  have hsub : evaluation r x '' interior (nonnegativeCone r) ⊆ Ici (0 : ℝ) := by
    rintro y ⟨u, hu, rfl⟩
    exact interior_subset hu x hx
  have hh := interior_maximal hsub hopen (mem_image_of_mem (evaluation r x) hv)
  simpa only [interior_Ici, Set.mem_Ioi, evaluation, LinearMap.coe_mk, AddHom.coe_mk] using hh

end
end SPR.Segment.Interpolation
