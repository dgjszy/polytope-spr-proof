import SPR.Segment.Definitions

/-!
# Finite-vertex robust synthesis with an exact numerator degree

A nonempty finite family may repeat vertices. Quantification over such families
of size at most m is equivalent to using polytopes with at most m vertices.
All convex weights precede the frequency quantifier; one numerator is fixed.
-/
namespace SPR.Polytope
open Polynomial
noncomputable section

/-- A convex combination using all the given coordinates. -/
def blend {r : ℕ} (a : Fin r → ℝ[X]) (weights : Fin r → ℝ) : ℝ[X] :=
  ∑ i, weights i • a i

/-- Closed simplex, including all boundary faces. -/
def Weights {r : ℕ} (weights : Fin r → ℝ) : Prop :=
  (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1

/-- Full convex-hull strict stability. -/
def Stable {r : ℕ} (a : Fin r → ℝ[X]) : Prop :=
  ∀ weights, Weights weights → IsHurwitz (blend a weights)

/-- A fixed common real numerator on the whole convex hull and finite real axis. -/
def Common {r : ℕ} (a : Fin r → ℝ[X]) (b : ℝ[X]) : Prop :=
  ∀ weights, Weights weights → Segment.FrequencySPR (blend a weights) b

/-- Universal existence for all nonempty families with at most m listed vertices. -/
def Universal (n m k : ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → r ≤ m → ∀ a : Fin r → ℝ[X],
    (∀ i, (a i).Monic ∧ (a i).natDegree = n) → Stable a →
    ∃ b : ℝ[X], b.natDegree = k ∧ Common a b

theorem universal_mono_vertices {n m M k : ℕ} (h : m ≤ M)
    (hu : Universal n M k) : Universal n m k := by
  intro r hr hm a ha hs
  exact hu r hr (hm.trans h) a ha hs

theorem failure_mono_vertices {n m M k : ℕ} (h : m ≤ M)
    (hf : ¬ Universal n m k) : ¬ Universal n M k :=
  fun hu => hf (universal_mono_vertices h hu)

/-- Squared modulus clearing is linear in the denominator family. -/
theorem pairing_blend {r : ℕ} (a : Fin r → ℝ[X]) (b : ℝ[X])
    (weights : Fin r → ℝ) (ω : ℝ) :
    Segment.pairing (blend a weights) b ω = ∑ i, weights i * Segment.pairing (a i) b ω := by
  have he : Segment.value (blend a weights) (Complex.I*(ω:ℂ)) =
      ∑ i, (weights i : ℂ)*Segment.value (a i) (Complex.I*(ω:ℂ)) := by
    simp [Segment.value, blend, smul_eq_C_mul, eval₂_finsetSum]
  unfold Segment.pairing
  rw [he, star_sum, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem common_of_vertices {r : ℕ} (a : Fin r → ℝ[X]) (hs : Stable a)
    (b : ℝ[X]) (hb : ∀ i, Segment.FrequencySPR (a i) b)
    (ha : ∀ i, IsHurwitz (a i)) : Common a b := by
  intro weights hweights
  rw [Segment.frequencySPR_iff_pairing_pos (hs weights hweights)]
  intro ω
  rw [pairing_blend]
  have hex : ∃ i, 0 < weights i := by
    by_contra! hn
    have hz : ∑ i, weights i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hn i) (hweights.1 i))
    linarith [hweights.2]
  obtain ⟨j, hj⟩ := hex
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hweights.1 i) ((Segment.frequencySPR_iff_pairing_pos (ha i)).mp (hb i) ω).le
  · exact ⟨j, Finset.mem_univ _, mul_pos hj
      ((Segment.frequencySPR_iff_pairing_pos (ha j)).mp (hb j) ω)⟩

end
end SPR.Polytope
