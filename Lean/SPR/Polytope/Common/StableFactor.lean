import SPR.Polytope.Common.ReflectionTransfer

/-! # Stable fixed input factors, with precise numerator-degree accounting. -/
namespace SPR.Polytope
open Polynomial Complex
noncomputable section

theorem hurwitz_mul {a g : ℝ[X]} (ha : IsHurwitz a) (hg : IsHurwitz g) :
    IsHurwitz (g*a) := by
  intro z hz
  have hprod : Segment.value g z*Segment.value a z=0 := by
    simpa [IsRoot,eval_map,Segment.value] using hz
  rcases mul_eq_zero.mp hprod with h | h
  · exact hg z (by simpa [IsRoot,eval_map,Segment.value] using h)
  · exact ha z (by simpa [IsRoot,eval_map,Segment.value] using h)

theorem blend_multiply {r : ℕ} (a : Fin r → ℝ[X]) (g : ℝ[X]) (weights : Fin r → ℝ) :
    blend (fun i => g*a i) weights=g*blend a weights := by
  simp [blend,smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem stable_multiply {r : ℕ} {a : Fin r → ℝ[X]} (ha : Stable a)
    {g : ℝ[X]} (hg : IsHurwitz g) : Stable (fun i => g*a i) := by
  intro weights hw
  rw [blend_multiply]
  exact hurwitz_mul (ha weights hw) hg

/-- The full degree budget required by reflection transfer. A low-order
same-degree obstruction alone is not a premise strong enough for this lemma. -/
theorem bounded_degree_transfer {r L k : ℕ} {a : Fin r → ℝ[X]} {g : ℝ[X]}
    (ha : Stable a) (hg : IsHurwitz g)
    (hbudget : k+g.natDegree ≤ L)
    (hno : ¬ ∃ p : ℝ[X], p.natDegree ≤ L ∧ Common a p) :
    ¬ ∃ b : ℝ[X], b.natDegree ≤ k ∧ Common (fun i => g*a i) b := by
  rintro ⟨b,hdb,hb⟩
  apply hno
  refine ⟨b*g.comp (-X),?_,?_⟩
  · exact (natDegree_mul_le.trans (Nat.add_le_add hdb
      (by rw [natDegree_comp]; simp))).trans hbudget
  · intro weights hw
    apply reflect_strict (ha weights hw) (hurwitz_mul (ha weights hw) hg)
    have hh := hb weights hw
    rwa [blend_multiply] at hh

end
end SPR.Polytope
