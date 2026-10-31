import SPR.Polytope.CubicTriangle.Exclusion

/-! # The complete cubic triangle obstruction and its classification cells. -/
namespace SPR.Polytope.CubicTriangle
open Polynomial
noncomputable section

theorem counterexample :
    (a₁.Monic ∧ a₁.natDegree=3) ∧ (a₂.Monic ∧ a₂.natDegree=3) ∧
    (a₃.Monic ∧ a₃.natDegree=3) ∧
    (∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u+v+w=1 →
      IsHurwitz (u • a₁+v • a₂+w • a₃)) ∧
    ¬ ∃ p : ℝ[X], p.natDegree ≤ 3 ∧
      ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u+v+w=1 →
        Segment.FrequencySPR (u • a₁+v • a₂+w • a₃) p := by
  refine ⟨cubic_degree _ _ _,cubic_degree _ _ _,cubic_degree _ _ _,?_,?_⟩
  · exact fun _ _ _ hu hv hw hs => triangle_hurwitz hu hv hw hs
  · rintro ⟨p,hd,hp⟩
    apply no_common_degree_le_three
    refine ⟨p,hd,?_,?_,?_⟩
    · simpa using hp 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · simpa using hp 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · simpa using hp 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def family : Fin 3 → ℝ[X] := ![a₁,a₂,a₃]

theorem family_blend (weights : Fin 3 → ℝ) : blend family weights =
    weights 0 • a₁+weights 1 • a₂+weights 2 • a₃ := by
  simp [blend,family,Fin.sum_univ_succ,add_assoc]

theorem family_stable : Stable family := by
  intro weights hw
  rw [family_blend]
  apply counterexample.2.2.2.1 _ _ _ (hw.1 0) (hw.1 1) (hw.1 2)
  simpa [Fin.sum_univ_succ,add_assoc] using hw.2

theorem cubic_failure {m k : ℕ} (hm : 3 ≤ m) (hk : k ≤ 3) : ¬ Universal 3 m k := by
  intro hu
  have ha : ∀ i, (family i).Monic ∧ (family i).natDegree=3 := by
    intro i
    fin_cases i
    · exact counterexample.1
    · exact counterexample.2.1
    · exact counterexample.2.2.1
  obtain ⟨p,hd,hp⟩ := hu 3 (by omega) hm family ha family_stable
  apply counterexample.2.2.2.2
  refine ⟨p,hd.le.trans hk,?_⟩
  intro u v w hu hv hw hs
  have hweights : Weights (![u,v,w] : Fin 3 → ℝ) := by
    constructor
    · intro i; fin_cases i <;> assumption
    · simpa [Fin.sum_univ_succ,add_assoc] using hs
  simpa [family_blend] using hp ![u,v,w] hweights

end
end SPR.Polytope.CubicTriangle
