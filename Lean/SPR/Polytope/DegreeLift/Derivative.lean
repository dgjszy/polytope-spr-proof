import SPR.Segment.Synthesis

/-! # A strictly proper common numerator for a single arbitrary-order Hurwitz polynomial. -/
namespace SPR.Polytope.DegreeLift
open Polynomial Complex
noncomputable section

theorem derivative_spr {a : ℝ[X]} (ha : IsHurwitz a) (hn : 1 ≤ a.natDegree) :
    Segment.FrequencySPR a a.derivative := by
  let P := a.map (algebraMap ℝ ℂ)
  have hane : a ≠ 0 := by intro hz; simp [hz] at hn
  have hPne : P ≠ 0 := Polynomial.map_ne_zero hane
  have hsplit : P.Splits := IsAlgClosed.splits P
  intro ω
  have hv : P.eval (I*(ω:ℂ)) ≠ 0 := by
    simpa [P,Segment.value,eval_map] using
      (Segment.value_ne_zero ha (z := I*(ω:ℂ)) (by simp))
  simp only [Segment.value,eval₂_eq_eval_map]
  change 0 < ((a.derivative.map (algebraMap ℝ ℂ)).eval (I*(ω:ℂ))/P.eval (I*(ω:ℂ))).re
  rw [← derivative_map,hsplit.eval_derivative_div_eval_of_ne_zero hv]
  have hroot (z : ℂ) (hz : z ∈ P.roots) : 0 < (1/(I*(ω:ℂ)-z)).re := by
    have hzr := ha z ((Polynomial.mem_roots hPne).mp hz)
    have hzneq : I*(ω:ℂ)-z ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp at he
      linarith
    have hnorm := Complex.normSq_pos.mpr hzneq
    simpa [one_div,Complex.inv_re] using div_pos (by simpa using neg_pos.mpr hzr) hnorm
  have hnroots : P.roots ≠ 0 := by
    intro hz
    have hh := hsplit.natDegree_eq_card_roots
    simp [hz,P] at hh
    omega
  have he : ((P.roots.map (fun z => 1/(I*(ω:ℂ)-z))).sum).re=
      (P.roots.map (fun z => (1/(I*(ω:ℂ)-z)).re)).sum := by
    simpa only [Multiset.map_map,Function.comp_def] using
      map_multiset_sum Complex.reAddGroupHom (P.roots.map (fun z => 1/(I*(ω:ℂ)-z)))
  rw [he]
  have sum_pos (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 < x) (hne : s ≠ 0) : 0 < s.sum := by
    induction s using Multiset.induction_on with
    | empty => exact False.elim (hne rfl)
    | @cons x s ih =>
      rw [Multiset.sum_cons]
      exact add_pos_of_pos_of_nonneg (hs x (by simp))
        (Multiset.sum_nonneg (fun y hy => (hs y (by simp [hy])).le))
  apply sum_pos
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
    exact hroot z hz
  · simpa using hnroots

end
end SPR.Polytope.DegreeLift
