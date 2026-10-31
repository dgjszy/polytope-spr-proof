import SPR.Segment.PositiveInterpolation

/-!
# Interpolation on a finite set of positive crossing frequencies

Adjoining zero produces exactly one additional distinct node. Reindexing this
finite set transfers the coefficient-space interpolation theorem without any
ordering or enumeration assumption.
-/

namespace SPR.Segment.Interpolation

open Polynomial Finset

noncomputable section

theorem finite_positive_ratio_interpolation (J : Finset ℝ)
    (hJ : ∀ t ∈ J, 0 < t) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ insert 0 J, 0 < ρ t) :
    ∃ u₀ u₁ : ℝ[X], u₀.natDegree ≤ J.card ∧ u₁.natDegree ≤ J.card ∧
      (∀ x : ℝ, 0 ≤ x → 0 < u₀.eval x) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < u₁.eval x) ∧
      ∀ t ∈ insert 0 J, u₁.eval t = ρ t * u₀.eval t := by
  classical
  have hz : (0 : ℝ) ∉ J := by intro hh; exact lt_irrefl 0 (hJ 0 hh)
  let S := insert (0 : ℝ) J
  have hcard : Fintype.card S = J.card + 1 := by simp [S, hz]
  let e : S ≃ Fin (J.card + 1) := Fintype.equivFinOfCardEq hcard
  let t (i : Fin (J.card + 1)) : ℝ := (e.symm i).val
  let r (i : Fin (J.card + 1)) : ℝ := ρ (t i)
  let o := e ⟨0, mem_insert_self _ _⟩
  have ht : Function.Injective t := by
    intro i j he
    apply e.symm.injective
    exact Subtype.ext he
  have ho : t o = 0 := by simp [t, o]
  have htpos (i : Fin (J.card + 1)) : 0 ≤ t i := by
    have hi := (e.symm i).property
    rcases mem_insert.mp hi with he | hh
    · exact he ▸ le_rfl
    · exact (hJ _ hh).le
  obtain ⟨u₀, u₁, hd₀, hd₁, hp₀, hp₁, he⟩ :=
    positive_ratio_interpolation J.card t r o ht ho htpos
      (fun i => hρ _ (e.symm i).property)
  have hdegree {u : ℝ[X]} (hpos : 0 < u.eval 0) (hd : u.degree < J.card + 1) :
      u.natDegree ≤ J.card := by
    have hu : u ≠ 0 := by intro hh; simp [hh] at hpos
    rw [degree_eq_natDegree hu] at hd
    have hh : u.natDegree < J.card + 1 := by exact_mod_cast hd
    omega
  refine ⟨u₀, u₁, hdegree (hp₀ 0 le_rfl) hd₀,
    hdegree (hp₁ 0 le_rfl) hd₁, hp₀, hp₁, ?_⟩
  intro x hx
  simpa [r, t] using he (e ⟨x, hx⟩)

end
end SPR.Segment.Interpolation
