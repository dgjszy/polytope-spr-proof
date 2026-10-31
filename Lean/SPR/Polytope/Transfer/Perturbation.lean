import SPR.Polytope.Transfer.Normalization

/-! # A whole-degree-space boundary obstruction persists at some stable perturbation.

The zero-frequency sign is obtained from the actual approximants, not from a
possibly singular limiting denominator. One normalized subsequence covers all frequencies.
-/
namespace SPR.Polytope.Transfer
open Polynomial Complex Filter
open scoped Topology
noncomputable section

def epsilon (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity

theorem epsilon_limit : Tendsto epsilon atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => (by linarith : (n:ℝ) ≤ (n:ℝ)+1))
      tendsto_natCast_atTop_atTop
  simpa [epsilon] using tendsto_inv_atTop_zero.comp hh

theorem pairing_positive_of_spr {a p : ℝ[X]} (h : Segment.FrequencySPR a p) (ω : ℝ) :
    0 < Segment.pairing a p ω := by
  have hh := h ω
  rw [Segment.real_ratio] at hh
  rcases div_pos_iff.mp hh with hh | hh
  · exact hh.1
  · exact False.elim ((not_lt_of_ge (Complex.normSq_nonneg _)) hh.2)

theorem constant_positive_of_spr {a p : ℝ[X]} (ha : 0 < a.coeff 0)
    (h : Segment.FrequencySPR a p) : 0 < p.coeff 0 := by
  have hh := pairing_positive_of_spr h 0
  have he : Segment.pairing a p 0=p.coeff 0*a.coeff 0 := by
    simp [Segment.pairing,Segment.value,← coeff_zero_eq_eval_zero]
  rw [he] at hh
  exact (mul_pos_iff_of_pos_right ha).mp hh

theorem exists_infeasible_perturbation (D : ℕ)
    (a : ℝ → Fin 3 → ℝ[X]) (a₀ : Fin 3 → ℝ[X])
    (hlim : ∀ (i : Fin 3) (ω : ℝ), Tendsto (fun n => Segment.value (a (epsilon n) i) (I*(ω:ℂ)))
      atTop (𝓝 (Segment.value (a₀ i) (I*(ω:ℂ)))))
    (hc : ∀ ε, 0 < ε → ∀ i, 0 < (a ε i).coeff 0)
    (hno : ¬ ∃ B : ℝ[X], B ≠ 0 ∧ B.natDegree ≤ D ∧ 0 ≤ B.coeff 0 ∧
      ∀ i ω, 0 ≤ Segment.pairing (a₀ i) B ω) :
    ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ B : ℝ[X], B.natDegree ≤ D ∧
      ∀ i, Segment.FrequencySPR (a ε i) B := by
  classical
  by_contra! hn
  have hex (n : ℕ) : ∃ B : ℝ[X], B.natDegree ≤ D ∧
      ∀ i, Segment.FrequencySPR (a (epsilon n) i) B := hn _ (epsilon_pos n)
  choose p hd hp using hex
  have hpn (n : ℕ) : p n ≠ 0 := by
    intro hz
    have hh := hp n 0 0
    simp [hz,Segment.value] at hh
  have hpc (n : ℕ) : 0 ≤ (p n).coeff 0 :=
    (constant_positive_of_spr (hc _ (epsilon_pos n) 0) (hp n 0)).le
  have hpair (n : ℕ) (i : Fin 3) (ω : ℝ) :
      0 ≤ Segment.pairing (a (epsilon n) i) (p n) ω :=
    (pairing_positive_of_spr (hp n i) ω).le
  obtain ⟨B,hB,hBd,hBc,hBw⟩ := normalized_weak_limit p hd hpn
    (fun n => a (epsilon n)) a₀ hlim hpair hpc
  exact hno ⟨B,hB,hBd,hBc,hBw⟩

end
end SPR.Polytope.Transfer
