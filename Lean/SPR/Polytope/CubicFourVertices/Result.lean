import SPR.Polytope.CubicFourVertices.Stability
import SPR.Polytope.Transfer.Result

/-! # The four-vertex cubic obstruction to a direct quartic numerator. -/
namespace SPR.Polytope.CubicFourVertices
open Polynomial
noncomputable section

theorem counterexample : ∃ a : Fin 4 → ℝ[X],
    (∀ i, (a i).Monic ∧ (a i).natDegree=3) ∧ Polytope.Stable a ∧
    ¬ ∃ B : ℝ[X], B.natDegree ≤ 4 ∧ Polytope.Common a B := by
  classical
  have hex : ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ B : ℝ[X], B.natDegree ≤ 4 ∧
      ∀ i, Segment.FrequencySPR (family ε i) B := by
    by_contra! hn
    have hx (n : ℕ) : ∃ B : ℝ[X], B.natDegree ≤ 4 ∧
        ∀ i, Segment.FrequencySPR (family (Transfer.epsilon n) i) B :=
      hn _ (Transfer.epsilon_pos n)
    choose p hd hp using hx
    have hpn (n : ℕ) : p n ≠ 0 := by
      intro hz
      have hh := hp n 0 0
      simp [hz,Segment.value] at hh
    have hc (n : ℕ) : 0 ≤ (p n).coeff 0 := by
      have ha := Polytope.vertex_hurwitz (stable (Transfer.epsilon_pos n)) (0:Fin 4)
      have ha0 := Hurwitz.hurwitz_coeff_pos ha
        (by rw [(degree (Transfer.epsilon n) 0).1.leadingCoeff]; norm_num) 0 (by omega)
      exact (Transfer.constant_positive_of_spr ha0 (hp n 0)).le
    have hpair (n : ℕ) (i : Fin 4) (ω : ℝ) :
        0 ≤ Segment.pairing (family (Transfer.epsilon n) i) (p n) ω :=
      (Transfer.pairing_positive_of_spr (hp n i) ω).le
    obtain ⟨B,hB,hBd,_,hBw⟩ := Transfer.normalized_weak_limit p hd hpn
      (fun n => family (Transfer.epsilon n)) boundary value_limit hpair hc
    exact no_nonzero_weak ⟨B,hB,hBd,hBw⟩
  obtain ⟨ε,hε,hno⟩ := hex
  refine ⟨family ε,degree ε,stable hε,?_⟩
  rintro ⟨B,hd,hB⟩
  exact hno ⟨B,hd,fun i => Polytope.common_vertex hB i⟩

theorem cubic_quartic_failure {m : ℕ} (hm : 4 ≤ m) : ¬ Polytope.Universal 3 m 4 := by
  intro hu
  obtain ⟨a,ha,hs,hno⟩ := counterexample
  obtain ⟨B,hd,hB⟩ := hu 4 (by omega) hm a ha hs
  exact hno ⟨B,hd.le,hB⟩

end
end SPR.Polytope.CubicFourVertices
