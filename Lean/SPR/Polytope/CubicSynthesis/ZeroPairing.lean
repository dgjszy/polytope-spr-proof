import SPR.Polytope.CubicSynthesis.Contacts
import SPR.Polytope.CubicSynthesis.Hurwitz
import SPR.Polytope.CubicSynthesis.CompactPerturbation
import SPR.Polytope.Common.SegmentExistence

/-! # The identically zero pairing branch in the full quartic coefficient space. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial Complex
noncomputable section

/-- The kernel of pairing against a strictly Hurwitz cubic consists exactly of
the scalar multiples of `s*a(s)` in the degree-at-most-four space. -/
theorem zero_pairing_coefficients {α β γ : ℝ}
    (hs : IsHurwitz (CubicTriangle.cubic α β γ)) (v : Vec)
    (hz : pairPoly α β γ v=0) :
    v 0=0 ∧ v 1=γ*v 4 ∧ v 2=β*v 4 ∧ v 3=α*v 4 := by
  obtain ⟨hα,hβ,hγ,hD⟩ := hurwitz_inequalities hs
  have c0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  have c1 := congrArg (fun p : ℝ[X] => p.coeff 1) hz
  have c2 := congrArg (fun p : ℝ[X] => p.coeff 2) hz
  have c3 := congrArg (fun p : ℝ[X] => p.coeff 3) hz
  norm_num only [pairPoly,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,
    coeff_zero,zero_add,add_zero] at c0 c1 c2 c3
  simp only [ite_true,ite_false,zero_add,add_zero] at c0 c1 c2 c3
  have hw : v 0=0 := (mul_eq_zero.mp c0).resolve_left hγ.ne'
  have hx : v 3=α*v 4 := by linarith
  have hy : v 2=β*v 4 := by
    have hh : (α*β-γ)*(v 2-β*v 4)=0 := by
      linear_combination β*c2+c1+β^2*c3+α*hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by linarith))
  have hz' : v 1=γ*v 4 := by
    have hh : β*(v 1-γ*v 4)=0 := by rw [hw,hy] at c1; nlinarith [c1]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hβ.ne')
  exact ⟨hw,hz',hy,hx⟩

def cubicVector (α β γ : ℝ) : Vec := ![γ,β,α,1,0]

theorem cubicVector_numerator (α β γ : ℝ) :
    numerator (cubicVector α β γ)=CubicTriangle.cubic α β γ := by
  simp [numerator,cubicVector,CubicTriangle.cubic]
  ring

theorem zero_pairing_numerator {α β γ : ℝ}
    (hs : IsHurwitz (CubicTriangle.cubic α β γ)) (v : Vec)
    (hz : pairPoly α β γ v=0) :
    numerator v=C (v 4)*X*CubicTriangle.cubic α β γ := by
  obtain ⟨hw,hz',hy,hx⟩ := zero_pairing_coefficients hs v hz
  simp [numerator,hw,hz',hy,hx,CubicTriangle.cubic]
  ring

/-- Whole-hull stability restricts to every ordered edge, even with coincident endpoints. -/
theorem stable_edge {r : ℕ} {a : Fin r → ℝ[X]} (hs : Stable a) (i j : Fin r) :
    Segment.Stable (a i) (a j) := by
  classical
  intro θ hθ
  let weights : Fin r → ℝ := fun k =>
    (if k=i then 1-θ else 0)+(if k=j then θ else 0)
  have hw : Weights weights := by
    constructor
    · intro k
      apply add_nonneg <;> split_ifs <;> first | positivity | linarith [hθ.1,hθ.2]
    · simp [weights,Finset.sum_add_distrib]
  have he : blend a weights=Segment.blend (a i) (a j) θ := by
    simp [blend,weights,add_smul,Finset.sum_add_distrib,Segment.blend]
  rw [← he]
  exact hs weights hw

/-- A real endpoint ratio cannot be nonpositive on a strictly stable edge. -/
theorem real_ratio_pairing_pos {p q : ℝ[X]} (hs : Segment.Stable p q) (ω : ℝ)
    (hi : (Segment.value q (I*(ω:ℂ))/Segment.value p (I*(ω:ℂ))).im=0) :
    0 < Segment.pairing p q ω := by
  let z := I*(ω:ℂ)
  have hp : Segment.value p z ≠ 0 := Segment.value_ne_zero hs.left (by simp [z])
  let ρ := (Segment.value q z/Segment.value p z).re
  have he : Segment.value q z=(ρ:ℂ)*Segment.value p z := by
    have hh : Segment.value q z/Segment.value p z=(ρ:ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [z] using hi
    exact (div_eq_iff hp).mp hh
  have hρ := Segment.collinear_ratio_pos hs (by simp [z]) he
  have hn : 0 < Complex.normSq (Segment.value p z) := Complex.normSq_pos.mpr hp
  have hr := Segment.real_ratio p q ω
  change (Segment.value q z/Segment.value p z).re=_ at hr
  have hh : ρ=Segment.pairing p q ω/Complex.normSq (Segment.value p z) := hr
  exact (div_pos_iff_of_pos_right hn).mp (hh ▸ hρ)

/-- An identically zero vertex pairing is harmless: the corresponding cubic
itself supplies one direction positive on the complete compact contact set. -/
theorem strictify_zero_pairing (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (v : Vec) (hne : v ≠ 0)
    (hw : ∀ i u, 0 ≤ u → u ≤ 1 → 0 ≤ compactG (α i) (β i) (γ i) v u)
    (j : Fin 3) (hz : pairPoly (α j) (β j) (γ j) v=0) :
    ∃ w : Vec, ∀ i u, 0 ≤ u → u ≤ 1 → 0 < compactG (α i) (β i) (γ i) w u := by
  let a : Fin 3 → ℝ[X] := fun i => CubicTriangle.cubic (α i) (β i) (γ i)
  have haj := vertex_hurwitz hs j
  have hb := zero_pairing_numerator haj v hz
  have hd : v 4 ≠ 0 := by
    intro hd
    have hp : numerator v=0 := by simpa [hd] using hb
    exact numerator_nonzero hne hp
  let q := cubicVector (α j) (β j) (γ j)
  have hcontact : ∀ i u, 0 ≤ u → u ≤ 1 →
      compactG (α i) (β i) (γ i) v u=0 →
      0 < compactG (α i) (β i) (γ i) q u := by
    intro i u hu hu1 he
    by_cases hlast : u=1
    · subst u
      simp [q,compactG,cubicVector]
    · obtain ⟨t,ht,rfl⟩ := finite_compact_parameter hu (lt_of_le_of_ne hu1 hlast)
      have hG : G (α i) (β i) (γ i) v t=0 := by
        rw [compactification _ _ _ _ ht] at he
        exact (div_eq_zero_iff).mp he |>.resolve_right (by positivity)
      let ω := Real.sqrt t
      have hω : ω^2=t := Real.sq_sqrt ht
      have hpair : Segment.pairing (a i) (numerator v) ω=0 := by
        rw [pairing_identity,hω]
        exact hG
      have him : (Segment.value (a j) (I*(ω:ℂ))/
          Segment.value (a i) (I*(ω:ℂ))).im=0 := by
        by_cases ht0 : t=0
        · simp [a,Segment.value,CubicTriangle.cubic,ω,ht0]
        · have hwne : ω ≠ 0 := by
            intro he
            exact ht0 (by simpa [he] using hω.symm)
          rw [hb] at hpair
          have hh : -(v 4)*ω*
              (Segment.value (a j) (I*(ω:ℂ))*
                star (Segment.value (a i) (I*(ω:ℂ)))).im=0 := by
            simpa [Segment.pairing,Segment.value,Complex.mul_re,Complex.mul_im,
              mul_assoc] using hpair
          have hI : (Segment.value (a j) (I*(ω:ℂ))*
              star (Segment.value (a i) (I*(ω:ℂ)))).im=0 :=
            (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (neg_ne_zero.mpr hd) hwne)
          simp only [Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im] at hI
          rw [Complex.div_im]
          have hnum : (Segment.value (a j) (I*(ω:ℂ))).im*
              (Segment.value (a i) (I*(ω:ℂ))).re-
              (Segment.value (a j) (I*(ω:ℂ))).re*
              (Segment.value (a i) (I*(ω:ℂ))).im=0 := by linarith
          rw [← sub_div,hnum,zero_div]
      have hpos := real_ratio_pairing_pos (stable_edge hs i j) ω him
      have hQ : G (α i) (β i) (γ i) q t=Segment.pairing (a i) (a j) ω := by
        change G (α i) (β i) (γ i) q t=
          Segment.pairing (CubicTriangle.cubic (α i) (β i) (γ i))
            (CubicTriangle.cubic (α j) (β j) (γ j)) ω
        rw [← cubicVector_numerator (α j) (β j) (γ j),pairing_identity,hω]
      rw [compactification _ _ _ _ ht,hQ]
      exact div_pos hpos (by positivity)
  let ι := Fin 3 × Set.Icc (0:ℝ) 1
  let f : ι → ℝ := fun p => compactG (α p.1) (β p.1) (γ p.1) v p.2
  let g : ι → ℝ := fun p => compactG (α p.1) (β p.1) (γ p.1) q p.2
  have hf : Continuous f := by
    change Continuous (fun p : Fin 3 × Set.Icc (0:ℝ) 1 =>
      compactG (α p.1) (β p.1) (γ p.1) v p.2)
    dsimp [compactG]; fun_prop
  have hg : Continuous g := by
    change Continuous (fun p : Fin 3 × Set.Icc (0:ℝ) 1 =>
      compactG (α p.1) (β p.1) (γ p.1) q p.2)
    dsimp [compactG]; fun_prop
  obtain ⟨ε,hε,hstrict⟩ := compact_weak_strictification f g hf hg
    (fun p => hw p.1 p.2 p.2.property.1 p.2.property.2)
    (fun p hp => hcontact p.1 p.2 p.2.property.1 p.2.property.2 hp)
  refine ⟨v+ε • q,?_⟩
  intro i u hu hu1
  simpa only [compactG_add,compactG_smul,f,g] using hstrict (i,⟨u,hu,hu1⟩)

end
end SPR.Polytope.CubicSynthesis
