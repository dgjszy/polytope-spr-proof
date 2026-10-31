import SPR.Polytope.Common.FirstOrder

/-! # All three exact numerator degrees for finite stable quadratic families. -/
namespace SPR.Polytope
open Polynomial Complex
noncomputable section

theorem quadratic_representation {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree=2) :
    p=X^2+C (p.coeff 1)*X+C (p.coeff 0) := by
  ext j
  by_cases h : j ≤ 2
  · interval_cases j
    · simp
    · simp
    · simpa [hd] using hm.coeff_natDegree
  · have hz := coeff_eq_zero_of_natDegree_lt (p := p) (show p.natDegree < j by omega)
    simp [hz,coeff_X,coeff_C,show j ≠ 0 by omega,show 1 ≠ j by omega,
      show j ≠ 2 by omega]

def quadraticNumerator (x y : ℝ) (k : ℕ) : ℝ[X] :=
  if k=1 then X+C x else if k=2 then X^2+C y*X+1 else -X^3+X^2+C y*X+1

theorem quadraticNumerator_degree (x y : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (quadraticNumerator x y k).natDegree=k := by
  interval_cases k <;> norm_num [quadraticNumerator] <;> compute_degree!

theorem quadratic_spr (α β x y : ℝ) (ha : 0 < α) (hb : 0 < β)
    (hx : 0 < x) (hxa : x < α) (hy : β+1 < α*y)
    {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    Segment.FrequencySPR (X^2+C α*X+C β) (quadraticNumerator x y k) := by
  intro ω
  rw [Segment.real_ratio]
  have hden : 0 < Complex.normSq
      (Segment.value (X^2+C α*X+C β) (I*(ω:ℂ))) := by
    apply Complex.normSq_pos.mpr
    intro hz
    have him := congrArg Complex.im hz
    have hre := congrArg Complex.re hz
    simp [Segment.value,pow_succ,Complex.mul_re,Complex.mul_im] at him hre
    have hw : ω=0 := him.resolve_left ha.ne'
    simp [hw] at hre
    linarith
  apply div_pos _ hden
  interval_cases k <;>
    simp [Segment.pairing,Segment.value,quadraticNumerator,pow_succ,
      Complex.mul_re,Complex.mul_im]
  · nlinarith [mul_pos hx hb,mul_nonneg (sub_pos.mpr hxa).le (sq_nonneg ω)]
  · nlinarith [sq_nonneg (ω^2),mul_nonneg (sub_pos.mpr hy).le (sq_nonneg ω)]
  · nlinarith [mul_nonneg ha.le (sq_nonneg (ω^2)),sq_nonneg (ω^2),
      mul_nonneg (sub_pos.mpr hy).le (sq_nonneg ω)]

theorem second_order_universal (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    Universal 2 m k := by
  intro r hr hm a ha hs
  have hα (i : Fin r) : 0 < (a i).coeff 1 := Hurwitz.hurwitz_coeff_pos
    (vertex_hurwitz hs i) (by rw [(ha i).1.leadingCoeff]; norm_num) 1 (by rw [(ha i).2]; omega)
  have hβ (i : Fin r) : 0 < (a i).coeff 0 := Hurwitz.hurwitz_coeff_pos
    (vertex_hurwitz hs i) (by rw [(ha i).1.leadingCoeff]; norm_num) 0 (by omega)
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0,hr⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ (fun i => (a i).coeff 1) hne
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => ((a i).coeff 0+1)/(a i).coeff 1) hne
  let x := (a i).coeff 1/2
  let y := ((a j).coeff 0+1)/(a j).coeff 1+1
  refine ⟨quadraticNumerator x y k,quadraticNumerator_degree x y hk1 hk3,?_⟩
  apply common_of_vertices a hs _
  · intro l
    rw [quadratic_representation (ha l).1 (ha l).2]
    apply quadratic_spr _ _ x y (hα l) (hβ l)
    · exact div_pos (hα i) (by norm_num)
    · have hh := hmin l (Finset.mem_univ _)
      dsimp [x]
      linarith [hα i]
    · have hh := hmax l (Finset.mem_univ _)
      have hratio : ((a l).coeff 0+1)/(a l).coeff 1 < y := by dsimp [y]; linarith
      simpa [mul_comm] using (div_lt_iff₀ (hα l)).mp hratio
    · exact hk1
    · exact hk3
  · exact vertex_hurwitz hs

end
end SPR.Polytope
