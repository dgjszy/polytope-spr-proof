import SPR.Segment.DegreeRaising
import SPR.Segment.Boundedness

/-! # Adding a small degree n-1 term using a positive compactified tail. -/
namespace SPR.Polytope.DegreeLift
open Polynomial Complex Set Filter Bornology
open scoped Topology
noncomputable section

def tailNumerator (a : ℝ[X]) : ℝ[X] := X^(a.natDegree-1)+X*a.eraseLead

theorem tail_numerator_degree {a : ℝ[X]} (ha : IsHurwitz a) (hm : a.Monic)
    (hn : 1 ≤ a.natDegree) :
    (tailNumerator a).natDegree=a.natDegree ∧
      (tailNumerator a).leadingCoeff=a.coeff (a.natDegree-1) := by
  let n := a.natDegree
  have hα : 0 < a.coeff (n-1) := Hurwitz.hurwitz_coeff_pos ha
    (by rw [hm.leadingCoeff]; norm_num) _ (by dsimp [n]; omega)
  have hle : (tailNumerator a).natDegree ≤ n := by
    apply natDegree_add_le_of_degree_le
    · simpa [n] using (show a.natDegree-1 ≤ a.natDegree by omega)
    · exact natDegree_mul_le.trans (by
        simp only [natDegree_X]
        have hh := a.eraseLead_natDegree_le
        dsimp [n]
        omega)
  have hc : (tailNumerator a).coeff n=a.coeff (n-1) := by
    unfold tailNumerator
    rw [coeff_add]
    have he : n=(n-1)+1 := by dsimp [n]; omega
    have hfirst : (X^(a.natDegree-1) : ℝ[X]).coeff n=0 := by
      simp only [coeff_X_pow]
      exact if_neg (by dsimp [n]; omega)
    rw [hfirst,zero_add,he,coeff_X_mul]
    rw [a.eraseLead_coeff_of_ne (n-1) (by dsimp [n]; omega)]
    congr 1 <;> omega
  have hd := natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc]; exact hα.ne')
  exact ⟨hd,by rw [← coeff_natDegree,hd,hc]⟩

theorem tail_numerator_identity {a : ℝ[X]} (hm : a.Monic) (hn : 1 ≤ a.natDegree) :
    tailNumerator a=(1-X^2)*X^(a.natDegree-1)+X*a := by
  have he : a.eraseLead+X^a.natDegree=a := by
    simpa only [hm.leadingCoeff,C_1,one_mul] using a.eraseLead_add_C_mul_X_pow
  have hp : X*X^a.natDegree=(X^2:ℝ[X])*X^(a.natDegree-1) := by
    rw [← pow_succ',← pow_add]
    congr 1
    omega
  dsimp [tailNumerator]
  linear_combination X*he-hp

theorem endpoint_proper_perturbation {a c : ℝ[X]} (ha : IsHurwitz a) (hm : a.Monic)
    (hn : 1 ≤ a.natDegree) (hc : Segment.FrequencySPR a c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      Segment.FrequencySPR a (c+ε • X^(a.natDegree-1)) := by
  let α := a.coeff (a.natDegree-1)
  have hα : 0 < α := Hurwitz.hurwitz_coeff_pos ha
    (by rw [hm.leadingCoeff]; norm_num) _ (by omega)
  let s : Set ℂ := {z | z.re=0}
  let f : ℂ → ℝ := fun z => (1+Complex.normSq z)/α*(Segment.value c z/Segment.value a z).re
  let g : ℂ → ℝ := fun z => (Segment.value (tailNumerator a) z/Segment.value a z).re/α
  have hden (z : ℂ) (hz : z ∈ s) : Segment.value a z ≠ 0 :=
    Segment.value_ne_zero ha (by rw [show z.re=0 from hz])
  have hf : ContinuousOn f s := by
    unfold f
    apply ContinuousOn.mul
    · fun_prop
    · exact continuous_re.comp_continuousOn
        (c.continuous_aeval.continuousOn.div a.continuous_aeval.continuousOn hden)
  have hg : ContinuousOn g s := by
    exact (continuous_re.comp_continuousOn
      ((tailNumerator a).continuous_aeval.continuousOn.div
        a.continuous_aeval.continuousOn hden)).div_const α
  have hpos (z : ℂ) (hz : z ∈ s) : 0 < f z := by
    have he : z=I*(z.im:ℂ) := by apply Complex.ext <;> simp [show z.re=0 from hz]
    dsimp [f]
    have hh : 0 < (Segment.value c z/Segment.value a z).re := by rw [he]; exact hc z.im
    exact mul_pos (div_pos (by have := Complex.normSq_nonneg z; linarith) hα) hh
  have hlim : Tendsto g (cobounded ℂ) (𝓝 1) := by
    let Q := (tailNumerator a).map (algebraMap ℝ ℂ)
    let A := a.map (algebraMap ℝ ℂ)
    obtain ⟨hdeg,hlc⟩ := tail_numerator_degree ha hm hn
    have hh := Segment.Analysis.quotient_tendsto_leadingCoeff
      (p := Q) (q := A) (hm.map _).ne_zero (by simpa [Q,A] using hdeg)
    have he : Q.leadingCoeff/A.leadingCoeff=(α:ℂ) := by
      simp [Q,A,leadingCoeff_map,hlc,hm.leadingCoeff,α]
    rw [he] at hh
    have hr := continuous_re.tendsto _ |>.comp hh
    simpa [g,Segment.value,Q,A,eval_map,hα.ne'] using hr.div_const α
  obtain ⟨δ,hδ,hbound⟩ := Segment.Analysis.positive_perturbation_on_closed
    (isClosed_eq continuous_re continuous_const) hf hg hpos hlim
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ ω
  have hh := hbound ε hε hεδ (I*(ω:ℂ)) (by simp)
  have hnz : Segment.value a (I*(ω:ℂ)) ≠ 0 := Segment.value_ne_zero ha (by simp)
  have hgid : g (I*(ω:ℂ))=(1+ω^2)/α*
      (Segment.value (X^(a.natDegree-1)) (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re := by
    dsimp [g]
    rw [tail_numerator_identity hm hn]
    simp only [Segment.value_add,Segment.value_mul,Segment.value_C,eval₂_one,
      Segment.value,eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_one]
    have hnz' : a.eval₂ (algebraMap ℝ ℂ) (I*(ω:ℂ)) ≠ 0 := hnz
    rw [add_div, mul_div_cancel_right₀ _ hnz']
    simp [pow_succ,Complex.mul_re,Complex.mul_im,Complex.div_re,add_div] <;> ring
  have hfid : f (I*(ω:ℂ))=(1+ω^2)/α*
      (Segment.value c (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re := by
    have hnorm : Complex.normSq (I*(ω:ℂ))=ω^2 := by
      simp [Complex.normSq,Complex.mul_re,Complex.mul_im] <;> ring
    dsimp [f]
    rw [hnorm]
  have heval : (Segment.value (c+ε • X^(a.natDegree-1)) (I*(ω:ℂ))/
      Segment.value a (I*(ω:ℂ))).re=
      (Segment.value c (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re+
      ε*(Segment.value (X^(a.natDegree-1)) (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re := by
    simp [Segment.value,smul_eq_C_mul,add_div,mul_div_assoc,Complex.mul_re,Complex.mul_im]
  rw [heval]
  rw [hgid,hfid] at hh
  have hscale : 0 < (1+ω^2)/α := div_pos (by positivity) hα
  nlinarith

end
end SPR.Polytope.DegreeLift
