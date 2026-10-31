import SPR.Polytope.DegreeLift.ProperPerturbation

/-! # A common degree n+1 direction whose real tail is strictly positive. -/
namespace SPR.Polytope.DegreeLift
open Polynomial Complex Set Filter Bornology
open scoped Topology
noncomputable section

def improperDirection (n : ℕ) (gain : ℝ) : ℝ[X] := X^n+gain • X^(n+1)
def corrected (a : ℝ[X]) (gain : ℝ) : ℝ[X] := X^a.natDegree-gain • (X*a.eraseLead)

theorem corrected_degree {a : ℝ[X]} (hm : a.Monic) (hn : 1 ≤ a.natDegree)
    {gain : ℝ} (hL : 0 < 1-gain*a.coeff (a.natDegree-1)) :
    (corrected a gain).natDegree=a.natDegree ∧
      (corrected a gain).leadingCoeff=1-gain*a.coeff (a.natDegree-1) := by
  let n := a.natDegree
  have hle : (corrected a gain).natDegree ≤ n := by
    have hq : (gain • (X*a.eraseLead)).natDegree ≤ n := by
      apply (natDegree_smul_le _ _).trans
      exact natDegree_mul_le.trans (by
        simp only [natDegree_X]
        have hh := a.eraseLead_natDegree_le
        dsimp [n]
        omega)
    exact (natDegree_sub_le_of_le (n := n) (m := n) (p := X^a.natDegree) (by simp [n]) hq).trans
      (by simp)
  have hc : (corrected a gain).coeff n=1-gain*a.coeff (n-1) := by
    have he : n=(n-1)+1 := by dsimp [n]; omega
    simp only [corrected,coeff_sub,coeff_smul,smul_eq_mul]
    rw [show (X^a.natDegree : ℝ[X]).coeff n=1 by simp [n]]
    rw [he,coeff_X_mul,a.eraseLead_coeff_of_ne (n-1) (by dsimp [n]; omega)]
    congr 2 <;> omega
  have hd := natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc]; exact hL.ne')
  exact ⟨hd,by rw [← coeff_natDegree,hd,hc]⟩

theorem corrected_identity {a : ℝ[X]} (hm : a.Monic) (gain : ℝ) :
    corrected a gain+gain • (X*a)=improperDirection a.natDegree gain := by
  have he : a.eraseLead+X^a.natDegree=a := by
    simpa only [hm.leadingCoeff,C_1,one_mul] using a.eraseLead_add_C_mul_X_pow
  dsimp [corrected,improperDirection]
  simp only [smul_eq_C_mul,pow_succ]
  linear_combination -C gain*X*he

theorem endpoint_improper_perturbation {a c : ℝ[X]} (ha : IsHurwitz a) (hm : a.Monic)
    (hn : 1 ≤ a.natDegree) (hc : Segment.FrequencySPR a c) {gain : ℝ}
    (hL : 0 < 1-gain*a.coeff (a.natDegree-1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      Segment.FrequencySPR a (c+ε • improperDirection a.natDegree gain) := by
  let L := 1-gain*a.coeff (a.natDegree-1)
  let s : Set ℂ := {z | z.re=0}
  let f : ℂ → ℝ := fun z => (Segment.value c z/Segment.value a z).re/L
  let g : ℂ → ℝ := fun z => (Segment.value (corrected a gain) z/Segment.value a z).re/L
  have hden (z : ℂ) (hz : z ∈ s) : Segment.value a z ≠ 0 :=
    Segment.value_ne_zero ha (by rw [show z.re=0 from hz])
  have hcont (p : ℝ[X]) : ContinuousOn (fun z => (Segment.value p z/Segment.value a z).re/L) s :=
    (continuous_re.comp_continuousOn
      (p.continuous_aeval.continuousOn.div a.continuous_aeval.continuousOn hden)).div_const L
  have hpos (z : ℂ) (hz : z ∈ s) : 0 < f z := by
    have he : z=I*(z.im:ℂ) := by apply Complex.ext <;> simp [show z.re=0 from hz]
    dsimp [f]
    rw [he]
    exact div_pos (hc _) hL
  have hlim : Tendsto g (cobounded ℂ) (𝓝 1) := by
    have hLne : L ≠ 0 := hL.ne'
    let Q := (corrected a gain).map (algebraMap ℝ ℂ)
    let A := a.map (algebraMap ℝ ℂ)
    obtain ⟨hd,hlc⟩ := corrected_degree hm hn hL
    have hh := Segment.Analysis.quotient_tendsto_leadingCoeff
      (p := Q) (q := A) (hm.map _).ne_zero (by simpa [Q,A] using hd)
    have he : Q.leadingCoeff/A.leadingCoeff=(L:ℂ) := by
      simp [Q,A,leadingCoeff_map,hlc,hm.leadingCoeff,L]
    rw [he] at hh
    have hr := continuous_re.tendsto _ |>.comp hh
    simpa [g,Segment.value,Q,A,eval_map,hLne] using hr.div_const L
  obtain ⟨δ,hδ,hbound⟩ := Segment.Analysis.positive_perturbation_on_closed
    (isClosed_eq continuous_re continuous_const) (hcont c) (hcont (corrected a gain)) hpos hlim
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ ω
  have hh := hbound ε hε hεδ (I*(ω:ℂ)) (by simp)
  have hnz : a.eval₂ (algebraMap ℝ ℂ) (I*(ω:ℂ)) ≠ 0 :=
    Segment.value_ne_zero ha (by simp)
  have hdir : (Segment.value (improperDirection a.natDegree gain) (I*(ω:ℂ))/
      Segment.value a (I*(ω:ℂ))).re=
      (Segment.value (corrected a gain) (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re := by
    have he : Segment.value (improperDirection a.natDegree gain) (I*(ω:ℂ))/
        Segment.value a (I*(ω:ℂ))=
        Segment.value (corrected a gain) (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))+
          (gain:ℂ)*(I*(ω:ℂ)) := by
      rw [← corrected_identity hm gain]
      simp only [Segment.value,smul_eq_C_mul,eval₂_add,eval₂_mul,eval₂_C,eval₂_X]
      have hcast : (algebraMap ℝ ℂ) gain=(gain:ℂ) := rfl
      rw [hcast]
      field_simp [hnz]
      <;> ring
    rw [he]
    simp [Complex.mul_re,Complex.mul_im]
  have heval : (Segment.value (c+ε • improperDirection a.natDegree gain) (I*(ω:ℂ))/
      Segment.value a (I*(ω:ℂ))).re=
      (Segment.value c (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re+
      ε*(Segment.value (improperDirection a.natDegree gain) (I*(ω:ℂ))/
        Segment.value a (I*(ω:ℂ))).re := by
    simp [Segment.value,smul_eq_C_mul,add_div,mul_div_assoc,Complex.mul_re,Complex.mul_im]
  rw [heval,hdir]
  simp only [f,g] at hh
  have hnum : 0 < (Segment.value c (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re+
      ε*(Segment.value (corrected a gain) (I*(ω:ℂ))/Segment.value a (I*(ω:ℂ))).re := by
    apply (div_pos_iff_of_pos_right hL).mp
    simpa [add_div,mul_div_assoc] using hh
  exact hnum

end
end SPR.Polytope.DegreeLift
