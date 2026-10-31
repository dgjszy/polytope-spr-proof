import SPR.Polytope.Transfer.QuadraticRemoval

/-! # Joint finite-factor elimination with complete degree and constant-sign budgets. -/
namespace SPR.Polytope.Transfer
open Polynomial Complex
noncomputable section

def IndependentAt (a : Fin 3 → ℝ[X]) (T : ℝ) : Prop :=
  (Segment.value (a 0) (I*(Real.sqrt T:ℂ))).re*
      (Segment.value (a 1) (I*(Real.sqrt T:ℂ))).im-
    (Segment.value (a 0) (I*(Real.sqrt T:ℂ))).im*
      (Segment.value (a 1) (I*(Real.sqrt T:ℂ))).re ≠ 0

def factors (S : Finset ℝ) : ℝ[X] := ∏ T ∈ S, quadratic T

theorem independent_multiply {a : Fin 3 → ℝ[X]} {T : ℝ} {g : ℝ[X]}
    (ha : IndependentAt a T) (hg : Segment.value g (I*(Real.sqrt T:ℂ)) ≠ 0) :
    IndependentAt (fun i => g*a i) T := by
  have hn : Complex.normSq (Segment.value g (I*(Real.sqrt T:ℂ))) ≠ 0 :=
    (Complex.normSq_pos.mpr hg).ne'
  unfold IndependentAt at *
  simp only [Segment.value_mul]
  have he (x y z : ℂ) : (x*y).re*(x*z).im-(x*y).im*(x*z).re=
      Complex.normSq x*(y.re*z.im-y.im*z.re) := by
    simp [Complex.mul_re,Complex.mul_im,Complex.normSq]
    ring
  rw [he]
  exact mul_ne_zero hn ha

theorem factors_value_nonzero {S : Finset ℝ} {T : ℝ} (hT : 0 ≤ T) (hn : T ∉ S) :
    Segment.value (factors S) (I*(Real.sqrt T:ℂ)) ≠ 0 := by
  classical
  have he : Segment.value (factors S) (I*(Real.sqrt T:ℂ))=
      ∏ U ∈ S, ((U-T : ℝ):ℂ) := by
    simp [factors,Segment.value,eval₂_finset_prod,quadratic,pow_succ,
      Complex.mul_re,Complex.mul_im]
    apply Finset.prod_congr rfl
    intro U hU
    apply Complex.ext <;> simp <;> nlinarith [Real.sq_sqrt hT]
  rw [he]
  apply Finset.prod_ne_zero_iff.mpr
  intro U hU
  exact_mod_cast sub_ne_zero.mpr (show U ≠ T from fun h => hn (h ▸ hU))

/-- A single polynomial survives the entire factor cancellation. All nodes are
distinct because S is a finset. Both degree and the zero-frequency sign survive. -/
theorem joint_remove (S : Finset ℝ) (a : Fin 3 → ℝ[X]) (K : ℕ)
    (hS : ∀ T ∈ S, 0 < T) (ha : ∀ T ∈ S, IndependentAt a T)
    (B : ℝ[X]) (hB : B ≠ 0) (hd : B.natDegree ≤ K+2*S.card)
    (hc : 0 ≤ B.coeff 0)
    (hw : ∀ i ω, 0 ≤ Segment.pairing (factors S*a i) B ω) :
    ∃ D : ℝ[X], D ≠ 0 ∧ D.natDegree ≤ K ∧ 0 ≤ D.coeff 0 ∧
      B=factors S*D ∧ ∀ i ω, 0 ≤ Segment.pairing (a i) D ω := by
  classical
  induction S using Finset.induction_on generalizing B with
  | empty =>
    refine ⟨B,hB,?_,hc,?_,?_⟩
    · simpa using hd
    · simp [factors]
    · simpa [factors] using hw
  | @insert T S hnot ih =>
    have hT := hS T (Finset.mem_insert_self _ _)
    have hres : IndependentAt (fun i => factors S*a i) T :=
      independent_multiply (ha T (Finset.mem_insert_self _ _)) (factors_value_nonzero hT.le hnot)
    have hweak : ∀ i ω, 0 ≤ Segment.pairing (quadratic T*(factors S*a i)) B ω := by
      intro i ω
      have hh := hw i ω
      simpa [factors,Finset.prod_insert hnot,mul_assoc] using hh
    obtain ⟨C,hC,hwC⟩ := remove_quadratic (a := fun i => factors S*a i) hT hres hweak
    have hCne : C ≠ 0 := by intro hz; simp [hz] at hC; exact hB hC
    have hqmon : (quadratic T).Monic := by dsimp [quadratic]; monicity!
    have hqdeg : (quadratic T).natDegree=2 := by dsimp [quadratic]; compute_degree!
    have hdC : C.natDegree ≤ K+2*S.card := by
      rw [hC,natDegree_mul hqmon.ne_zero hCne,hqdeg] at hd
      rw [Finset.card_insert_of_notMem hnot] at hd
      omega
    have hcC : 0 ≤ C.coeff 0 := by
      rw [hC,mul_coeff_zero] at hc
      have hq0 : (quadratic T).coeff 0=T := by simp [quadratic]
      rw [hq0] at hc
      exact (mul_nonneg_iff_of_pos_left hT).mp hc
    obtain ⟨D,hDn,hDd,hDc,hD,hDw⟩ := ih
      (fun U hU => hS U (Finset.mem_insert_of_mem hU))
      (fun U hU => ha U (Finset.mem_insert_of_mem hU)) C hCne hdC hcC hwC
    refine ⟨D,hDn,hDd,hDc,?_,hDw⟩
    rw [hC,hD]
    simp [factors,Finset.prod_insert hnot,mul_assoc]

end
end SPR.Polytope.Transfer
