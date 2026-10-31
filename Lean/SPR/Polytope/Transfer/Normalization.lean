import SPR.Polytope.Common.Definitions

/-! # Fixed-degree coefficient normalization and a single nonzero subsequential limit. -/
namespace SPR.Polytope.Transfer
open Polynomial Complex Filter
open scoped Topology
noncomputable section

def coefficients (N : ℕ) (p : ℝ[X]) : Fin (N+1) → ℝ := fun i => p.coeff i

def polynomial {N : ℕ} (v : Fin (N+1) → ℝ) : ℝ[X] :=
  ∑ i, C (v i)*X^(i:ℕ)

theorem coefficient_polynomial {N : ℕ} (v : Fin (N+1) → ℝ) (j : Fin (N+1)) :
    (polynomial v).coeff j=v j := by
  simp only [polynomial,finsetSum_coeff,coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [show (j:ℕ) ≠ (i:ℕ) from fun h => hij (Fin.ext h.symm)]
  · simp

theorem polynomial_degree {N : ℕ} (v : Fin (N+1) → ℝ) :
    (polynomial v).natDegree ≤ N := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem reconstruct {N : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ N) :
    polynomial (coefficients N p)=p := by
  ext j
  by_cases hj : j < N+1
  · exact coefficient_polynomial (coefficients N p) ⟨j,hj⟩
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (polynomial_degree _) (by omega)),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]

theorem coefficients_ne_zero {N : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ N) (hp : p ≠ 0) :
    coefficients N p ≠ 0 := by
  intro h
  apply hp
  rw [← reconstruct hd,h]
  simp [polynomial]

theorem polynomial_smul {N : ℕ} (c : ℝ) (v : Fin (N+1) → ℝ) :
    polynomial (c • v)=c • polynomial v := by
  simp [polynomial,smul_eq_C_mul,Finset.mul_sum,C_mul,mul_assoc]

theorem polynomial_ne_zero {N : ℕ} {v : Fin (N+1) → ℝ} (hv : ‖v‖=1) :
    polynomial v ≠ 0 := by
  intro hz
  have hc : v=0 := by
    funext i
    have hh := coefficient_polynomial v i
    rw [hz] at hh
    simpa using hh.symm
  simp [hc] at hv

theorem continuous_value {N : ℕ} (z : ℂ) :
    Continuous (fun v : Fin (N+1) → ℝ => Segment.value (polynomial v) z) := by
  simp only [polynomial,Segment.value,eval₂_finsetSum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
  fun_prop

/-- The same coefficient subsequence works for every frequency; its norm is one. -/
theorem normalized_subsequence (N : ℕ) (p : ℕ → ℝ[X])
    (hd : ∀ n, (p n).natDegree ≤ N) (hp : ∀ n, p n ≠ 0) :
    ∃ v : Fin (N+1) → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖v‖=1 ∧
      Tendsto (fun n => (‖coefficients N (p (φ n))‖⁻¹ : ℝ) •
        coefficients N (p (φ n))) atTop (𝓝 v) := by
  let u : ℕ → Fin (N+1) → ℝ := fun n =>
    (‖coefficients N (p n)‖⁻¹ : ℝ) • coefficients N (p n)
  have hu (n : ℕ) : ‖u n‖=1 := by
    have hn : ‖coefficients N (p n)‖ ≠ 0 := norm_ne_zero_iff.mpr (coefficients_ne_zero (hd n) (hp n))
    simp [u,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hn]
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (isCompact_sphere (0 : Fin (N+1) → ℝ) 1).tendsto_subseq
    (fun n => by simpa only [Metric.mem_sphere,dist_zero_right] using hu n)
  exact ⟨v,φ,hφ,by simpa only [Metric.mem_sphere,dist_zero_right] using hv,hlim⟩

/-- Nonnegative real pairings and the constant sign pass to one nonzero normalized
limit. Frequency is quantified after the single subsequence has been selected. -/
theorem normalized_weak_limit {N r : ℕ} (p : ℕ → ℝ[X])
    (hd : ∀ n, (p n).natDegree ≤ N) (hp : ∀ n, p n ≠ 0)
    (a : ℕ → Fin r → ℝ[X]) (a₀ : Fin r → ℝ[X])
    (ha : ∀ (i : Fin r) (ω : ℝ), Tendsto (fun n => Segment.value (a n i) (I*(ω:ℂ))) atTop
      (𝓝 (Segment.value (a₀ i) (I*(ω:ℂ)))))
    (hpair : ∀ n i ω, 0 ≤ Segment.pairing (a n i) (p n) ω)
    (hc : ∀ n, 0 ≤ (p n).coeff 0) :
    ∃ B : ℝ[X], B ≠ 0 ∧ B.natDegree ≤ N ∧ 0 ≤ B.coeff 0 ∧
      ∀ i ω, 0 ≤ Segment.pairing (a₀ i) B ω := by
  obtain ⟨v,φ,hφ,hv,hlim⟩ := normalized_subsequence N p hd hp
  refine ⟨polynomial v,polynomial_ne_zero hv,polynomial_degree v,?_,?_⟩
  · have hh := (continuous_apply (⟨0,by omega⟩ : Fin (N+1))).tendsto v |>.comp hlim
    rw [coefficient_polynomial v ⟨0,by omega⟩]
    apply ge_of_tendsto hh
    exact Eventually.of_forall (fun n => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (hc (φ n)))
  · intro i ω
    have heval := (continuous_value (N := N) (I*(ω:ℂ))).tendsto v |>.comp hlim
    have hden := (ha i ω).comp hφ.tendsto_atTop
    have hh := Complex.continuous_re.tendsto _ |>.comp (heval.mul hden.star)
    apply ge_of_tendsto hh
    apply Eventually.of_forall
    intro n
    have he : polynomial ((‖coefficients N (p (φ n))‖⁻¹ : ℝ) • coefficients N (p (φ n))) =
        (‖coefficients N (p (φ n))‖⁻¹ : ℝ) • p (φ n) := by
      rw [polynomial_smul,reconstruct (hd (φ n))]
    change 0 ≤ Segment.pairing (a (φ n) i)
      (polynomial ((‖coefficients N (p (φ n))‖⁻¹ : ℝ) • coefficients N (p (φ n)))) ω
    rw [he]
    have hsmul : Segment.pairing (a (φ n) i)
        ((‖coefficients N (p (φ n))‖⁻¹ : ℝ) • p (φ n)) ω =
        ‖coefficients N (p (φ n))‖⁻¹ * Segment.pairing (a (φ n) i) (p (φ n)) ω := by
      simp [Segment.pairing,Segment.value,smul_eq_C_mul,Complex.mul_re,Complex.mul_im]
      ring
    rw [hsmul]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (hpair (φ n) i ω)

end
end SPR.Polytope.Transfer
