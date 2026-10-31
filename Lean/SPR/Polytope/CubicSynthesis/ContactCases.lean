import SPR.Polytope.CubicSynthesis.Aggregation
import SPR.Polytope.CubicSynthesis.ContactFactors

/-! # Exhaustion of the finite contact certificate configurations. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section
namespace ContactCertificate
variable {α β γ : Fin 3 → ℝ} {v : Vec}

/-- The contact identities determine all three factorization coefficients. The
zero node is treated separately, so its denominator weight is never divided out. -/
theorem factor_coefficients (C : ContactCertificate α β γ v) (A D : ℝ)
    (hc : 3 ≤ C.support.card) (hu : ∀ t ∈ C.nodes,C.u t ≠ 0)
    (hz : ∀ t ∈ C.nodes,C.z t=(A*t+D)*C.u t)
    (hw : 0 ∈ C.support → v 0= -D*v 1) :
    v 4=A*v 3 ∧ v 2=A*v 1-D*v 3 ∧ v 0= -D*v 1 := by
  let p : ℝ[X] := Polynomial.C (v 4)*X^2-Polynomial.C (v 2)*X+Polynomial.C (v 0)+
    (Polynomial.C (v 1)-Polynomial.C (v 3)*X)*(Polynomial.C A*X+Polynomial.C D)
  have hd : p.natDegree ≤ 2 := by dsimp [p]; compute_degree!
  have heval : ∀ t ∈ C.support,p.eval t=0 := by
    intro t ht
    by_cases ht0 : t=0
    · subst t
      simp [p,hw ht]
      ring
    · have htpos : 0 < t := lt_of_le_of_ne (C.support_nonneg ht) (Ne.symm ht0)
      have htnode := C.positive_support_node ht htpos
      have he := C.node_contact_equation htnode
      rw [hz t htnode] at he
      have hh : p.eval t*C.u t=0 := by
        simp only [p,eval_add,eval_sub,eval_mul,eval_C,eval_pow,eval_X]
        linear_combination he
      exact (mul_eq_zero.mp hh).resolve_right (hu t htnode)
  have hp : p=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p C.support heval (by omega)
  have he : p=Polynomial.C (v 4-A*v 3)*X^2+
      Polynomial.C (A*v 1-D*v 3-v 2)*X+Polynomial.C (v 0+D*v 1) := by
    dsimp [p]
    simp only [C_sub,C_add,C_mul]
    ring
  rw [he] at hp
  have h0 := congrArg (fun q : ℝ[X] => q.coeff 0) hp
  have h1 := congrArg (fun q : ℝ[X] => q.coeff 1) hp
  have h2 := congrArg (fun q : ℝ[X] => q.coeff 2) hp
  norm_num only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,coeff_zero] at h0 h1 h2
  simp only [ite_true,ite_false,zero_add,add_zero] at h0 h1 h2
  exact ⟨by linarith,by linarith,by linarith⟩

theorem no_infinity (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (hw : Weak α β γ v) (hv : v ≠ 0) (hmu : ∑ i,C.mu i=0) : False := by
  classical
  have hcard := C.card_support_of_no_infinity hs hmu
  have hk : 0 < C.kappa := by
    by_contra hn
    have he : C.support=C.nodes := by simp [support,hn]
    rw [he] at hcard
    have hh := C.nodes_card_le
    omega
  have hsupp : C.support=insert 0 C.nodes := by simp [support,hk]
  have hnodes : C.nodes.card=3 := by
    rw [hsupp,Finset.card_insert_of_notMem C.zero_not_nodes] at hcard
    have hh := C.nodes_card_le
    omega
  have hfull := C.full_nodes hnodes
  have hm : ∀ k ≤ 2,∑ t ∈ C.support,t^k*C.u t=0 := by
    intro k hk'
    interval_cases k
    · simpa using C.u_moment0
    · simpa using C.u_moment1
    · simpa [C.mu_zero_of_sum_zero hmu] using C.u_moment2
  have hbound : C.support.card ≤ 2+2 := by
    rw [hsupp,Finset.card_insert_of_notMem C.zero_not_nodes,hnodes]
  have hu : ∀ t ∈ C.nodes,C.u t ≠ 0 := by
    intro t ht hzero
    have htS : t ∈ C.support := by rw [hsupp]; exact Finset.mem_insert_of_mem ht
    have hz := moment_kernel_zero_of_one_zero C.support C.u 2 hbound hm htS hzero
    have h0 := hz 0 (by rw [hsupp]; exact Finset.mem_insert_self _ _)
    rw [C.u_zero] at h0
    linarith
  have hnonzero : ∃ t ∈ C.nodes,t*C.u t ≠ 0 := by
    obtain ⟨t,ht⟩ := C.nodes_nonempty hs
    exact ⟨t,ht,mul_ne_zero (C.nodes_pos ht).ne' (hu t ht)⟩
  obtain ⟨r,hr,hrpos⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun t => t*C.u t) C.node_u_moment1 hnonzero
  have hur : 0 < C.u r := (mul_pos_iff_of_pos_left (C.nodes_pos hr)).mp hrpos
  have hzr := C.node_sign hs hr hur.le
  let A := C.z r/(r*C.u r)
  have hA : 0 < A := div_pos hzr hrpos
  have hf : ∀ k ≤ 1,∑ t ∈ C.nodes,t^k*C.z t=0 := by
    intro k hk'
    interval_cases k
    · simpa using C.node_z_moment0
    · simpa [hmu] using C.node_z_moment1
  have hg : ∀ k ≤ 1,∑ t ∈ C.nodes,t^k*(t*C.u t)=0 := by
    intro k hk'
    interval_cases k
    · simpa using C.node_u_moment1
    · have hh : ∑ t ∈ C.nodes,t^2*C.u t=0 := by
        simpa [C.mu_zero_of_sum_zero hmu] using C.node_u_moment2
      convert hh using 1
      apply Finset.sum_congr rfl
      intro t _
      ring
  have hprop := moment_kernel_proportional C.nodes C.z (fun t => t*C.u t) 1
    (by omega) hf hg hr hrpos.ne'
  have hfactor := C.factor_coefficients A 0 (by omega) hu
    (fun t ht => by have hh := hprop t ht; dsimp [A]; nlinarith [hh])
    (fun _ => by simpa using C.zero_contact hk)
  have hw0 := C.zero_contact hk
  have hy : v 2=A*v 1 := by simpa using hfactor.2.1
  have hrouth (i : Fin 3) : 0 < α i ∧ γ i < α i*β i := by
    have hh := hurwitz_inequalities (vertex_hurwitz hs i)
    exact ⟨hh.1,hh.2.2.2⟩
  have hhalf (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ G (α i) (β i) (γ i) v t :=
    compact_nonnegative_halfaxis (fun u hu => hw i u hu.1 hu.2) ht
  apply hv
  exact two_contacts_force_zero hrouth hw0 hfactor.1 hy hhalf
    (C.t_pos 0) (C.t_pos 1) (fun he => by have hh := hfull.2 he; exact Fin.zero_ne_one hh)
    (C.finite_contact 0 (hfull.1 0)) (C.finite_contact 1 (hfull.1 1))

theorem positive_mu_exists (C : ContactCertificate α β γ v) (h : 0 < ∑ i,C.mu i) :
    ∃ i,0 < C.mu i := by
  by_contra! hn
  have hh : (∑ i,C.mu i) ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
  linarith

/-- Infinity support with a positive constant coefficient is the three-positive-
contact case. Its forced quadratic factor contradicts one of those contacts. -/
theorem infinity_positive_constant (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (hw : Weak α β γ v) (hn : ∀ i,pairPoly (α i) (β i) (γ i) v ≠ 0)
    (hmu : 0 < ∑ i,C.mu i) (hv0 : 0 < v 0) : False := by
  classical
  have hk0 : C.kappa=0 := by
    by_contra hh
    have hp : 0 < C.kappa := lt_of_le_of_ne C.kappa_nonneg (Ne.symm hh)
    have hz := C.zero_contact hp
    linarith
  have hsupp : C.support=C.nodes := by simp [support,hk0]
  have hc : C.nodes.card=3 := by
    have hh := C.card_support hs
    rw [hsupp] at hh
    exact le_antisymm C.nodes_card_le hh
  have hfull := C.full_nodes hc
  have hrouth (i : Fin 3) := hurwitz_inequalities (vertex_hurwitz hs i)
  obtain ⟨h,hμh⟩ := C.positive_mu_exists hmu
  let M := ∑ i,C.mu i*α i
  have hM : 0 < M := Finset.sum_pos'
    (fun i _ => mul_nonneg (C.mu_nonneg i) (hrouth i).1.le)
    ⟨h,Finset.mem_univ h,mul_pos hμh (hrouth h).1⟩
  have hu0 : ∑ t ∈ C.nodes,C.u t=0 := by simpa [hsupp] using C.u_moment0
  have hune : ∃ r ∈ C.nodes,C.u r ≠ 0 := by
    by_contra! hz
    have hh := C.node_u_moment2
    have he : ∑ t ∈ C.nodes,t^2*C.u t=0 := Finset.sum_eq_zero (by
      intro t ht; rw [hz t ht,mul_zero])
    rw [he] at hh
    linarith
  have hum : ∀ k ≤ 1,∑ t ∈ C.nodes,t^k*C.u t=0 := by
    intro k hk
    interval_cases k
    · simpa using hu0
    · simpa using C.node_u_moment1
  have hu : ∀ r ∈ C.nodes,C.u r ≠ 0 := by
    intro r hr hz
    have hh := moment_kernel_zero_of_one_zero C.nodes C.u 1 (by omega) hum hr hz
    obtain ⟨t,ht,hne⟩ := hune
    exact hne (hh t ht)
  obtain ⟨A,D,hA,hAM,hprop⟩ := affine_moment_representation C.nodes C.u C.z (by omega)
    hu0 C.node_u_moment1 C.node_z_moment0 M (∑ i,C.mu i)
    C.node_u_moment2 C.node_z_moment1 hM hmu hune
  have hfactor := C.factor_coefficients A D (C.card_support hs) hu hprop (by
    intro he
    rw [C.zero_mem_support_iff,hk0] at he
    linarith)
  have hhalf (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ (pairPoly (α i) (β i) (γ i) v).eval t := by
    rw [pairPoly_eval]
    exact compact_nonnegative_halfaxis (fun u hu => hw i u hu.1 hu.2) ht
  have he (i : Fin 3) := pairPoly_factor_quadratic (α i) (β i) (γ i) A D v
    hfactor.1 hfactor.2.1 hfactor.2.2
  by_cases hx : v 3=0
  · have hd : v 4=0 := by simpa [hx] using hfactor.1
    have htop (i : Fin 3) : 0 < v 1*(A*α i-1) := by
      have hdegree : (pairPoly (α i) (β i) (γ i) v).natDegree ≤ 2 := by
        simp only [pairPoly,hx,hd,mul_zero,sub_self,C_0,zero_mul,zero_add]
        compute_degree!
      have hconstant : 0 < (pairPoly (α i) (β i) (γ i) v).coeff 0 := by
        simpa [pairPoly] using mul_pos (hrouth i).2.2.1 hv0
      have hh := quadratic_contact_top_positive hdegree (hhalf i) hconstant
        (C.t_pos i) (by rw [pairPoly_eval]; exact C.finite_contact i (hfull.1 i))
      have hcoef : (pairPoly (α i) (β i) (γ i) v).coeff 2=v 1*(A*α i-1) := by
        simp only [pairPoly,hx,hd,mul_zero,sub_zero,hfactor.2.1]
        norm_num only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
        simp only [ite_true,ite_false,zero_add,add_zero]
        ring
      rwa [hcoef] at hh
    have hsum : 0 < ∑ i,C.mu i*(v 1*(A*α i-1)) := Finset.sum_pos'
      (fun i _ => mul_nonneg (C.mu_nonneg i) (htop i).le)
      ⟨h,Finset.mem_univ h,mul_pos hμh (htop h)⟩
    have heq : (∑ i,C.mu i*(v 1*(A*α i-1)))=
        v 1*(A*M-(∑ i,C.mu i)) := by
      simp only [M,Fin.sum_univ_succ,Fin.isValue,Fin.reduceFinMk]
      ring
    rw [hAM,sub_self,mul_zero] at heq
    linarith
  · have hinf := C.infinite_contact h hμh
    have hlead : A*α h-1=0 := by
      have hh : v 3*(A*α h-1)=0 := by rw [hfactor.1] at hinf; nlinarith [hinf]
      exact (mul_eq_zero.mp hh).resolve_left hx
    have hdegree : (residualQuadratic (α h) (β h) (γ h) A D).natDegree ≤ 1 := by
      simp only [residualQuadratic,hlead,C_0,zero_mul,zero_add]
      compute_degree!
    have hroot : (commonLinear (v 3) (v 1)).eval (C.t h)=0 := by
      apply contact_of_affine_factor
        (residualQuadratic_ne_zero (hrouth h).1 (hrouth h).2.2.1 (hrouth h).2.2.2) hdegree
      · intro t ht
        rw [← he h]
        exact hhalf h t ht
      · exact C.t_pos h
      · rw [← he h,pairPoly_eval]
        exact C.finite_contact h (hfull.1 h)
    obtain ⟨j,hj⟩ := exists_ne h
    have hjcontact : (pairPoly (α j) (β j) (γ j) v).eval (C.t h)=0 := by
      rw [he j,eval_mul,hroot,zero_mul]
    have hsame : C.t j=C.t h := at_most_one_positive_contact (hn j)
      (pairPoly_degree _ _ _ _) (hhalf j) (C.t_pos j) (C.t_pos h)
      (by rw [pairPoly_eval]; exact C.finite_contact j (hfull.1 j)) hjcontact
    exact hj (hfull.2 hsame)

/-- Infinity and zero contacts exclude one original positive contact, leaving
exactly two distinct positive frequencies. Their moments force the same linear
factorization already excluded in the no-infinity branch. -/
theorem infinity_zero_constant (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (hw : Weak α β γ v) (hv : v ≠ 0)
    (hn : ∀ i,pairPoly (α i) (β i) (γ i) v ≠ 0)
    (hmu : 0 < ∑ i,C.mu i) (hv0 : v 0=0) : False := by
  classical
  obtain ⟨h,hμh⟩ := C.positive_mu_exists hmu
  have hinf := C.infinite_contact h hμh
  have hθ : C.theta h=0 := by
    by_contra hθ
    have hp : 0 < C.theta h := lt_of_le_of_ne (C.theta_nonneg h) (Ne.symm hθ)
    have hdegree : (pairPoly (α h) (β h) (γ h) v).natDegree ≤ 2 := by
      simp only [pairPoly,hinf,C_0,zero_mul,zero_add]
      compute_degree!
    apply hn h
    have hhalf : ∀ t : ℝ,0 ≤ t → 0 ≤ (pairPoly (α h) (β h) (γ h) v).eval t := by
      intro t ht
      rw [pairPoly_eval]
      exact compact_nonnegative_halfaxis (fun u hu => hw h u hu.1 hu.2) ht
    apply quadratic_zero_constant_contact hdegree hhalf
      (by simp [pairPoly,hv0]) (C.t_pos h)
    rw [pairPoly_eval]
    exact C.finite_contact h hp
  have hnodesle : C.nodes.card ≤ 2 := by
    have hsubset : C.active ⊆ Finset.univ.erase h := by
      intro i hi
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_univ i⟩
      intro he
      have hp := (Finset.mem_filter.mp hi).2
      rw [he,hθ] at hp
      linarith
    exact Finset.card_image_le.trans ((Finset.card_le_card hsubset).trans (by simp))
  have hk : 0 < C.kappa := by
    by_contra hh
    have hcard := C.card_support hs
    have he : C.support=C.nodes := by simp [support,hh]
    rw [he] at hcard
    omega
  have hsupp : C.support=insert 0 C.nodes := by simp [support,hk]
  have hcard := C.card_support hs
  have hc : C.nodes.card=2 := by
    rw [hsupp,Finset.card_insert_of_notMem C.zero_not_nodes] at hcard
    omega
  have hsbound : C.support.card ≤ 1+2 := by
    rw [hsupp,Finset.card_insert_of_notMem C.zero_not_nodes,hc]
  have hm : ∀ k ≤ 1,∑ t ∈ C.support,t^k*C.u t=0 := by
    intro k hk'
    interval_cases k
    · simpa using C.u_moment0
    · simpa using C.u_moment1
  have hu : ∀ t ∈ C.nodes,C.u t ≠ 0 := by
    intro t ht hz
    have htS : t ∈ C.support := by rw [hsupp]; exact Finset.mem_insert_of_mem ht
    have hh := moment_kernel_zero_of_one_zero C.support C.u 1 hsbound hm htS hz
    have h0 := hh 0 (by rw [hsupp]; exact Finset.mem_insert_self _ _)
    rw [C.u_zero] at h0
    linarith
  have hnonzero : ∃ t ∈ C.nodes,t*C.u t ≠ 0 := by
    obtain ⟨t,ht⟩ := C.nodes_nonempty hs
    exact ⟨t,ht,mul_ne_zero (C.nodes_pos ht).ne' (hu t ht)⟩
  obtain ⟨r,hr,hrpos⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun t => t*C.u t) C.node_u_moment1 hnonzero
  have hur : 0 < C.u r := (mul_pos_iff_of_pos_left (C.nodes_pos hr)).mp hrpos
  have hzr := C.node_sign hs hr hur.le
  let A := C.z r/(r*C.u r)
  have hf : ∀ k ≤ 0,∑ t ∈ C.nodes,t^k*C.z t=0 := by
    intro k hk'
    have hk0 : k=0 := by omega
    subst k
    simpa using C.node_z_moment0
  have hg : ∀ k ≤ 0,∑ t ∈ C.nodes,t^k*(t*C.u t)=0 := by
    intro k hk'
    have hk0 : k=0 := by omega
    subst k
    simpa using C.node_u_moment1
  have hprop := moment_kernel_proportional C.nodes C.z (fun t => t*C.u t) 0
    (by omega) hf hg hr hrpos.ne'
  have hfactor := C.factor_coefficients A 0 (C.card_support hs) hu
    (fun t ht => by have hh := hprop t ht; dsimp [A]; nlinarith [hh])
    (fun _ => by simpa using hv0)
  have hy : v 2=A*v 1 := by simpa using hfactor.2.1
  obtain ⟨r,hr,s,hs',hne⟩ := Finset.one_lt_card.mp (show 1 < C.nodes.card by omega)
  obtain ⟨i,hθi,hti,hci⟩ := C.node_has_vertex hr
  obtain ⟨j,hθj,htj,hcj⟩ := C.node_has_vertex hs'
  have hrouth (i : Fin 3) : 0 < α i ∧ γ i < α i*β i := by
    have hh := hurwitz_inequalities (vertex_hurwitz hs i)
    exact ⟨hh.1,hh.2.2.2⟩
  have hhalf (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ G (α i) (β i) (γ i) v t :=
    compact_nonnegative_halfaxis (fun u hu => hw i u hu.1 hu.2) ht
  exact hv (two_contacts_force_zero hrouth hv0 hfactor.1 hy hhalf
    (C.nodes_pos hr) (C.nodes_pos hs') hne hci hcj)

/-- All masses and coefficient cancellations are exhausted. -/
theorem impossible (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (hw : Weak α β γ v) (hv : v ≠ 0)
    (hn : ∀ i,pairPoly (α i) (β i) (γ i) v ≠ 0) : False := by
  have hμ : 0 ≤ ∑ i,C.mu i := Finset.sum_nonneg (fun i _ => C.mu_nonneg i)
  by_cases hμ0 : ∑ i,C.mu i=0
  · exact C.no_infinity hs hw hv hμ0
  have hμpos : 0 < ∑ i,C.mu i := lt_of_le_of_ne hμ (Ne.symm hμ0)
  have hγ : 0 < γ 0 := (hurwitz_inequalities (vertex_hurwitz hs 0)).2.2.1
  have hc : 0 ≤ v 0 := by
    have hh := hw 0 0 le_rfl zero_le_one
    rw [compact_zero] at hh
    exact (mul_nonneg_iff_of_pos_left hγ).mp hh
  by_cases hv0 : v 0=0
  · exact C.infinity_zero_constant hs hw hv hn hμpos hv0
  · exact C.infinity_positive_constant hs hw hn hμpos (lt_of_le_of_ne hc (Ne.symm hv0))

end ContactCertificate

/-- The complete critical-cone lemma, including identically zero pairings,
zero and infinity contacts, coincident frequencies, and all leading signs. -/
theorem weak_strictification (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (v : Vec) (hv : v ≠ 0) (hw : Weak α β γ v) : ∃ w,Strict α β γ w := by
  classical
  by_cases hz : ∃ i,pairPoly (α i) (β i) (γ i) v=0
  · obtain ⟨j,hj⟩ := hz
    exact strictify_zero_pairing α β γ hs v hv hw j hj
  · have hn : ∀ i,pairPoly (α i) (β i) (γ i) v ≠ 0 := fun i hi => hz ⟨i,hi⟩
    by_contra hno
    obtain ⟨C⟩ := exists_contact_certificate α β γ hs v hw hn hno
    exact C.impossible hs hw hv hn

end
end SPR.Polytope.CubicSynthesis
