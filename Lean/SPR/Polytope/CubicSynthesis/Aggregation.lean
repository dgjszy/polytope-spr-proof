import SPR.Polytope.CubicSynthesis.ContactCertificate
import SPR.Polytope.CubicSynthesis.Moments
import SPR.Polytope.CubicFourVertices.Stability

/-! # Merging repeated finite contact frequencies without losing hull stability. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section

/-- The strict node sign uses stability of the actual convex combination, not
merely the three vertex Routh inequalities. -/
theorem weighted_node_sign (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (weights : Fin 3 → ℝ) (hn : ∀ i,0 ≤ weights i) (hm : 0 < ∑ i,weights i)
    {t : ℝ} (ht : 0 < t) (hu : 0 ≤ ∑ i,weights i*(γ i-α i*t)) :
    0 < ∑ i,weights i*t*(β i-t) := by
  let M := ∑ i,weights i
  let q : Fin 3 → ℝ := fun i => weights i/M
  have hM : 0 < M := hm
  have hMne : M ≠ 0 := hM.ne'
  have hq : Weights q := by
    constructor
    · intro i; exact div_nonneg (hn i) hM.le
    · simp [q,← Finset.sum_div,M,hMne]
  have ha := hs q hq
  rw [CubicFourVertices.blend_cubics α β γ q hq.2] at ha
  obtain ⟨hα,hβ,hγ,hD⟩ := hurwitz_inequalities ha
  have hU : 0 ≤ (∑ i,q i*γ i)-(∑ i,q i*α i)*t := by
    have he : (∑ i,q i*γ i)-(∑ i,q i*α i)*t=
        (∑ i,weights i*(γ i-α i*t))/M := by
      simp only [q,Fin.sum_univ_succ,Fin.isValue,Fin.reduceFinMk]
      field_simp
      ring
    rw [he]
    exact div_nonneg hu hM.le
  have hb : t < ∑ i,q i*β i := by nlinarith
  have he : (∑ i,weights i*t*(β i-t))=
      M*t*((∑ i,q i*β i)-t) := by
    simp only [q,Fin.sum_univ_succ,Fin.isValue,Fin.reduceFinMk]
    field_simp
    simp only [M,Fin.sum_univ_succ,Fin.isValue,Fin.reduceFinMk]
    ring
  rw [he]
  exact mul_pos (mul_pos hM ht) (sub_pos.mpr hb)

namespace ContactCertificate
variable {α β γ : Fin 3 → ℝ} {v : Vec}

def active (C : ContactCertificate α β γ v) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => 0 < C.theta i)

def nodes (C : ContactCertificate α β γ v) : Finset ℝ := C.active.image C.t

def support (C : ContactCertificate α β γ v) : Finset ℝ :=
  if 0 < C.kappa then insert 0 C.nodes else C.nodes

def group (C : ContactCertificate α β γ v) (f : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => C.t i=t), f i

def u (C : ContactCertificate α β γ v) (t : ℝ) : ℝ :=
  (if t=0 then C.kappa else 0)+C.group (fun i => C.theta i*(γ i-α i*C.t i)) t

def z (C : ContactCertificate α β γ v) (t : ℝ) : ℝ :=
  C.group (fun i => C.theta i*C.t i*(β i-C.t i)) t

theorem nodes_pos (C : ContactCertificate α β γ v) {t : ℝ} (ht : t ∈ C.nodes) :
    0 < t := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
  exact C.t_pos i

theorem zero_not_nodes (C : ContactCertificate α β γ v) : 0 ∉ C.nodes :=
  fun h => (lt_irrefl (0:ℝ)) (C.nodes_pos h)

theorem theta_zero_off_active (C : ContactCertificate α β γ v) {i : Fin 3}
    (hi : i ∉ C.active) : C.theta i=0 := by
  have hh : ¬ 0 < C.theta i := by simpa [active] using hi
  exact le_antisymm (le_of_not_gt hh) (C.theta_nonneg i)

theorem group_zero (C : ContactCertificate α β γ v) (f : Fin 3 → ℝ) :
    C.group f 0=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2
  exact ((C.t_pos i).ne' hh).elim

theorem u_zero (C : ContactCertificate α β γ v) : C.u 0=C.kappa := by
  simp [u,group_zero]

theorem z_zero (C : ContactCertificate α β γ v) : C.z 0=0 := C.group_zero _

/-- Summing fibres discards only atoms whose certified weight is zero. -/
theorem sum_groups (C : ContactCertificate α β γ v) (f : Fin 3 → ℝ)
    (hf : ∀ i,C.theta i=0 → f i=0) : ∑ t ∈ C.nodes,C.group f t=∑ i,f i := by
  classical
  simp only [group]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hti : C.t i ∉ C.nodes := by simpa using hi
  have htheta : C.theta i=0 := C.theta_zero_off_active (by
    intro hh
    exact hti (Finset.mem_image.mpr ⟨i,hh,rfl⟩))
  exact hf i htheta

theorem group_mul (C : ContactCertificate α β γ v) (f : Fin 3 → ℝ)
    (p : ℝ → ℝ) (t : ℝ) :
    p t*C.group f t=C.group (fun i => p (C.t i)*f i) t := by
  classical
  rw [group,Finset.mul_sum,group]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem sum_node_u (C : ContactCertificate α β γ v) (p : ℝ → ℝ) :
    ∑ t ∈ C.nodes,p t*C.u t=
      ∑ i,p (C.t i)*(C.theta i*(γ i-α i*C.t i)) := by
  classical
  calc
    ∑ t ∈ C.nodes,p t*C.u t=
      ∑ t ∈ C.nodes,C.group (fun i => p (C.t i)*(C.theta i*(γ i-α i*C.t i))) t := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht0 : t ≠ 0 := (C.nodes_pos ht).ne'
        simp only [u,if_neg ht0,zero_add]
        exact C.group_mul _ p t
    _=_ := C.sum_groups _ (fun i hi => by rw [hi]; ring)

theorem sum_support_u (C : ContactCertificate α β γ v) (p : ℝ → ℝ) :
    ∑ t ∈ C.support,p t*C.u t=
      p 0*C.kappa+∑ i,p (C.t i)*(C.theta i*(γ i-α i*C.t i)) := by
  classical
  by_cases hk : 0 < C.kappa
  · rw [support,if_pos hk,Finset.sum_insert C.zero_not_nodes,C.u_zero,C.sum_node_u]
  · have hk0 : C.kappa=0 := le_antisymm (le_of_not_gt hk) C.kappa_nonneg
    rw [support,if_neg hk,C.sum_node_u,hk0,mul_zero,zero_add]

theorem sum_support_z (C : ContactCertificate α β γ v) (p : ℝ → ℝ) :
    ∑ t ∈ C.support,p t*C.z t=
      ∑ i,p (C.t i)*(C.theta i*C.t i*(β i-C.t i)) := by
  classical
  have he : ∑ t ∈ C.nodes,p t*C.z t=
      ∑ i,p (C.t i)*(C.theta i*C.t i*(β i-C.t i)) := by
    simp only [z,C.group_mul]
    exact C.sum_groups _ (fun i hi => by rw [hi]; ring)
  by_cases hk : 0 < C.kappa
  · rw [support,if_pos hk,Finset.sum_insert C.zero_not_nodes,C.z_zero,mul_zero,zero_add,he]
  · rw [support,if_neg hk,he]

theorem u_moment0 (C : ContactCertificate α β γ v) : ∑ t ∈ C.support,C.u t=0 := by
  have hh := C.sum_support_u (fun _ => 1)
  simp only [one_mul] at hh
  exact hh.trans C.moment0

theorem u_moment1 (C : ContactCertificate α β γ v) : ∑ t ∈ C.support,t*C.u t=0 := by
  simpa using C.sum_support_u id |>.trans (by simpa using C.moment1)

theorem u_moment2 (C : ContactCertificate α β γ v) :
    ∑ t ∈ C.support,t^2*C.u t=∑ i,C.mu i*α i := by
  simpa using C.sum_support_u (fun t => t^2) |>.trans (by simpa using C.moment2)

theorem z_moment0 (C : ContactCertificate α β γ v) : ∑ t ∈ C.support,C.z t=0 := by
  have hh := C.sum_support_z (fun _ => 1)
  simp only [one_mul] at hh
  exact hh.trans C.odd0

theorem z_moment1 (C : ContactCertificate α β γ v) :
    ∑ t ∈ C.support,t*C.z t=∑ i,C.mu i := by
  exact C.sum_support_z id |>.trans C.odd1

theorem node_sign (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    {t : ℝ} (ht : t ∈ C.nodes) (hu : 0 ≤ C.u t) : 0 < C.z t := by
  classical
  let weights : Fin 3 → ℝ := fun i => if C.t i=t then C.theta i else 0
  have htpos := C.nodes_pos ht
  have hn (i : Fin 3) : 0 ≤ weights i := by
    dsimp [weights]; split_ifs; exact C.theta_nonneg i; exact le_rfl
  have hmass : 0 < ∑ i,weights i := by
    obtain ⟨i,hi,hti⟩ := Finset.mem_image.mp ht
    refine Finset.sum_pos' (fun j _ => hn j) ⟨i,Finset.mem_univ i,?_⟩
    simpa [weights,hti] using (Finset.mem_filter.mp hi).2
  have hU : C.u t=∑ i,weights i*(γ i-α i*t) := by
    simp only [u,if_neg htpos.ne',zero_add,group,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [weights]
    split_ifs with hi
    · rw [hi]
    · ring
  have hV : C.z t=∑ i,weights i*t*(β i-t) := by
    simp only [z,group,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [weights]
    split_ifs with hi
    · rw [hi]
    · ring
  rw [hV]
  apply weighted_node_sign α β γ hs weights hn hmass htpos
  rwa [← hU]

theorem support_nonneg (C : ContactCertificate α β γ v) {t : ℝ}
    (ht : t ∈ C.support) : 0 ≤ t := by
  classical
  by_cases hk : 0 < C.kappa
  · rw [support,if_pos hk,Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact le_rfl
    · exact (C.nodes_pos ht).le
  · rw [support,if_neg hk] at ht
    exact (C.nodes_pos ht).le

theorem zero_mem_support_iff (C : ContactCertificate α β γ v) :
    0 ∈ C.support ↔ 0 < C.kappa := by
  classical
  by_cases hk : 0 < C.kappa <;> simp [support,hk,C.zero_not_nodes]

theorem positive_support_node (C : ContactCertificate α β γ v) {t : ℝ}
    (ht : t ∈ C.support) (htpos : 0 < t) : t ∈ C.nodes := by
  classical
  by_cases hk : 0 < C.kappa
  · simpa [support,hk,htpos.ne'] using ht
  · simpa [support,hk] using ht

theorem mu_zero_of_sum_zero (C : ContactCertificate α β γ v) (h : ∑ i,C.mu i=0) :
    ∀ i,C.mu i=0 := by
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => C.mu_nonneg i)).mp h
  exact fun i => hh i (Finset.mem_univ i)

theorem nodes_nonempty (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i))) :
    C.nodes.Nonempty := by
  classical
  by_contra hn
  have htheta (i : Fin 3) : C.theta i=0 := C.theta_zero_off_active (by
    intro hi
    exact hn ⟨C.t i,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩)
  have hκ : C.kappa=0 := by simpa [htheta] using C.moment0
  have hα (i : Fin 3) : 0 < α i := (hurwitz_inequalities (vertex_hurwitz hs i)).1
  have hweighted : ∑ i,C.mu i*α i=0 := by simpa [htheta] using C.moment2.symm
  have hmu (i : Fin 3) : C.mu i=0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (C.mu_nonneg j) (hα j).le)).mp hweighted i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hh).resolve_right (hα i).ne'
  have hm := C.mass
  simp [htheta,hmu,hκ] at hm

theorem support_nonempty (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i))) :
    C.support.Nonempty := by
  classical
  obtain ⟨t,ht⟩ := C.nodes_nonempty hs
  refine ⟨t,?_⟩
  by_cases hk : 0 < C.kappa <;> simp [support,hk,ht]

/-- No infinity mass requires at least four distinct finite nodes, including zero. -/
theorem card_support_of_no_infinity (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (hmu : ∑ i,C.mu i=0) : 4 ≤ C.support.card := by
  by_contra hn
  have hsmall : C.support.card ≤ 2+1 := by omega
  apply no_small_moment_support C.support C.u C.z 2 (C.support_nonempty hs) hsmall
    (fun t ht => C.support_nonneg ht)
    (fun ht => by rw [C.u_zero]; exact C.zero_mem_support_iff.mp ht)
    (fun t ht hp hu => C.node_sign hs (C.positive_support_node ht hp) hu) C.z_moment0
  intro k hk
  interval_cases k
  · simpa using C.u_moment0
  · simpa using C.u_moment1
  · simpa [C.mu_zero_of_sum_zero hmu] using C.u_moment2

/-- With infinity mass, the first two moments still force three finite nodes. -/
theorem card_support (C : ContactCertificate α β γ v)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i))) :
    3 ≤ C.support.card := by
  by_contra hn
  have hsmall : C.support.card ≤ 1+1 := by omega
  apply no_small_moment_support C.support C.u C.z 1 (C.support_nonempty hs) hsmall
    (fun t ht => C.support_nonneg ht)
    (fun ht => by rw [C.u_zero]; exact C.zero_mem_support_iff.mp ht)
    (fun t ht hp hu => C.node_sign hs (C.positive_support_node ht hp) hu) C.z_moment0
  intro k hk
  interval_cases k
  · simpa using C.u_moment0
  · simpa using C.u_moment1

theorem nodes_card_le (C : ContactCertificate α β γ v) : C.nodes.card ≤ 3 := by
  exact (Finset.card_image_le.trans (Finset.card_le_card (Finset.subset_univ C.active))).trans
    (by simp)

theorem full_nodes (C : ContactCertificate α β γ v) (hc : C.nodes.card=3) :
    (∀ i,0 < C.theta i) ∧ Function.Injective C.t := by
  classical
  have hactive : C.active=Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ _) (by
      have hh := Finset.card_image_le (f := C.t) (s := C.active)
      rw [← nodes] at hh
      simpa [hc] using hh)
  have hinj : Set.InjOn C.t (C.active : Set (Fin 3)) := Finset.card_image_iff.mp (by
    simpa [nodes,hactive] using hc)
  constructor
  · intro i
    have hi : i ∈ C.active := by rw [hactive]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  · intro i j he
    exact hinj (by simp [hactive]) (by simp [hactive]) he

theorem node_has_vertex (C : ContactCertificate α β γ v) {r : ℝ} (hr : r ∈ C.nodes) :
    ∃ i,0 < C.theta i ∧ C.t i=r ∧ G (α i) (β i) (γ i) v r=0 := by
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hr
  have hp := (Finset.mem_filter.mp hi).2
  exact ⟨i,hp,he,by rw [← he]; exact C.finite_contact i hp⟩

theorem sum_node_z (C : ContactCertificate α β γ v) (p : ℝ → ℝ) :
    ∑ t ∈ C.nodes,p t*C.z t=∑ i,p (C.t i)*(C.theta i*C.t i*(β i-C.t i)) := by
  simp only [z,C.group_mul]
  exact C.sum_groups _ (fun i hi => by rw [hi]; ring)

theorem node_u_moment1 (C : ContactCertificate α β γ v) : ∑ t ∈ C.nodes,t*C.u t=0 := by
  exact (C.sum_node_u id).trans C.moment1

theorem node_u_moment2 (C : ContactCertificate α β γ v) :
    ∑ t ∈ C.nodes,t^2*C.u t=∑ i,C.mu i*α i := by
  exact (C.sum_node_u (fun t => t^2)).trans C.moment2

theorem node_z_moment0 (C : ContactCertificate α β γ v) : ∑ t ∈ C.nodes,C.z t=0 := by
  have hh := C.sum_node_z (fun _ => 1)
  simp only [one_mul] at hh
  exact hh.trans C.odd0

theorem node_z_moment1 (C : ContactCertificate α β γ v) :
    ∑ t ∈ C.nodes,t*C.z t=∑ i,C.mu i := (C.sum_node_z id).trans C.odd1

/-- At a merged positive node the actual numerator is orthogonal to the merged
denominator value. Every contributing original atom is a genuine contact. -/
theorem node_contact_equation (C : ContactCertificate α β γ v) {r : ℝ}
    (hr : r ∈ C.nodes) :
    (v 4*r^2-v 2*r+v 0)*C.u r+(v 1-v 3*r)*C.z r=0 := by
  classical
  have hrpos := C.nodes_pos hr
  have hz : C.group (fun i => C.theta i*G (α i) (β i) (γ i) v (C.t i)) r=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hθ : C.theta i=0
    · rw [hθ,zero_mul]
    · rw [C.finite_contact i (lt_of_le_of_ne (C.theta_nonneg i) (Ne.symm hθ)),mul_zero]
  have he : (v 4*r^2-v 2*r+v 0)*C.u r+(v 1-v 3*r)*C.z r=
      C.group (fun i => C.theta i*G (α i) (β i) (γ i) v (C.t i)) r := by
    simp only [u,if_neg hrpos.ne',zero_add,z,group,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
    dsimp [G]
    ring
  exact he.trans hz

end ContactCertificate
end
end SPR.Polytope.CubicSynthesis
