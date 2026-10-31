import SPR.Polytope.CubicSynthesis.ZeroPairing
import SPR.Polytope.CubicSynthesis.FiniteSeparation
import SPR.Polytope.CubicSynthesis.Homotopy

/-! # A finite contact certificate retaining all three original vertex labels.

Zero-frequency rows are positive multiples of one common row. Each nonzero cubic
pairing contributes at most one positive contact. Infinity keeps its three labels.
-/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section

def finiteRow (α β γ t : ℝ) : Vec :=
  ![γ-α*t,t*(β-t),-t*(γ-α*t),-t^2*(β-t),t^2*(γ-α*t)]

def infinityRow (α : ℝ) : Vec := ![0,0,0,1,-α]

def zeroRow : Vec := ![1,0,0,0,0]

theorem dot_finiteRow (α β γ t : ℝ) (v : Vec) :
    dot v (finiteRow α β γ t)=G α β γ v t := by
  simp [dot,finiteRow,Fin.sum_univ_succ,G]
  ring

theorem dot_infinityRow (α : ℝ) (v : Vec) :
    dot v (infinityRow α)=v 3-α*v 4 := by
  simp [dot,infinityRow,Fin.sum_univ_succ]
  ring

theorem dot_zeroRow (v : Vec) : dot v zeroRow=v 0 := by
  simp [dot,zeroRow,Fin.sum_univ_succ]

/-- All fields are necessary consequences of a finite separator in the complete
five-dimensional numerator space; no coefficient sign is imposed on the numerator. -/
structure ContactCertificate (α β γ : Fin 3 → ℝ) (v : Vec) where
  t : Fin 3 → ℝ
  theta : Fin 3 → ℝ
  mu : Fin 3 → ℝ
  kappa : ℝ
  t_pos : ∀ i, 0 < t i
  theta_nonneg : ∀ i, 0 ≤ theta i
  mu_nonneg : ∀ i, 0 ≤ mu i
  kappa_nonneg : 0 ≤ kappa
  mass : kappa+(∑ i,theta i)+(∑ i,mu i)=1
  finite_contact : ∀ i, 0 < theta i → G (α i) (β i) (γ i) v (t i)=0
  infinite_contact : ∀ i, 0 < mu i → v 3-α i*v 4=0
  zero_contact : 0 < kappa → v 0=0
  moment0 : kappa+∑ i,theta i*(γ i-α i*t i)=0
  moment1 : ∑ i,t i*(theta i*(γ i-α i*t i))=0
  moment2 : ∑ i,(t i)^2*(theta i*(γ i-α i*t i))=∑ i,mu i*α i
  odd0 : ∑ i,theta i*t i*(β i-t i)=0
  odd1 : ∑ i,t i*(theta i*t i*(β i-t i))=∑ i,mu i

/-- Every infeasible strictification of a nonzero weak vector with no identically
zero pairing has this finite certificate. All contacts, including infinity, are kept. -/
theorem exists_contact_certificate (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i)))
    (v : Vec) (hw : Weak α β γ v)
    (hn : ∀ i, pairPoly (α i) (β i) (γ i) v ≠ 0)
    (hno : ¬ ∃ w, Strict α β γ w) : Nonempty (ContactCertificate α β γ v) := by
  classical
  let positive : Fin 3 → Prop := fun i => ∃ t : ℝ,0 < t ∧ G (α i) (β i) (γ i) v t=0
  let t : Fin 3 → ℝ := fun i => if h : positive i then h.choose else 1
  have ht (i : Fin 3) : 0 < t i := by
    dsimp [t]
    split_ifs with hi
    · exact hi.choose_spec.1
    · norm_num
  have hc (i : Fin 3) (hi : positive i) : G (α i) (β i) (γ i) v (t i)=0 := by
    simpa [t,hi] using hi.choose_spec.2
  have hunique (i : Fin 3) (r : ℝ) (hr : 0 < r)
      (hz : G (α i) (β i) (γ i) v r=0) : r=t i := by
    have hi : positive i := ⟨r,hr,hz⟩
    have hhalf : ∀ s : ℝ,0 ≤ s → 0 ≤ (pairPoly (α i) (β i) (γ i) v).eval s := by
      intro s hs'
      rw [pairPoly_eval]
      exact compact_nonnegative_halfaxis (fun u hu => hw i u hu.1 hu.2) hs'
    exact at_most_one_positive_contact (hn i) (pairPoly_degree _ _ _ _) hhalf hr (ht i)
      (by simpa [pairPoly_eval] using hz) (by simpa [pairPoly_eval] using hc i hi)
  let allowed : Fin 7 → Prop :=
    ![v 0=0,positive 0,positive 1,positive 2,
      v 3-α 0*v 4=0,v 3-α 1*v 4=0,v 3-α 2*v 4=0]
  let rows : Fin 7 → Vec :=
    ![zeroRow,finiteRow (α 0) (β 0) (γ 0) (t 0),
      finiteRow (α 1) (β 1) (γ 1) (t 1),finiteRow (α 2) (β 2) (γ 2) (t 2),
      infinityRow (α 0),infinityRow (α 1),infinityRow (α 2)]
  have hsep : ¬ ∃ c : Vec,∀ j,allowed j → 0 < dot c (rows j) := by
    rintro ⟨c,hcpos⟩
    have hcontact : ∀ i u,0 ≤ u → u ≤ 1 → compactG (α i) (β i) (γ i) v u=0 →
        0 < compactG (α i) (β i) (γ i) c u := by
      intro i u hu hu1 he
      by_cases hlast : u=1
      · subst u
        rw [compact_infinity] at he ⊢
        fin_cases i
        · simpa [rows,dot_infinityRow] using hcpos 4 (by simpa [allowed] using he)
        · simpa [rows,dot_infinityRow] using hcpos 5 (by simpa [allowed] using he)
        · simpa [rows,dot_infinityRow] using hcpos 6 (by simpa [allowed] using he)
      · obtain ⟨r,hr,rfl⟩ := finite_compact_parameter hu (lt_of_le_of_ne hu1 hlast)
        rw [compactification _ _ _ _ hr] at he ⊢
        have hz : G (α i) (β i) (γ i) v r=0 :=
          (div_eq_zero_iff.mp he).resolve_right (by positivity)
        apply div_pos _ (by positivity)
        by_cases hr0 : r=0
        · subst r
          have hγ := (hurwitz_inequalities (vertex_hurwitz hs i)).2.2.1
          have hv0 : v 0=0 := by
            have hh : γ i=0 ∨ v 0=0 := by simpa [G] using hz
            exact hh.resolve_left hγ.ne'
          have hc0 : 0 < c 0 := by simpa [rows,dot_zeroRow] using hcpos 0 (by
            simpa [allowed] using hv0)
          simpa [G] using mul_pos hγ hc0
        · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
          have hp : positive i := ⟨r,hrpos,hz⟩
          rw [hunique i r hrpos hz]
          fin_cases i
          · simpa [rows,dot_finiteRow] using hcpos 1 (by simpa [allowed] using hp)
          · simpa [rows,dot_finiteRow] using hcpos 2 (by simpa [allowed] using hp)
          · simpa [rows,dot_finiteRow] using hcpos 3 (by simpa [allowed] using hp)
    let K := Fin 3 × Parameter
    let f : K → ℝ := fun p => compactG (α p.1) (β p.1) (γ p.1) v p.2
    let g : K → ℝ := fun p => compactG (α p.1) (β p.1) (γ p.1) c p.2
    have hf : Continuous f := by
      change Continuous (fun p : Fin 3 × Parameter =>
        compactG (α p.1) (β p.1) (γ p.1) v p.2)
      dsimp [compactG]; fun_prop
    have hg : Continuous g := by
      change Continuous (fun p : Fin 3 × Parameter =>
        compactG (α p.1) (β p.1) (γ p.1) c p.2)
      dsimp [compactG]; fun_prop
    obtain ⟨ε,hε,hstrict⟩ := compact_weak_strictification f g hf hg
      (fun p => hw p.1 p.2 p.2.property.1 p.2.property.2)
      (fun p hp => hcontact p.1 p.2 p.2.property.1 p.2.property.2 hp)
    apply hno
    refine ⟨v+ε • c,?_⟩
    intro i u hu hu1
    simpa only [compactG_add,compactG_smul,f,g] using hstrict (i,⟨u,hu,hu1⟩)
  obtain ⟨w,hwn,hwz,hwm,hwr⟩ := indexed_finite_separation allowed rows hsep
  let theta : Fin 3 → ℝ := ![w 1,w 2,w 3]
  let mu : Fin 3 → ℝ := ![w 4,w 5,w 6]
  have hfinite : ∀ i,0 < theta i → positive i := by
    intro i hi
    by_contra hh
    fin_cases i <;> simp [theta] at hi
    · rw [hwz 1 (by simpa [allowed] using hh)] at hi; linarith
    · rw [hwz 2 (by simpa [allowed] using hh)] at hi; linarith
    · rw [hwz 3 (by simpa [allowed] using hh)] at hi; linarith
  have hinfinite : ∀ i,0 < mu i → v 3-α i*v 4=0 := by
    intro i hi
    by_contra hh
    fin_cases i <;> simp [mu] at hi
    · rw [hwz 4 (by simpa [allowed] using hh)] at hi; linarith
    · rw [hwz 5 (by simpa [allowed] using hh)] at hi; linarith
    · rw [hwz 6 (by simpa [allowed] using hh)] at hi; linarith
  have hcoord (j : Fin 5) := congrArg (fun p : Vec => p j) hwr
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hcoord
  refine ⟨{
    t := t
    theta := theta
    mu := mu
    kappa := w 0
    t_pos := ht
    theta_nonneg := ?_
    mu_nonneg := ?_
    kappa_nonneg := hwn 0
    mass := ?_
    finite_contact := fun i hi => hc i (hfinite i hi)
    infinite_contact := hinfinite
    zero_contact := ?_
    moment0 := ?_
    moment1 := ?_
    moment2 := ?_
    odd0 := ?_
    odd1 := ?_ }⟩
  · intro i; fin_cases i <;> exact hwn _
  · intro i; fin_cases i <;> exact hwn _
  · simpa [theta,mu,Fin.sum_univ_succ,add_assoc] using hwm
  · intro hi
    by_contra hn
    rw [hwz 0 (by simpa [allowed] using hn)] at hi
    linarith
  · simpa [rows,zeroRow,finiteRow,infinityRow,theta,Fin.sum_univ_succ] using hcoord 0
  · have hh := hcoord 2
    simp [rows,zeroRow,finiteRow,infinityRow,theta,Fin.sum_univ_succ] at hh ⊢
    linarith
  · have hh := hcoord 4
    simp [rows,zeroRow,finiteRow,infinityRow,theta,mu,Fin.sum_univ_succ] at hh ⊢
    linarith
  · simpa [rows,zeroRow,finiteRow,infinityRow,theta,Fin.sum_univ_succ,mul_assoc]
      using hcoord 1
  · have hh := hcoord 3
    simp [rows,zeroRow,finiteRow,infinityRow,theta,mu,Fin.sum_univ_succ] at hh ⊢
    nlinarith

end
end SPR.Polytope.CubicSynthesis
