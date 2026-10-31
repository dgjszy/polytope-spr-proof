import SPR.Polytope.CubicSynthesis.CompactPerturbation

/-! # Open and closed continuation for the complete five-dimensional synthesis cone.

This module isolates the topological argument from the contact algebra. Its
strictification hypothesis is exposed, and is discharged by the synthesis module.
-/
namespace SPR.Polytope.CubicSynthesis
open Polynomial Filter
open scoped Topology
noncomputable section

abbrev Parameter := Set.Icc (0:ℝ) 1

def Strict (α β γ : Fin 3 → ℝ) (v : Vec) : Prop :=
  ∀ i u, 0 ≤ u → u ≤ 1 → 0 < compactG (α i) (β i) (γ i) v u

def Weak (α β γ : Fin 3 → ℝ) (v : Vec) : Prop :=
  ∀ i u, 0 ≤ u → u ≤ 1 → 0 ≤ compactG (α i) (β i) (γ i) v u

theorem strict_vector_nonzero {α β γ : Fin 3 → ℝ} {v : Vec}
    (hv : Strict α β γ v) : v ≠ 0 := by
  intro hz
  have hh := hv 0 0 le_rfl zero_le_one
  simp [hz,compactG] at hh

/-- One normalized subsequence, chosen before any frequency, closes the feasible
parameter set whenever every nonzero weak limit can be strictified. -/
theorem continuation (α β γ : Parameter → Fin 3 → ℝ)
    (hα : Continuous α) (hβ : Continuous β) (hγ : Continuous γ)
    (hregular : ∀ τ v, v ≠ 0 → Weak (α τ) (β τ) (γ τ) v →
      ∃ w, Strict (α τ) (β τ) (γ τ) w)
    (hinitial : ∃ v, Strict (α ⟨0,le_rfl,zero_le_one⟩)
      (β ⟨0,le_rfl,zero_le_one⟩) (γ ⟨0,le_rfl,zero_le_one⟩) v) :
    ∀ τ, ∃ v, Strict (α τ) (β τ) (γ τ) v := by
  classical
  let T : Set Parameter := {τ | ∃ v, Strict (α τ) (β τ) (γ τ) v}
  have hOpen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    rintro τ ⟨v,hv⟩
    let K := Fin 3 × Parameter
    let f : Parameter × K → ℝ := fun p =>
      compactG (α p.1 p.2.1) (β p.1 p.2.1) (γ p.1 p.2.1) v p.2.2
    have hf : Continuous f := by
      change Continuous (fun p : Parameter × (Fin 3 × Parameter) =>
        compactG (α p.1 p.2.1) (β p.1 p.2.1) (γ p.1 p.2.1) v p.2.2)
      have he : Continuous (fun p : (Fin 3 → ℝ) × Fin 3 => p.1 p.2) :=
        continuous_prod_of_discrete_right.mpr (fun i => continuous_apply i)
      have ca := he.comp ((hα.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd) :
          Continuous (fun p : Parameter × (Fin 3 × Parameter) => (α p.1,p.2.1)))
      have cb := he.comp ((hβ.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd) :
          Continuous (fun p : Parameter × (Fin 3 × Parameter) => (β p.1,p.2.1)))
      have cc := he.comp ((hγ.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd) :
          Continuous (fun p : Parameter × (Fin 3 × Parameter) => (γ p.1,p.2.1)))
      have hb : Continuous (fun p : ℝ × ℝ × ℝ × Vec × ℝ =>
          compactG p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
        dsimp [compactG]
        fun_prop
      exact hb.comp (ca.prodMk (cb.prodMk (cc.prodMk
        (continuous_const.prodMk (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd))))))
    have he : ∀ᶠ σ in 𝓝 τ, ∀ q : K, 0 < f (σ,q) := by
      have hh := isCompact_univ.eventually_forall_of_forall_eventually
        (K := (Set.univ : Set K)) (x₀ := τ) (P := fun σ q => 0 < f (σ,q)) (by
          intro q _
          exact hf.continuousAt.eventually (Ioi_mem_nhds
            (hv q.1 q.2 q.2.property.1 q.2.property.2)))
      simpa only [Set.mem_univ,true_implies] using hh
    filter_upwards [he] with σ hσ
    exact ⟨v,fun i u hu hu1 => hσ (i,⟨u,hu,hu1⟩)⟩
  have hClosed : IsClosed T := by
    apply isSeqClosed_iff_isClosed.mp
    intro σ τ hσ hτ
    choose v hv using hσ
    have hn (j : ℕ) : numerator (v j) ≠ 0 :=
      numerator_nonzero (strict_vector_nonzero (hv j))
    obtain ⟨w,φ,hφ,hwnorm,hlim⟩ := Transfer.normalized_subsequence 4
      (fun j => numerator (v j)) (fun j => numerator_degree (v j)) hn
    have hcoeff (j : ℕ) : Transfer.coefficients 4 (numerator (v j))=v j := by
      funext i
      exact coefficients_numerator (v j) i
    simp only [hcoeff] at hlim
    have hwne : w ≠ 0 := by intro he; simp [he] at hwnorm
    apply hregular τ w hwne
    intro i u hu hu1
    have hc : Continuous (fun p : Parameter × Vec =>
        compactG (α p.1 i) (β p.1 i) (γ p.1 i) p.2 u) := by
      dsimp [compactG]
      fun_prop
    have hparameter := hτ.comp hφ.tendsto_atTop
    have hh := hc.tendsto (τ,w) |>.comp (hparameter.prodMk_nhds hlim)
    apply ge_of_tendsto hh
    apply Eventually.of_forall
    intro j
    change 0 ≤ compactG (α (σ (φ j)) i) (β (σ (φ j)) i) (γ (σ (φ j)) i)
      ((‖v (φ j)‖⁻¹ : ℝ) • v (φ j)) u
    rw [compactG_smul]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ((hv (φ j) i u hu hu1).le)
  have heq : T=Set.univ := IsClopen.eq_univ ⟨hClosed,hOpen⟩
    ⟨⟨0,le_rfl,zero_le_one⟩,hinitial⟩
  intro τ
  have hh : τ ∈ T := by rw [heq]; exact Set.mem_univ τ
  exact hh

end
end SPR.Polytope.CubicSynthesis
