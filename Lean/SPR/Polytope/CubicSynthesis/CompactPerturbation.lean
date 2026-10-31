import SPR.Polytope.CubicSynthesis.Pairing

/-! # Compact strictness permits an actual quartic leading coefficient of either sign. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section

/-- A positive continuous function on a compact domain keeps its sign under a
small fixed continuous perturbation. Both δ and δ/2 are controlled. -/
theorem compact_positive_perturbation {ι : Type*} [TopologicalSpace ι] [CompactSpace ι]
    (f g : ι → ℝ) (hf : Continuous f) (hg : Continuous g) (hp : ∀ i, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ i, 0 < f i+ε*g i := by
  obtain ⟨μ,hμ,hlower⟩ := isCompact_univ.exists_forall_le' hf.continuousOn
    (fun i _ => hp i)
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  let δ := μ/(|M|+1)
  refine ⟨δ,by dsimp [δ]; positivity,?_⟩
  intro ε hε hεδ i
  have hfi := hlower i (Set.mem_univ i)
  have hgi := hM i (Set.mem_univ i)
  have hlo : -|M| ≤ g i := by
    have hh : |g i| ≤ |M| := hgi.trans (le_abs_self M)
    exact (abs_le.mp hh).1
  have hsmall : ε*(|M|+1) ≤ μ := (le_div_iff₀ (by positivity)).mp hεδ
  nlinarith [abs_nonneg M]

theorem compactG_add (α β γ : ℝ) (v w : Vec) (u : ℝ) :
    compactG α β γ (v+w) u=compactG α β γ v u+compactG α β γ w u := by
  simp [compactG]
  ring

theorem compactG_smul (α β γ : ℝ) (v : Vec) (ε u : ℝ) :
    compactG α β γ (ε • v) u=ε*compactG α β γ v u := by
  simp [compactG]
  ring

/-- A direction positive on every zero of a continuous nonnegative function
strictifies it on a compact domain. No uniform positive margin for `f` is assumed. -/
theorem compact_weak_strictification {ι : Type*} [TopologicalSpace ι] [CompactSpace ι]
    (f g : ι → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hn : ∀ i, 0 ≤ f i) (hz : ∀ i, f i=0 → 0 < g i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 < f i+ε*g i := by
  let K : Set ι := {i | g i ≤ 0}
  have hK : IsCompact K := (isClosed_le hg continuous_const).isCompact
  obtain ⟨μ,hμ,hlower⟩ := hK.exists_forall_le' hf.continuousOn (by
    intro i hi
    have hne : f i ≠ 0 := by
      intro he
      have hh := hz i he
      exact (not_lt_of_ge hi) hh
    exact lt_of_le_of_ne (hn i) (Ne.symm hne))
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  let ε := μ/(|M|+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  intro i
  by_cases hi : g i ≤ 0
  · have hfi := hlower i hi
    have hgi : -|M| ≤ g i :=
      (abs_le.mp ((hM i (Set.mem_univ i)).trans (le_abs_self M))).1
    have hsmall : ε*(|M|+1)=μ := by dsimp [ε]; field_simp
    nlinarith [abs_nonneg M]
  · have hp : 0 < g i := lt_of_not_ge hi
    exact add_pos_of_nonneg_of_pos (hn i) (mul_pos hε hp)

/-- Exact degree four follows by perturbing the full coefficient vector, without
choosing a sign for the quartic coefficient in advance. -/
theorem exact_quartic_of_compact (α β γ : Fin 3 → ℝ) (v : Vec)
    (hp : ∀ i u, 0 ≤ u → u ≤ 1 → 0 < compactG (α i) (β i) (γ i) v u) :
    ∃ w : Vec, (numerator w).natDegree=4 ∧
      ∀ i u, 0 ≤ u → u ≤ 1 → 0 < compactG (α i) (β i) (γ i) w u := by
  let ι := Fin 3 × Set.Icc (0:ℝ) 1
  let f : ι → ℝ := fun x => compactG (α x.1) (β x.1) (γ x.1) v x.2
  let g : ι → ℝ := fun x => compactG (α x.1) (β x.1) (γ x.1) (Pi.single 4 1) x.2
  have hf : Continuous f := by
    change Continuous (fun x : Fin 3 × Set.Icc (0:ℝ) 1 =>
      compactG (α x.1) (β x.1) (γ x.1) v x.2)
    dsimp [compactG]
    fun_prop
  have hg : Continuous g := by
    change Continuous (fun x : Fin 3 × Set.Icc (0:ℝ) 1 =>
      compactG (α x.1) (β x.1) (γ x.1) (Pi.single 4 1) x.2)
    dsimp [compactG]
    fun_prop
  obtain ⟨δ,hδ,hcontrol⟩ := compact_positive_perturbation f g hf hg
    (fun x => hp x.1 x.2 x.2.property.1 x.2.property.2)
  have choose_step : ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ v 4+ε ≠ 0 := by
    by_cases h : v 4+δ=0
    · refine ⟨δ/2,by positivity,by linarith,?_⟩
      linarith
    · exact ⟨δ,hδ,le_rfl,h⟩
  obtain ⟨ε,hε,hεδ,hlead⟩ := choose_step
  let w := v+ε • Pi.single 4 (1:ℝ)
  refine ⟨w,?_,?_⟩
  · apply natDegree_eq_of_le_of_coeff_ne_zero (numerator_degree w)
    have hc : (numerator w).coeff 4=w 4 := coefficients_numerator w ⟨4,by omega⟩
    rw [hc]
    simpa [w,Pi.single_apply] using hlead
  · intro i u hu hu1
    have hh := hcontrol ε hε hεδ (i,⟨u,hu,hu1⟩)
    simpa only [w,compactG_add,compactG_smul,f,g] using hh

end
end SPR.Polytope.CubicSynthesis
