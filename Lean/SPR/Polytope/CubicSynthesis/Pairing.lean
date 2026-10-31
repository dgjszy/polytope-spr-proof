import SPR.Polytope.CubicTriangle.Basic
import SPR.Polytope.QuarticTriangle.Exclusion
import SPR.Polytope.Transfer.Normalization

/-! # Full quartic numerator space against a cubic denominator and its compactification. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial Complex
noncomputable section

abbrev Vec := Fin 5 → ℝ

def numerator (v : Vec) : ℝ[X] :=
  C (v 0)+C (v 1)*X+C (v 2)*X^2+C (v 3)*X^3+C (v 4)*X^4

def G (α β γ : ℝ) (v : Vec) (t : ℝ) : ℝ :=
  (v 3-α*v 4)*t^3+(γ*v 4+α*v 2-β*v 3-v 1)*t^2+
    (β*v 1-γ*v 2-α*v 0)*t+γ*v 0

/-- u=t/(1+t) compactifies the half-axis. u=1 is the real-part limit at infinity. -/
def compactG (α β γ : ℝ) (v : Vec) (u : ℝ) : ℝ :=
  (v 3-α*v 4)*u^3+(γ*v 4+α*v 2-β*v 3-v 1)*u^2*(1-u)+
    (β*v 1-γ*v 2-α*v 0)*u*(1-u)^2+γ*v 0*(1-u)^3

theorem pairing_identity (α β γ : ℝ) (v : Vec) (ω : ℝ) :
    Segment.pairing (CubicTriangle.cubic α β γ) (numerator v) ω=G α β γ v (ω^2) := by
  simp [Segment.pairing,Segment.value,CubicTriangle.cubic,numerator,G,pow_succ,
    Complex.mul_re,Complex.mul_im]
  ring

theorem compactification (α β γ : ℝ) (v : Vec) {t : ℝ} (ht : 0 ≤ t) :
    compactG α β γ v (t/(1+t))=G α β γ v t/(1+t)^3 := by
  have hn : (1+t) ≠ 0 := by linarith
  dsimp [compactG,G]
  field_simp
  ring

theorem compact_infinity (α β γ : ℝ) (v : Vec) :
    compactG α β γ v 1=v 3-α*v 4 := by simp [compactG]

theorem compact_zero (α β γ : ℝ) (v : Vec) :
    compactG α β γ v 0=γ*v 0 := by simp [compactG]

theorem compact_nonnegative_halfaxis {α β γ : ℝ} {v : Vec}
    (hv : ∀ u ∈ Set.Icc (0:ℝ) 1, 0 ≤ compactG α β γ v u)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ G α β γ v t := by
  have hu : t/(1+t) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩
  have hh := hv _ hu
  rw [compactification _ _ _ _ ht] at hh
  have hh' := mul_nonneg hh (show 0 ≤ (1+t)^3 by positivity)
  simpa only [div_mul_cancel₀ _ (show (1+t)^3 ≠ 0 by positivity)] using hh'

/-- Every finite compact parameter has a nonnegative half-axis representative. -/
theorem finite_compact_parameter {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    ∃ t : ℝ, 0 ≤ t ∧ u=t/(1+t) := by
  refine ⟨u/(1-u),by positivity,?_⟩
  have hn : 1-u ≠ 0 := by linarith
  field_simp
  ring

theorem numerator_degree (v : Vec) : (numerator v).natDegree ≤ 4 := by
  unfold numerator
  compute_degree!

theorem coefficients_numerator (v : Vec) (i : Fin 5) : (numerator v).coeff i=v i := by
  fin_cases i <;> simp [numerator]

theorem numerator_nonzero {v : Vec} (hv : v ≠ 0) : numerator v ≠ 0 := by
  intro hn
  apply hv
  funext i
  have hh := coefficients_numerator v i
  rw [hn] at hh
  simpa using hh.symm

theorem reconstruction {B : ℝ[X]} (hd : B.natDegree ≤ 4) :
    numerator (fun i => B.coeff i)=B := by
  have h5 : B.coeff 5=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have he := QuarticTriangle.numerator_eq (show B.natDegree ≤ 5 by omega)
  simpa [QuarticTriangle.numerator,numerator,h5,add_assoc,add_comm,add_left_comm] using he

theorem strict_of_compact {α β γ : ℝ} (ha : IsHurwitz (CubicTriangle.cubic α β γ))
    (v : Vec) (hv : ∀ u ∈ Set.Icc (0:ℝ) 1, 0 < compactG α β γ v u) :
    Segment.FrequencySPR (CubicTriangle.cubic α β γ) (numerator v) := by
  rw [Segment.frequencySPR_iff_pairing_pos ha]
  intro ω
  rw [pairing_identity]
  have ht : 0 ≤ ω^2 := sq_nonneg ω
  have hu : ω^2/(1+ω^2) ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith)
  have hh := hv _ hu
  rw [compactification _ _ _ _ ht] at hh
  exact (div_pos_iff_of_pos_right (by positivity)).mp hh

end
end SPR.Polytope.CubicSynthesis
