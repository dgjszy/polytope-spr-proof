import SPR.Polytope.Common.Definitions

/-! # Boundary sign changes and simultaneous complex orthogonality.

These are the local steps in the high-order limit argument. No weak-existence
or compactness conclusion is assumed or claimed by these local statements.
-/
namespace SPR.Polytope
open Complex Set

/-- A continuous real factor paired nonnegatively with T-t must vanish at T>0. -/
theorem zero_of_boundary_sign {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 < T)
    (h : ∀ t, 0 ≤ t → 0 ≤ (T-t)*f t) : f T=0 := by
  have hcpos : IsClosed {t : ℝ | 0 ≤ f t} := isClosed_le continuous_const hf
  have hcneg : IsClosed {t : ℝ | f t ≤ 0} := isClosed_le hf continuous_const
  have hleft : Ioo 0 T ⊆ {t : ℝ | 0 ≤ f t} := by
    intro t ht
    by_contra hn
    exact (not_lt_of_ge (h t ht.1.le))
      (mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) (lt_of_not_ge hn))
  have hright : Ioi T ⊆ {t : ℝ | f t ≤ 0} := by
    intro t ht
    have hh := h t (hT.le.trans ht.le)
    by_contra hn
    exact (not_lt_of_ge hh) (mul_neg_of_neg_of_pos (sub_neg.mpr ht) (lt_of_not_ge hn))
  have hp := (hcpos.closure_subset_iff.mpr hleft)
    (show T ∈ closure (Ioo 0 T) by rw [closure_Ioo hT.ne]; exact ⟨hT.le,le_rfl⟩)
  have hn := (hcneg.closure_subset_iff.mpr hright)
    (show T ∈ closure (Ioi T) by rw [closure_Ioi]; exact (le_rfl : T ≤ T))
  exact le_antisymm hn hp

/-- A nonzero determinant of two complex values excludes a nonzero simultaneous
orthogonal value, viewing complex numbers as real two-dimensional vectors. -/
theorem zero_of_two_orthogonal {z a b : ℂ}
    (hdet : a.re*b.im-a.im*b.re ≠ 0)
    (ha : (z*star a).re=0) (hb : (z*star b).re=0) : z=0 := by
  have h1 : z.re*a.re+z.im*a.im=0 := by simpa [Complex.mul_re] using ha
  have h2 : z.re*b.re+z.im*b.im=0 := by simpa [Complex.mul_re] using hb
  have hr : z.re*(a.re*b.im-a.im*b.re)=0 := by
    linear_combination b.im*h1-a.im*h2
  have hi : z.im*(a.re*b.im-a.im*b.re)=0 := by
    linear_combination a.re*h2-b.re*h1
  apply Complex.ext
  · simpa using (mul_eq_zero.mp hr).resolve_right hdet
  · simpa using (mul_eq_zero.mp hi).resolve_right hdet

end SPR.Polytope
