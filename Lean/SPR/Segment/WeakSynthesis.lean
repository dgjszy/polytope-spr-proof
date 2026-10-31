import SPR.Segment.OddCross
import SPR.Segment.CrossingRatios
import SPR.Segment.CrossingProduct
import SPR.Segment.FiniteInterpolation

/-!
# A common nonzero weakly positive numerator of smaller degree

Positive-ratio interpolation at zero and the positive odd crossings makes the
simple crossing product divide the interpolation numerator. Exact polynomial
cancellation recovers both nonnegative pairings. Its degree is strictly below
the common denominator degree.
-/

namespace SPR.Segment

open Polynomial Complex Finset

noncomputable section

/-- Distinct stable monic endpoints admit a nonzero strictly proper numerator
with nonnegative real pairings on the entire imaginary axis. -/
theorem weak_synthesis {p₀ p₁ : ℝ[X]} (hm₀ : p₀.Monic) (hm₁ : p₁.Monic)
    (hd : p₀.natDegree = p₁.natDegree) (_hn : 1 ≤ p₀.natDegree)
    (hs : Stable p₀ p₁) (hne : p₀ ≠ p₁) :
    ∃ c : ℝ[X], c ≠ 0 ∧ c.natDegree < p₀.natDegree ∧
      (∀ ω : ℝ, 0 ≤ pairing p₀ c ω) ∧ (∀ ω : ℝ, 0 ≤ pairing p₁ c ω) := by
  have hDne := cross_ne_zero hs.left hs.right hm₀ hm₁ hd hne
  obtain ⟨d, hD⟩ := odd_frequency_representation (reflect_cross p₀ p₁)
  have hdne : d ≠ 0 := by intro he; simp [he, frequencyLift] at hD; exact hDne hD
  obtain ⟨κ, Q, hκ, hQ, hQpos, hfactor⟩ := Algebra.nonnegative_remainder hdne
  let J := Algebra.positiveOddRoots d
  have hJ : ∀ t ∈ J, 0 < t := fun _ ht => Algebra.positiveOddRoots_pos ht
  have hcross (t : ℝ) (ht : t ∈ insert 0 J) :
      value (cross p₀ p₁) (I * (Real.sqrt t : ℂ)) = 0 := by
    rw [hD, value_mul, value_frequencyLift]
    rcases mem_insert.mp ht with he | ht
    · subst t
      simp [value]
    · have hr : d.eval t = 0 := by
        exact (mem_roots hdne).mp (Multiset.mem_toFinset.mp (mem_filter.mp ht).1)
      rw [Real.sq_sqrt (hJ t ht).le, hr, ofReal_zero, mul_zero]
  obtain ⟨u₀, u₁, hu₀deg, hu₁deg, hu₀pos, hu₁pos, huinterp⟩ :=
    Interpolation.finite_positive_ratio_interpolation J hJ (crossingRatio p₀ p₁)
      (fun t ht => crossing_ratio_positive hs (hcross t ht))
  let N : ℝ[X] := C 2 * (frequencyLift u₀ * p₁ - frequencyLift u₁ * p₀)
  have hNroot (t : ℝ) (ht : t ∈ insert 0 J) :
      value N (I * (Real.sqrt t : ℂ)) = 0 := by
    have htpos : 0 ≤ t := by
      rcases mem_insert.mp ht with he | hh
      · exact he ▸ le_rfl
      · exact (hJ t hh).le
    have hcol := crossing_ratio_collinear hs (hcross t ht)
    change value p₁ (I * (Real.sqrt t : ℂ)) =
      (crossingRatio p₀ p₁ t : ℂ) * value p₀ (I * (Real.sqrt t : ℂ)) at hcol
    have heval (p : ℝ[X]) : value (frequencyLift p) (I * (Real.sqrt t : ℂ)) =
        Complex.ofReal (p.eval t) := by
      rw [value_frequencyLift, Real.sq_sqrt htpos]
    simp only [N, value_mul, value_sub, value_C]
    rw [heval, heval, huinterp t ht, hcol, ofReal_mul]
    ring
  have hNzero : N.eval 0 = 0 := by
    have hh := hNroot 0 (mem_insert_self _ _)
    have he : value N 0 = Complex.ofReal (N.eval 0) := Polynomial.aeval_ofReal (K := ℂ) N 0
    simp only [Real.sqrt_zero, ofReal_zero, mul_zero] at hh
    rw [he] at hh
    exact_mod_cast hh
  obtain ⟨v, hv⟩ := crossing_product_dvd hJ hNzero
    (fun t ht => hNroot t (mem_insert_of_mem ht))
  change N = crossingProduct J * v at hv
  let σ : ℝ := (-1) ^ J.card
  let c := C (σ / κ) * v
  have hσ : σ ≠ 0 := pow_ne_zero _ (by norm_num)
  have hquot : cross p₀ p₁ * c =
      C 2 * (frequencyLift (Q * u₀) * p₁ - frequencyLift (Q * u₁) * p₀) := by
    have hKlift : X * frequencyLift (Algebra.oddRootProduct d) = C σ * crossingProduct J :=
      lift_oddRootProduct d
    have hκσ : κ * (σ * (σ / κ)) = 1 := by
      have hsq : σ * σ = 1 := by
        dsimp [σ]
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      field_simp
      nlinarith [hsq]
    have hDfactor : cross p₀ p₁ = C κ * frequencyLift Q *
        (X * frequencyLift (Algebra.oddRootProduct d)) := by
      calc
        _ = X * frequencyLift d := hD
        _ = X * frequencyLift (C κ * Q * Algebra.oddRootProduct d) :=
          congrArg (fun e => X * frequencyLift e) hfactor
        _ = _ := by simp only [frequencyLift, mul_comp, C_comp]; ring
    rw [hDfactor, hKlift]
    calc
      _ = C (κ * (σ * (σ / κ))) * frequencyLift Q * (crossingProduct J * v) := by
        simp only [c, map_mul]; ring
      _ = frequencyLift Q * N := by rw [hκσ, C_1, one_mul, ← hv]
      _ = _ := by simp only [N, frequencyLift, mul_comp]; ring
  have hleft := elimination_left hDne hquot
  have hright := elimination_right hDne hquot
  have hu₀ne : u₀ ≠ 0 := by intro he; simpa [he] using hu₀pos 0 le_rfl
  have hcne : c ≠ 0 := numerator_ne_zero_of_identity
    (frequencyLift_ne_zero (mul_ne_zero hQ hu₀ne)) hleft
  have hvne : v ≠ 0 := by intro he; apply hcne; simp [c, he]
  have hNdeg : N.natDegree ≤ 2 * J.card + p₀.natDegree := by
    have h₀ : (frequencyLift u₀ * p₁).natDegree ≤ 2 * J.card + p₀.natDegree := by
      apply natDegree_mul_le.trans
      rw [frequencyLift_degree, ← hd]
      omega
    have h₁ : (frequencyLift u₁ * p₀).natDegree ≤ 2 * J.card + p₀.natDegree := by
      apply natDegree_mul_le.trans
      rw [frequencyLift_degree]
      omega
    have hsub := (natDegree_sub_le (frequencyLift u₀ * p₁)
      (frequencyLift u₁ * p₀)).trans (max_le h₀ h₁)
    have hsc := natDegree_mul_le (p := C (2 : ℝ))
      (q := frequencyLift u₀ * p₁ - frequencyLift u₁ * p₀)
    simp only [natDegree_C, zero_add] at hsc
    exact hsc.trans hsub
  have hvdeg : v.natDegree < p₀.natDegree := by
    have hmul := natDegree_mul (crossingProduct_monic J).ne_zero hvne
    rw [← hv, crossingProduct_degree] at hmul
    omega
  have hcdeg : c.natDegree < p₀.natDegree := by
    have hle := natDegree_mul_le (p := C (σ / κ)) (q := v)
    simp only [natDegree_C, zero_add] at hle
    exact hle.trans_lt hvdeg
  refine ⟨c, hcne, hcdeg, ?_, ?_⟩
  · intro ω
    rw [pairing_of_identity hleft, eval_mul]
    exact mul_nonneg (hQpos _ (sq_nonneg ω)) (hu₀pos _ (sq_nonneg ω)).le
  · intro ω
    rw [pairing_of_identity hright, eval_mul]
    exact mul_nonneg (hQpos _ (sq_nonneg ω)) (hu₁pos _ (sq_nonneg ω)).le

end
end SPR.Segment
