import Rev9FourRate
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Auxiliary arithmetic for N5, not a completed proof of N5. This module does not
assert that the actual continued-fraction denominators satisfy the displayed
premises. Connecting those denominators, their infinitely many partial
quotients at least two, and the period/window theorem remains outstanding.
-/
namespace HypMRev9Ratio

theorem sqrt_two_properties : 1 < Real.sqrt 2 ∧ (Real.sqrt 2)^2=2 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)
  · exact Real.sq_sqrt (by norm_num)

/-- At a recurrence step with coefficient at least two, one of the two
adjacent denominator ratios is already at least 1+sqrt(2). -/
theorem adjacent_large_ratio (a b c : ℕ) (h : 2*b+a ≤ c) :
    (1+Real.sqrt 2)*(a : ℝ) ≤ b ∨ (1+Real.sqrt 2)*(b : ℝ) ≤ c := by
  obtain ⟨hs,hsq⟩ := sqrt_two_properties
  by_cases hab : (1+Real.sqrt 2)*(a : ℝ) ≤ b
  · exact Or.inl hab
  · right
    have hR : (0 : ℝ) < 1+Real.sqrt 2 := by positivity
    have hinv : (1+Real.sqrt 2)*(Real.sqrt 2-1)=1 := by nlinarith
    have hab' : (b : ℝ) ≤ (1+Real.sqrt 2)*(a : ℝ) := le_of_lt (lt_of_not_ge hab)
    have hmul : (Real.sqrt 2-1)*(b : ℝ) ≤ a := by
      apply (mul_le_mul_iff_right₀ hR).1
      calc
        (1+Real.sqrt 2)*((Real.sqrt 2-1)*(b : ℝ)) =
            ((1+Real.sqrt 2)*(Real.sqrt 2-1))*(b : ℝ) := by ring
        _ = b := by rw [hinv,one_mul]
        _ ≤ (1+Real.sqrt 2)*(a : ℝ) := hab'
    have hc : (2 : ℝ)*b+a ≤ c := by exact_mod_cast h
    nlinarith

/-- This is the recurrence consequence of infinitely many partial quotients
at least two. No Gelfond–Schneider theorem is postulated as an axiom. -/
theorem arbitrarily_large_ratio_indices (q : ℕ → ℕ)
    (hrec : ∀ N, ∃ m, N ≤ m ∧ 2*q (m+1)+q m ≤ q (m+2)) :
    ∀ N, ∃ m, N ≤ m ∧ (1+Real.sqrt 2)*(q m : ℝ) ≤ q (m+1) := by
  intro N
  obtain ⟨m,hm,hr⟩ := hrec N
  rcases adjacent_large_ratio (q m) (q (m+1)) (q (m+2)) hr with h | h
  · exact ⟨m,hm,h⟩
  · refine ⟨m+1,by omega,?_⟩
    simpa only [show m+1+1=m+2 by omega] using h

/-- Finite arithmetic of the N5 cutoff. A proved N4 bound at k=Q-4 and a
large denominator ratio yield sqrt(2)+7/k, with a harmless explicit error. -/
theorem window_sqrt_two_bound (q Q k A : ℕ)
    (hk : 0<k) (hcut : Q=k+4) (hA : A ≤ k+q+3)
    (hratio : (1+Real.sqrt 2)*(q : ℝ) ≤ Q) :
    (A : ℝ)/(k : ℝ) ≤ Real.sqrt 2+7/(k : ℝ) := by
  obtain ⟨hs,hsq⟩ := sqrt_two_properties
  have hR : (0 : ℝ) < 1+Real.sqrt 2 := by positivity
  have hinv : (1+Real.sqrt 2)*(Real.sqrt 2-1)=1 := by nlinarith
  have hq : (q : ℝ) ≤ (Real.sqrt 2-1)*(Q : ℝ) := by
    apply (mul_le_mul_iff_right₀ hR).1
    calc
      (1+Real.sqrt 2)*(q : ℝ) ≤ Q := hratio
      _ = (1+Real.sqrt 2)*((Real.sqrt 2-1)*(Q : ℝ)) := by rw [← mul_assoc,hinv,one_mul]
  have hc : (Q : ℝ)=(k : ℝ)+4 := by exact_mod_cast hcut
  have hAR : (A : ℝ) ≤ (k : ℝ)+(q : ℝ)+3 := by exact_mod_cast hA
  have hkr : (0 : ℝ)<k := by exact_mod_cast hk
  have hs2 : Real.sqrt 2 < 2 := by nlinarith
  apply (div_le_iff₀ hkr).2
  rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hkr)]
  nlinarith

#check adjacent_large_ratio
#print axioms adjacent_large_ratio
#check arbitrarily_large_ratio_indices
#print axioms arbitrarily_large_ratio_indices
#check window_sqrt_two_bound
#print axioms window_sqrt_two_bound
end HypMRev9Ratio
