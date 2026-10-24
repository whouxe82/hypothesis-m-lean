import Rev9RealCount
import Rev9Residues

namespace HypMRev9Real
open HypothesisMTarget HypothesisMCritical

/-- The counted word predicate agrees with the actual frozen orbit's prefix
coefficients. The lower bound is in naturals and the real upper bound is exact. -/
theorem admissible_frozen_orbit (K : ℝ) (n L : ℕ) :
    Admissible K (orbitWord n 0 L) ↔
      ∀ j, 1 ≤ j → j ≤ L →
        2^j ≤ 3^(oddCount n j) ∧ (3 : ℝ)^(oddCount n j) ≤ K*(2 : ℝ)^j := by
  have hlen := HypothesisMWordAffine.orbitWord_length n 0 L
  have hc : ∀ j ≤ L, ((orbitWord n 0 L).take j).count true = oddCount n j := by
    intro j hj
    rw [orbitWord_take n 0 L j hj]
    have h := orbitWord_count_add n 0 j
    simpa only [Nat.zero_add,oddCount] using h.symm
  unfold Admissible
  rw [hlen]
  constructor <;> intro h j hj hjL
  · simpa only [hc j hjL] using h j hj hjL
  · rw [hc j hjL]; exact h j hj hjL

#check admissible_frozen_orbit
#print axioms admissible_frozen_orbit
end HypMRev9Real
