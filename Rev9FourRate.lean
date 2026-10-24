import Rev9CountFour
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace HypMRev9Four
open Filter
open scoped Topology

noncomputable def alpha : ℝ := Real.log 2 / Real.log 3

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
theorem alpha_pos : 0 < alpha := div_pos (Real.log_pos (by norm_num)) log_three_pos

theorem c_real_bounds (j : ℕ) :
    (j : ℝ)*alpha ≤ (N1.c j : ℝ) ∧ (N1.c j : ℝ) < (j : ℝ)*alpha+1 := by
  obtain ⟨hl,hu⟩ := N1.c_spec j
  have hlR : (2 : ℝ)^j ≤ (3 : ℝ)^(N1.c j) := by exact_mod_cast hl
  have huR : (3 : ℝ)^(N1.c j) < 3*(2 : ℝ)^j := by exact_mod_cast hu
  have hlogl := Real.log_le_log (by positivity : (0 : ℝ) < 2^j) hlR
  have hlogu := Real.log_lt_log (by positivity : (0 : ℝ) < 3^(N1.c j)) huR
  rw [Real.log_pow,Real.log_pow] at hlogl
  rw [Real.log_pow,Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity),Real.log_pow] at hlogu
  have ha : alpha * Real.log 3 = Real.log 2 := div_mul_cancel₀ _ (ne_of_gt log_three_pos)
  constructor <;> nlinarith [log_three_pos]

theorem c_real_strict (j : ℕ) (hj : 1 ≤ j) : (j : ℝ)*alpha < (N1.c j : ℝ) := by
  have hR : (2 : ℝ)^j < (3 : ℝ)^(N1.c j) := by exact_mod_cast N1.c_strict j hj
  have hh := Real.log_lt_log (by positivity : (0 : ℝ) < 2^j) hR
  rw [Real.log_pow,Real.log_pow] at hh
  have ha : alpha * Real.log 3 = Real.log 2 := div_mul_cancel₀ _ (ne_of_gt log_three_pos)
  nlinarith [log_three_pos]

/-- The integer comparison definition agrees with the paper's real floor. -/
theorem floorCount_eq_floor (j : ℕ) : floorCount j = ⌊(j : ℝ)*alpha⌋₊ := by
  by_cases hj : j=0
  · subst j; norm_num [floorCount,N1.c]
  have hc := c_positive j (by omega)
  have he : floorCount j+1=N1.c j := by unfold floorCount; omega
  have heR : (floorCount j : ℝ)+1=N1.c j := by exact_mod_cast he
  have hbounds := c_real_bounds j
  have hstrict := c_real_strict j (by omega)
  have ha := alpha_pos
  symm
  apply (Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ (j : ℝ)*alpha)).2
  constructor <;> linarith

theorem four_exponent (L : ℕ) :
    floorCount (L+1)+floorCount (L+2)-L-1 = N1.B 4 1 L := by
  have ht := choices_four_telescopes L
  have hc1 := c_positive (L+1) (by omega)
  have hc2 := c_positive (L+2) (by omega)
  unfold floorCount
  omega

theorem log_count_four (L : ℕ) :
    Real.log (HypMRev9Real.count 4 L : ℝ) / Real.log 2 = (N1.B 4 1 L : ℝ) := by
  rw [proposition14_exact,four_exponent]
  push_cast
  rw [Real.log_pow]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2)))

/-- Proposition 14, with exactly the real-floor exponents used in the paper. -/
theorem proposition14_real_formula (L : ℕ) :
    HypMRev9Real.count 4 L =
      2^(⌊((L+1 : ℕ) : ℝ)*alpha⌋₊+⌊((L+2 : ℕ) : ℝ)*alpha⌋₊-L-1) := by
  simpa only [floorCount_eq_floor] using proposition14_exact L

/-- Proposition 14, asymptotic growth rate, in the standard real logarithm form. -/
theorem proposition14_rate :
    Tendsto (fun L : ℕ => Real.log (HypMRev9Real.count 4 L : ℝ) / Real.log 2 / (L : ℝ))
      atTop (𝓝 (2*alpha-1)) := by
  have hlow : Tendsto (fun L : ℕ => (2*alpha-1)+(3*alpha-3)/(L : ℝ))
      atTop (𝓝 (2*alpha-1)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (3*alpha-3))
  have hhigh : Tendsto (fun L : ℕ => (2*alpha-1)+(3*alpha-1)/(L : ℝ))
      atTop (𝓝 (2*alpha-1)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (3*alpha-1))
  have hbound : ∀ᶠ L : ℕ in atTop,
      (2*alpha-1)+(3*alpha-3)/(L : ℝ) ≤ (N1.B 4 1 L : ℝ)/(L : ℝ) ∧
      (N1.B 4 1 L : ℝ)/(L : ℝ) ≤ (2*alpha-1)+(3*alpha-1)/(L : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0<L by omega)
    have h1 := c_real_bounds (L+1)
    have h2 := c_real_bounds (L+2)
    have ht : (N1.B 4 1 L : ℝ)+(L : ℝ)+3 = (N1.c (L+1) : ℝ)+(N1.c (L+2) : ℝ) := by
      exact_mod_cast choices_four_telescopes L
    push_cast at h1 h2
    constructor
    · apply (le_div_iff₀ hLp).2
      rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hLp)]
      nlinarith
    · apply (div_le_iff₀ hLp).2
      rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hLp)]
      nlinarith
  have ht := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
  simpa only [log_count_four] using ht

#check floorCount_eq_floor
#print axioms floorCount_eq_floor
#check proposition14_rate
#print axioms proposition14_rate
#check proposition14_real_formula
#print axioms proposition14_real_formula
end HypMRev9Four
