import Rev9ExactBits

/-!
An auxiliary reduction for items 3 and 9, NOT a completed formalization of
Theorem 4 or Lemma 11. The explicit period hypothesis still has to be proved
for the paper's consecutive continued-fraction denominators. This file proves
the orbit/congruence/size/balanced-cycle argument once that hypothesis is given.
It does not invoke Theorem 1 in the period-to-exit theorem.
-/
namespace HypMRev9
open HypothesisMTarget HypothesisMCritical HypothesisMOrbit HypothesisMAffine
open HypothesisMCycleAdapter HypothesisMAssembly HypothesisMMinimal

/-- One-based critical letter, expressed by the exact integer count increment. -/
def criticalLetter (t : ℕ) : ℕ := N1.c t-N1.c (t-1)

theorem parity_eq_criticalLetter (n L t : ℕ)
    (hno : ¬ CoefficientExitWithin n L) (ht : t < L) :
    orbit n t % 2 = criticalLetter (t+1) := by
  have h0 := (no_exit_iff_counts n L).1 hno t (by omega)
  have h1 := (no_exit_iff_counts n L).1 hno (t+1) (by omega)
  simp only [oddCount] at h1
  unfold criticalLetter
  rw [Nat.add_sub_cancel]
  have hm := Nat.mod_lt (orbit n t) (by decide : 0<2)
  split_ifs at h1 <;> omega

theorem confined_state_upper (n L t : ℕ)
    (hno : ¬ CoefficientExitWithin n L) (ht : t ≤ L) : orbit n t ≤ 3*n+t := by
  have hc := coefficient_bounds_of_no_exit n L hno t ht
  obtain ⟨e,he0,het,heq⟩ := affine_error_bounds n t
    (fun s hs => (coefficient_bounds_of_no_exit n L hno s (hs.trans ht)).1) hc.2.le
  have hn : (0 : ℚ) ≤ n := by positivity
  have hr : (orbit n t : ℚ) ≤ 3*(n : ℚ)+(t : ℚ) := by nlinarith
  exact_mod_cast hr

/-- The arithmetic and dynamical part of Theorem 4, with its unproved
continued-fraction period input displayed as a hypothesis. -/
theorem period_implies_exit (q k n : ℕ) (hq : 0<q) (hk : q+4 ≤ k)
    (hn : 2 ≤ n) (hnk : n < 2^k)
    (hperiod : ∀ t, 2 ≤ t → t ≤ k+3 → criticalLetter t = criticalLetter (t+q)) :
    CoefficientExitWithin n (k+q+3) := by
  by_contra hno
  have hpar : ∀ t < k+2, orbit n (1+t) % 2 = orbit n (1+q+t) % 2 := by
    intro t ht
    rw [parity_eq_criticalLetter n (k+q+3) (1+t) hno (by omega),
      parity_eq_criticalLetter n (k+q+3) (1+q+t) hno (by omega)]
    have hp := hperiod (t+2) (by omega) (by omega)
    simpa only [show 1+t+1=t+2 by omega,show 1+q+t+1=t+2+q by omega] using hp
  have hsize1 := confined_state_upper n (k+q+3) 1 hno (by omega)
  have hsizeq := confined_state_upper n (k+q+3) (1+q) hno (by omega)
  have hkpow : k < 2^k := Nat.lt_two_pow_self
  have hp : 2^(k+2) = 4*2^k := by ring
  have hu1 : orbit n 1 < 2^(k+2) := by rw [hp]; omega
  have huq : orbit n (1+q) < 2^(k+2) := by rw [hp]; omega
  have hc : |(orbit n 1 : ℤ)-(orbit n (1+q) : ℤ)| < (2 : ℤ)^(k+2) := by
    have h1 : (orbit n 1 : ℤ) < (2 : ℤ)^(k+2) := by exact_mod_cast hu1
    have h2 : (orbit n (1+q) : ℤ) < (2 : ℤ)^(k+2) := by exact_mod_cast huq
    rw [abs_lt]; constructor <;> omega
  have heq := collision_of_close n 1 (1+q) (k+2) hpar hc
  have hret : orbit (orbit n 1) q = orbit n 1 := by
    have h := return_of_collision n 1 (1+q) (by omega) heq
    simpa only [Nat.add_sub_cancel_left] using h
  obtain ⟨d,hd,hdq,hretD,hmin⟩ := exists_least_return (orbit n 1) q hq hret
  letI : NeZero d := ⟨by omega⟩
  have hbal := returned_orbit_cyclically_balanced n (k+q+3) 1 d hno (by omega) hretD
  have hgrow : n < orbit n 1 := orbit_gt_seed n 1 (by omega) (by omega)
    (fun s hs => (coefficient_bounds_of_no_exit n (k+q+3) hno s (by omega)).1)
    (coefficient_bounds_of_no_exit n (k+q+3) hno 1 (by omega)).2.le
  have hd2 := balanced_minimal_return_period_two (orbit n 1) d (by omega) hd hretD hmin hbal
  have htriv := period_two_states (orbit n 1) (by omega) (by simpa only [hd2] using hretD)
  omega

/-- Cumulative version of the preceding auxiliary reduction. This is not
labelled Corollary N4 until the period input has been proved for convergents. -/
theorem period_implies_maximum_bound (q k : ℕ) (hq : 0<q) (hk : q+4 ≤ k)
    (hperiod : ∀ t, 2 ≤ t → t ≤ k+3 → criticalLetter t = criticalLetter (t+q)) :
    maximumExit k ≤ k+q+3 := by
  apply (maximum_le_iff k _).2
  intro n hn hnk
  exact period_implies_exit q k n hq hk hn hnk hperiod

#check period_implies_exit
#print axioms period_implies_exit
#check period_implies_maximum_bound
#print axioms period_implies_maximum_bound
end HypMRev9
