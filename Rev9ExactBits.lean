import Rev9Digits
import Mathlib.Order.Interval.Finset.Nat

namespace HypMRev9

def exactSeeds (b : ℕ) : Finset ℕ := Finset.Ico (2^(b-1)) (2^b)
noncomputable def exactMaximum (b : ℕ) : ℕ := (exactSeeds b).sup sigma

theorem exact_seed_ge_two (b n : ℕ) (hb : 2 ≤ b) (hn : n ∈ exactSeeds b) : 2 ≤ n := by
  have hn' : 2^(b-1) ≤ n ∧ n < 2^b := Finset.mem_Ico.1 hn
  have hp : 2^1 ≤ 2^(b-1) := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  omega

theorem exact_le_maximum (b : ℕ) (hb : 2 ≤ b) : exactMaximum b ≤ maximumExit b := by
  apply Finset.sup_le
  intro n hn
  have hn' : 2^(b-1) ≤ n ∧ n < 2^b := Finset.mem_Ico.1 hn
  exact sigma_le_maximum b n (exact_seed_ge_two b n hb hn) hn'.2

/-- Corollary N3, exact bit length, when the preceding digit is one. -/
theorem corollaryN3_exact_one (b : ℕ) (hb : 2 ≤ b) (hbit : digit (b-1) = 1) :
    exactMaximum b = b+1+zeroRun b := by
  have hD := (mem_depthFinset b (maxDepth b)).1 (maxDepth_mem b hb)
  have he := residue_step_digit (b-1)
  rw [show b-1+1=b by omega,hbit,one_mul] at he
  have hrlow : 2^(b-1) ≤ residue (maxDepth b) := by
    have hm := residue_mono (k_le_maxDepth b hb)
    omega
  have hmem : residue (maxDepth b) ∈ exactSeeds b := Finset.mem_Ico.2 ⟨hrlow,hD.2⟩
  have hn := exact_seed_ge_two b (residue (maxDepth b)) hb hmem
  have hgt : maxDepth b < sigma (residue (maxDepth b)) := by
    apply (sigma_gt_iff_mod _ _ hn).2
    exact Nat.mod_eq_of_lt (residue_lt _)
  have hle : sigma (residue (maxDepth b)) ≤ exactMaximum b := Finset.le_sup (f:=sigma) hmem
  have hu := exact_le_maximum b hb
  rw [corollaryN3_identity b hb] at hu
  have hend := run_end b hb
  omega

/-- Corollary N3, exact bit length, when the preceding digit is zero. -/
theorem corollaryN3_exact_zero (b : ℕ) (hb : 2 ≤ b) (hbit : digit (b-1) = 0) :
    exactMaximum b = b := by
  have he := (digit_zero_iff (b-1)).1 hbit
  rw [show b-1+1=b by omega] at he
  have hpow : 2^b = 2^(b-1)*2 := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ b by omega)]
    exact Nat.pow_succ _ _
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro n hn
    have hn' : 2^(b-1) ≤ n ∧ n < 2^b := Finset.mem_Ico.1 hn
    have hn2 := exact_seed_ge_two b n hb hn
    by_contra hh
    have hm := (sigma_gt_iff_mod n b hn2).1 (by omega)
    rw [Nat.mod_eq_of_lt hn'.2,he] at hm
    have hr := residue_lt (b-1)
    omega
  · let n := residue (b-1)+2^(b-1)
    have hr := residue_lt (b-1)
    have hmem : n ∈ exactSeeds b := by
      apply Finset.mem_Ico.2
      dsimp [n]
      constructor
      · exact Nat.le_add_left _ _
      · omega
    have hn2 := exact_seed_ge_two b n hb hmem
    have hm : n % 2^(b-1) = residue (b-1) := by
      dsimp [n]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    have hgt := (sigma_gt_iff_mod n (b-1) hn2).2 hm
    have hle : sigma n ≤ exactMaximum b := Finset.le_sup (f:=sigma) hmem
    omega

/-- The complete two-case exact-bit-length formula in a single statement. -/
theorem corollaryN3_exact (b : ℕ) (hb : 2 ≤ b) :
    exactMaximum b = if digit (b-1) = 1 then b+1+zeroRun b else b := by
  split_ifs with h
  · exact corollaryN3_exact_one b hb h
  · have h0 : digit (b-1) = 0 := by
      rcases digit_binary (b-1) with h0 | h1
      · exact h0
      · contradiction
    exact corollaryN3_exact_zero b hb h0

#check corollaryN3_exact
#print axioms corollaryN3_exact
#check corollaryN3_exact_one
#print axioms corollaryN3_exact_one
#check corollaryN3_exact_zero
#print axioms corollaryN3_exact_zero
end HypMRev9
