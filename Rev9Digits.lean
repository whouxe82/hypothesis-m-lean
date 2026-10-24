import Rev9Maximum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Binary digits of the compatible canonical residue system and Corollary N3. -/
namespace HypMRev9
open HypothesisMTarget
open scoped BigOperators

/-- Digit i of the 2-adic integer determined by the canonical critical residues. -/
noncomputable def digit (i : ℕ) : ℕ :=
  if residue (i+1) = residue i then 0 else 1

theorem digit_zero_iff (i : ℕ) : digit i = 0 ↔ residue (i+1) = residue i := by
  simp [digit]

theorem digit_binary (i : ℕ) : digit i = 0 ∨ digit i = 1 := by
  unfold digit; split <;> simp

theorem residue_step_digit (i : ℕ) :
    residue (i+1) = residue i + digit i * 2^i := by
  rcases residue_step i with h | h
  · simp [digit,h]
  · have hn : residue (i+1) ≠ residue i := by
      have hp : 0 < 2^i := by positivity
      omega
    simp [digit,hn,h]

theorem residue_zero : residue 0 = 0 := by
  have := residue_lt 0
  norm_num at this
  omega

/-- The digits are proved to be the literal binary expansion of every residue. -/
theorem residue_binary_expansion (L : ℕ) :
    residue L = ∑ i ∈ Finset.range L, digit i * 2^i := by
  induction L with
  | zero => simp [residue_zero]
  | succ L ih => rw [Finset.sum_range_succ, residue_step_digit, ih]

theorem zero_block_iff (k L : ℕ) (hkL : k ≤ L) :
    (∀ i, k ≤ i → i < L → digit i = 0) ↔ residue L = residue k := by
  constructor
  · intro h
    have hg : ∀ j, k ≤ j → j ≤ L → residue j = residue k := by
      intro j hkj
      induction j, hkj using Nat.le_induction with
      | base => intro _; rfl
      | succ j hkj ih =>
        intro hjL
        rw [residue_step_digit, h j hkj (by omega), zero_mul, add_zero]
        exact ih (by omega)
    exact hg L hkL le_rfl
  · intro he i hki hiL
    apply (digit_zero_iff i).2
    have h1 := residue_mono hki
    have h2 := residue_mono (show i ≤ i+1 by omega)
    have h3 := residue_mono (show i+1 ≤ L by omega)
    omega

theorem residue_small_iff_zero_block (k L : ℕ) (hkL : k ≤ L) :
    residue L < 2^k ↔ ∀ i, k ≤ i → i < L → digit i = 0 := by
  rw [zero_block_iff k L hkL]
  constructor
  · intro h
    have := residue_mod L k hkL
    simpa only [Nat.mod_eq_of_lt h] using this
  · intro h; rw [h]; exact residue_lt k

/-- Length of the zero run beginning at digit k. Its zero/one characterization
is proved below, so this definition is not merely a renamed exit-time bound. -/
noncomputable def zeroRun (k : ℕ) : ℕ := maxDepth k-k

theorem k_le_maxDepth (k : ℕ) (hk : 2 ≤ k) : k ≤ maxDepth k :=
  depth_le_maxDepth k k ⟨hk,residue_lt k⟩

theorem run_end (k : ℕ) (hk : 2 ≤ k) : k+zeroRun k = maxDepth k := by
  unfold zeroRun
  exact Nat.add_sub_of_le (k_le_maxDepth k hk)

/-- Exact semantics: every digit in the run is zero, and its next digit is one. -/
theorem zeroRun_spec (k : ℕ) (hk : 2 ≤ k) :
    (∀ i < zeroRun k, digit (k+i) = 0) ∧ digit (k+zeroRun k) = 1 := by
  have hD := (mem_depthFinset k (maxDepth k)).1 (maxDepth_mem k hk)
  have hDmin : 2 ≤ maxDepth k := hD.1
  have hb := (residue_small_iff_zero_block k (maxDepth k) (k_le_maxDepth k hk)).1 hD.2
  constructor
  · intro i hi
    apply hb (k+i) (by omega)
    have := run_end k hk
    omega
  · rw [run_end k hk]
    rcases digit_binary (maxDepth k) with h0 | h1
    · have he := (digit_zero_iff _).1 h0
      have hm : maxDepth k+1 ∈ residueDepths k := ⟨by omega,by simpa [he] using hD.2⟩
      have := depth_le_maxDepth k (maxDepth k+1) hm
      omega
    · exact h1

theorem zeroRun_unique (k z : ℕ) (hk : 2 ≤ k)
    (hz : ∀ i < z, digit (k+i) = 0) (hone : digit (k+z) = 1) : z = zeroRun k := by
  obtain ⟨hzero,hend⟩ := zeroRun_spec k hk
  rcases lt_trichotomy z (zeroRun k) with h | h | h
  · have := hzero z h; omega
  · exact h
  · have := hz (zeroRun k) h; omega

/-- Corollary N3, cumulative form. -/
theorem corollaryN3_identity (k : ℕ) (hk : 2 ≤ k) :
    maximumExit k = k+1+zeroRun k := by
  rw [corollaryN2_identity k hk, ← run_end k hk]
  omega

theorem corollaryN3_run_bound (k : ℕ) (hk : 2 ≤ k) : zeroRun k ≤ k-1 := by
  have hu := maximum_upper k
  rw [corollaryN3_identity k hk] at hu
  omega

#check residue_binary_expansion
#print axioms residue_binary_expansion
#check zeroRun_spec
#print axioms zeroRun_spec
#check corollaryN3_identity
#print axioms corollaryN3_identity
#check corollaryN3_run_bound
#print axioms corollaryN3_run_bound
end HypMRev9
