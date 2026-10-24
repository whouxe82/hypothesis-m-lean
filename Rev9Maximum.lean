import Rev9Residues
import Mathlib.Data.Finset.Max

/-! First exit and cumulative maximum, defined from the frozen exit predicate. -/
namespace HypMRev9
open HypothesisMTarget

theorem exit_exists (n : ℕ) (hn : 2 ≤ n) : ∃ B, CoefficientExitWithin n B :=
  ⟨_, HypothesisMAssembly.hypothesis_M n hn⟩

/-- First exit for the seeds in the paper; zero is only a totalization at n<2. -/
noncomputable def sigma (n : ℕ) : ℕ := by
  classical
  exact if hn : 2 ≤ n then Nat.find (exit_exists n hn) else 0

theorem sigma_spec (n : ℕ) (hn : 2 ≤ n) : CoefficientExitWithin n (sigma n) := by
  classical
  simp only [sigma, dif_pos hn]
  exact Nat.find_spec (exit_exists n hn)

theorem sigma_le_iff (n B : ℕ) (hn : 2 ≤ n) :
    sigma n ≤ B ↔ CoefficientExitWithin n B := by
  classical
  constructor
  · intro h; exact exit_mono (sigma_spec n hn) h
  · intro h
    simp only [sigma, dif_pos hn]
    exact Nat.find_min' (exit_exists n hn) h

theorem sigma_pos (n : ℕ) (hn : 2 ≤ n) : 0 < sigma n := by
  obtain ⟨j, hj, hB, _⟩ := sigma_spec n hn
  omega

theorem sigma_gt_iff_mod (n L : ℕ) (hn : 2 ≤ n) :
    L < sigma n ↔ n % 2^L = residue L := by
  rw [← no_exit_iff_mod, ← sigma_le_iff n L hn]
  omega

def seeds (k : ℕ) : Finset ℕ := (Finset.range (2^k)).filter (2 ≤ ·)

theorem mem_seeds (k n : ℕ) : n ∈ seeds k ↔ 2 ≤ n ∧ n < 2^k := by
  simp only [seeds, Finset.mem_filter, Finset.mem_range]
  tauto

/-- Cumulative maximum M(k), over every seed of at most k binary digits. -/
noncomputable def maximumExit (k : ℕ) : ℕ := (seeds k).sup sigma

theorem sigma_le_maximum (k n : ℕ) (hn : 2 ≤ n) (hk : n < 2^k) :
    sigma n ≤ maximumExit k :=
  Finset.le_sup (f := sigma) ((mem_seeds k n).2 ⟨hn, hk⟩)

theorem maximum_le_iff (k B : ℕ) : maximumExit k ≤ B ↔
    ∀ n, 2 ≤ n → n < 2^k → CoefficientExitWithin n B := by
  simp only [maximumExit, Finset.sup_le_iff]
  constructor
  · intro h n hn hk
    exact (sigma_le_iff n B hn).1 (h n ((mem_seeds k n).2 ⟨hn,hk⟩))
  · intro h n hn
    obtain ⟨hn,hk⟩ := (mem_seeds k n).1 hn
    exact (sigma_le_iff n B hn).2 (h n hn hk)

theorem maximum_upper (k : ℕ) : maximumExit k ≤ 2*k := by
  apply (maximum_le_iff k (2*k)).2
  exact HypMRev8Bridge.n2_upper_frozen k

theorem maximum_lower (k : ℕ) (hk : 2 ≤ k) : k+1 ≤ maximumExit k := by
  obtain ⟨n,hn,hnk,hno⟩ := HypMRev8Bridge.n2_lower_frozen k hk
  have hgt : k < sigma n := by
    by_contra hh
    exact hno ((sigma_le_iff n k hn).1 (by omega))
  have := sigma_le_maximum k n hn hnk
  omega

/-- Literal set S_k from Corollary N2; the next lemma gives its finite cutoff. -/
def residueDepths (k : ℕ) : Set ℕ := {L | 2 ≤ L ∧ residue L < 2^k}

theorem residueDepth_lt_twice (k L : ℕ) (h : L ∈ residueDepths k) : L < 2*k := by
  obtain ⟨hL,hres⟩ := h
  have hs := corollary2_residue L hL
  have hsq : residue L * residue L < 2^(2*k) := by
    have := Nat.mul_lt_mul_of_lt_of_lt hres hres
    simpa [← Nat.pow_add, show k+k=2*k by omega] using this
  by_contra hh
  have hp : 2^(2*k) ≤ 2^L := Nat.pow_le_pow_right (by decide) (by omega)
  omega

noncomputable def depthFinset (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2*k)).filter (fun L => 2 ≤ L ∧ residue L < 2^k)

theorem mem_depthFinset (k L : ℕ) : L ∈ depthFinset k ↔ L ∈ residueDepths k := by
  classical
  simp only [depthFinset, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨residueDepth_lt_twice k L h,h⟩⟩

theorem residueDepths_finite (k : ℕ) : (residueDepths k).Finite := by
  have he : residueDepths k = (depthFinset k : Set ℕ) := by
    ext L; exact (mem_depthFinset k L).symm
  rw [he]; exact Finset.finite_toSet _

theorem k_mem_depthFinset (k : ℕ) (hk : 2 ≤ k) : k ∈ depthFinset k :=
  (mem_depthFinset k k).2 ⟨hk,residue_lt k⟩

theorem residueDepths_nonempty (k : ℕ) (hk : 2 ≤ k) : (residueDepths k).Nonempty :=
  ⟨k,hk,residue_lt k⟩

/-- Maximum element of S_k, with zero only for an empty set at k<2. -/
noncomputable def maxDepth (k : ℕ) : ℕ := (depthFinset k).sup id

theorem maxDepth_mem (k : ℕ) (hk : 2 ≤ k) : maxDepth k ∈ depthFinset k := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup (depthFinset k)
    ⟨k,k_mem_depthFinset k hk⟩ id
  change (depthFinset k).sup id ∈ depthFinset k
  rw [he]
  exact hi

theorem depth_le_maxDepth (k L : ℕ) (h : L ∈ residueDepths k) : L ≤ maxDepth k :=
  Finset.le_sup (f := id) ((mem_depthFinset k L).2 h)

/-- Corollary N2, exact identity for the literal set S_k. -/
theorem corollaryN2_identity (k : ℕ) (hk : 2 ≤ k) :
    maximumExit k = 1 + maxDepth k := by
  have hmem := (mem_depthFinset k (maxDepth k)).1 (maxDepth_mem k hk)
  obtain ⟨hD,hres⟩ := hmem
  have hn := residue_ge_two (maxDepth k) hD
  have hlo : maxDepth k < sigma (residue (maxDepth k)) := by
    apply (sigma_gt_iff_mod _ _ hn).2
    exact Nat.mod_eq_of_lt (residue_lt (maxDepth k))
  have hmax := sigma_le_maximum k (residue (maxDepth k)) hn hres
  apply Nat.le_antisymm
  · unfold maximumExit
    apply Finset.sup_le
    intro n hnmem
    obtain ⟨hn,hnk⟩ := (mem_seeds k n).1 hnmem
    by_contra h
    have hs : maxDepth k + 1 < sigma n := by omega
    have he := (sigma_gt_iff_mod n (maxDepth k + 1) hn).1 hs
    have hr : residue (maxDepth k+1) < 2^k := by
      rw [← he]
      exact (Nat.mod_le _ _).trans_lt hnk
    have := depth_le_maxDepth k (maxDepth k+1) ⟨by omega,hr⟩
    omega
  · omega

#check corollaryN2_identity
#print axioms corollaryN2_identity
#check residueDepths_finite
#print axioms residueDepths_finite
#check residueDepths_nonempty
#print axioms residueDepths_nonempty
#check maximum_lower
#print axioms maximum_lower
#check maximum_upper
#print axioms maximum_upper
end HypMRev9
