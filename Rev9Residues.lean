import Rev8Bridge
import N1
import Mathlib.Data.Nat.ModEq

/-!
Revision 9: canonical residues and Corollary 2, using the frozen natural-number
orbit and exit predicate. Critical counts use exact comparisons of powers.
No real logarithm or numerical approximation is used in this module.
-/
namespace HypMRev9
open HypothesisMTarget

theorem exit_mono {n B C : ℕ} (h : CoefficientExitWithin n B) (hBC : B ≤ C) :
    CoefficientExitWithin n C := by
  obtain ⟨j, hj, hB, he⟩ := h
  exact ⟨j, hj, hB.trans hBC, he⟩

theorem crit_eq_c (j : ℕ) : HypMRev8.crit j = N1.c j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [HypMRev8.crit, HypMRev8.critBit, N1.c, ih]
    split_ifs <;> omega

/-- Exact forcing, expressed in the frozen odd-step counts. -/
theorem no_exit_iff_counts (n L : ℕ) :
    ¬ CoefficientExitWithin n L ↔ ∀ j ≤ L, oddCount n j = N1.c j := by
  constructor
  · intro h j hj
    by_cases hz : j = 0
    · subst j; rfl
    have hj1 : 1 ≤ j := by omega
    have hlo : 2^j ≤ 3^(oddCount n j) := by
      by_contra hh
      exact h ⟨j, hj1, hj, Or.inl (by omega)⟩
    have hhi : 3^(oddCount n j) ≤ 3 * 2^j := by
      by_contra hh
      exact h ⟨j, hj1, hj, Or.inr (by omega)⟩
    have hc := N1.c_le_of j (oddCount n j) hlo
    have hs := N1.c_strict j hj1
    by_contra he
    have hp : 3^(N1.c j + 1) ≤ 3^(oddCount n j) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    omega
  · intro h
    rintro ⟨j, hj, hjL, he⟩
    rw [h j hjL] at he
    have hs := N1.c_spec j
    omega

theorem residue_exists (L : ℕ) : ∃ n, n < 2^L ∧ ¬ CoefficientExitWithin n L := by
  obtain ⟨n, hn, hp⟩ := HypMRev8.lift
    (fun t => HypMRev8.critBit (HypMRev8.crit t) t)
    (fun t => by unfold HypMRev8.critBit; split <;> omega) L
  refine ⟨n, hn, (no_exit_iff_counts n L).2 ?_⟩
  intro j hj
  rw [← HypMRev8Bridge.oddCount_agree, HypMRev8.follow_counts n L hp j hj,
    crit_eq_c]

/-- The least nonnegative residue following the critical prefix of length L.
The uniqueness theorem below makes the choice independent of the witness. -/
noncomputable def residue (L : ℕ) : ℕ := Classical.choose (residue_exists L)

theorem residue_lt (L : ℕ) : residue L < 2^L :=
  (Classical.choose_spec (residue_exists L)).1

theorem residue_no_exit (L : ℕ) : ¬ CoefficientExitWithin (residue L) L :=
  (Classical.choose_spec (residue_exists L)).2

theorem same_counts_same_parities (n m L : ℕ)
    (h : ∀ j ≤ L, oddCount n j = oddCount m j) :
    ∀ t < L, orbit n t % 2 = orbit m t % 2 := by
  intro t ht
  have h0 := h t (by omega)
  have h1 := h (t+1) (by omega)
  simp only [oddCount] at h1
  have hn := Nat.mod_lt (orbit n t) (by decide : 0 < 2)
  have hm := Nat.mod_lt (orbit m t) (by decide : 0 < 2)
  split_ifs at h1 <;> omega

theorem no_exit_same_parities (n m L : ℕ)
    (hn : ¬ CoefficientExitWithin n L) (hm : ¬ CoefficientExitWithin m L) :
    ∀ t < L, orbit n t % 2 = orbit m t % 2 := by
  apply same_counts_same_parities
  intro j hj
  rw [(no_exit_iff_counts n L).1 hn j hj, (no_exit_iff_counts m L).1 hm j hj]

theorem no_exit_unique (L n m : ℕ) (hn : n < 2^L) (hm : m < 2^L)
    (hnc : ¬ CoefficientExitWithin n L) (hmc : ¬ CoefficientExitWithin m L) : n = m := by
  have hd := HypothesisMOrbit.same_parities_dvd L n m
    (no_exit_same_parities n m L hnc hmc)
  have hni : (n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hn
  have hmi : (m : ℤ) < (2 : ℤ)^L := by exact_mod_cast hm
  have hsmall : |(n : ℤ) - (m : ℤ)| < (2 : ℤ)^L := by
    rw [abs_lt]; constructor <;> omega
  have hz : (n : ℤ) - (m : ℤ) = 0 := by
    by_contra he
    have := Int.le_of_dvd (abs_pos.mpr he) ((dvd_abs _ _).mpr hd)
    omega
  exact_mod_cast sub_eq_zero.mp hz

theorem residue_two : residue 2 = 3 := by
  apply no_exit_unique 2 (residue 2) 3 (residue_lt 2) (by decide)
    (residue_no_exit 2)
  rintro ⟨j,hj,hj2,he⟩
  interval_cases j <;> norm_num [oddCount, orbit, shortcut] at he

theorem residue_ge_two (L : ℕ) (hL : 2 ≤ L) : 2 ≤ residue L := by
  have hcounts := (no_exit_iff_counts (residue L) L).1 (residue_no_exit L)
  have h2 := hcounts 2 hL
  by_contra h
  have hsmall : residue L = 0 ∨ residue L = 1 := by omega
  rcases hsmall with h0 | h1
  · rw [h0] at h2; norm_num [oddCount, orbit, shortcut, N1.c] at h2
  · rw [h1] at h2; norm_num [oddCount, orbit, shortcut, N1.c] at h2

/-- Theorem 1 implies the square bound for every positive integer surviving L steps. -/
theorem survivor_square_bound (n L : ℕ) (hn : 2 ≤ n)
    (h : ¬ CoefficientExitWithin n L) : 2^L ≤ n*n := by
  have hm := HypothesisMAssembly.hypothesis_M n hn
  have hlog : L ≤ Nat.log2 (n*n) := by
    by_contra hh
    exact h (exit_mono hm (by omega))
  exact (Nat.le_log2 (by nlinarith : n*n ≠ 0)).1 hlog

/-- Corollary 2, least-residue form. -/
theorem corollary2_residue (L : ℕ) (hL : 2 ≤ L) : 2^L ≤ residue L * residue L :=
  survivor_square_bound (residue L) L (residue_ge_two L hL) (residue_no_exit L)

theorem shift_count (n q L j : ℕ) (hj : j ≤ L) :
    oddCount (n + q * 2^L) j = oddCount n j := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hs := (HypMRev8.shift_lemma (n + q * 2^L) j (L-j)).2
    rw [Nat.add_sub_of_le hj] at hs
    simp only [HypMRev8Bridge.oddCount_agree] at hs
    rw [show n + (q+1)*2^L = (n+q*2^L)+2^L by ring, hs, ih]

/-- The exact residue/parity correspondence, including both directions. -/
theorem no_exit_iff_mod (n L : ℕ) :
    ¬ CoefficientExitWithin n L ↔ n % 2^L = residue L := by
  constructor
  · intro hn
    have hd := HypothesisMOrbit.same_parities_dvd L n (residue L)
      (no_exit_same_parities n (residue L) L hn (residue_no_exit L))
    have hm : Nat.ModEq (2^L) (residue L) n := by
      apply Nat.modEq_iff_dvd.2
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hd
    have he := hm.symm
    change n % 2^L = residue L % 2^L at he
    simpa only [Nat.mod_eq_of_lt (residue_lt L)] using he
  · intro hn
    apply (no_exit_iff_counts n L).2
    intro j hj
    have he : n = residue L + (n / 2^L) * 2^L := by
      have h := Nat.mod_add_div n (2^L)
      rw [hn] at h
      nlinarith
    rw [he, shift_count (residue L) (n / 2^L) L j hj]
    exact (no_exit_iff_counts (residue L) L).1 (residue_no_exit L) j hj

/-- Corollary 2 in the integer approximation form requested by the brief. -/
theorem corollary2_integer (n L : ℕ) (hn : 2 ≤ n)
    (hmod : n % 2^L = residue L) : 2^L ≤ n*n :=
  survivor_square_bound n L hn ((no_exit_iff_mod n L).2 hmod)

theorem residue_mod (L j : ℕ) (hj : j ≤ L) : residue L % 2^j = residue j := by
  apply (no_exit_iff_mod (residue L) j).1
  intro h
  exact residue_no_exit L (exit_mono h hj)

theorem residue_step (L : ℕ) :
    residue (L+1) = residue L ∨ residue (L+1) = residue L + 2^L := by
  have hm := residue_mod (L+1) L (by omega)
  have hlo := residue_lt L
  have hhi := residue_lt (L+1)
  rw [Nat.pow_succ] at hhi
  have hdiv := Nat.mod_add_div (residue (L+1)) (2^L)
  have hp : 0 < 2^L := by positivity
  have hq : residue (L+1) / 2^L < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
  rw [hm] at hdiv
  interval_cases h : residue (L+1) / 2^L <;> simp_all <;> omega

theorem residue_mono : Monotone residue := by
  apply monotone_nat_of_le_succ
  intro L
  rcases residue_step L with h | h
  · rw [h]
  · rw [h]; exact Nat.le_add_right _ _

#check corollary2_residue
#print axioms corollary2_residue
#check survivor_square_bound
#print axioms survivor_square_bound
#check corollary2_integer
#print axioms corollary2_integer
#check no_exit_iff_mod
#print axioms no_exit_iff_mod
end HypMRev9
