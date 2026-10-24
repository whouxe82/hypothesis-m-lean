import Rev9RealCount

/-! Proposition 14's finite exact formula, using integer powers to represent
floor(j log_3 2). The asymptotic conclusion is treated separately. -/
namespace HypMRev9Four

/-- The integer floor of j log_3 2, represented without real logarithms.
For positive j, 2^j lies strictly between 3^(c j-1) and 3^(c j). -/
def floorCount (j : ℕ) : ℕ := N1.c j-1

theorem c_positive (j : ℕ) (hj : 1 ≤ j) : 1 ≤ N1.c j := by
  have hs := N1.c_spec j
  have hp : 2^1 ≤ 2^j := Nat.pow_le_pow_right (by decide) hj
  by_contra hh
  have he : N1.c j = 0 := by omega
  rw [he] at hs
  norm_num at hs hp
  omega

theorem floorCount_spec (j : ℕ) (hj : 1 ≤ j) :
    3^(floorCount j) < 2^j ∧ 2^j < 3^(floorCount j+1) := by
  have hc := c_positive j hj
  have he : floorCount j+1 = N1.c j := by unfold floorCount; omega
  constructor
  · by_contra h
    have hle := N1.c_le_of j (floorCount j) (by omega)
    unfold floorCount at hle
    omega
  · rw [he]; exact N1.c_strict j hj

theorem c_two_step (j : ℕ) (hj : 1 ≤ j) :
    N1.c (j+2) = N1.c j + 1 + (if N1.choice 4 1 j then 1 else 0) := by
  have hs := N1.c_spec j
  have hs2 := N1.c_spec (j+2)
  have hp : 0 < 2^j := by positivity
  have htwo : 2^(j+2) = 4*2^j := by ring
  have hthree : 3^(N1.c j+2) = 9*3^(N1.c j) := by ring
  have hupper : N1.c (j+2) ≤ N1.c j+2 := by
    apply N1.c_le_of
    rw [htwo,hthree]
    omega
  have hlower : N1.c j+1 ≤ N1.c (j+2) := by
    by_contra h
    have hpw : 3^(N1.c (j+2)) ≤ 3^(N1.c j) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [htwo] at hs2
    omega
  by_cases hch : N1.choice 4 1 j
  · simp only [hch,ite_true]
    have hch' : 3^(N1.c j+1) ≤ 2^(j+2) := by
      simpa [N1.choice,htwo] using hch
    have hodd := N1.three_pow_odd (N1.c j+1)
    have heven := N1.two_pow_even (j+2) (by omega)
    have hstrict : 3^(N1.c j+1) < 2^(j+2) := by omega
    by_contra hh
    have hce : N1.c (j+2) = N1.c j+1 := by omega
    rw [hce] at hs2
    omega
  · simp only [hch,ite_false,Nat.add_zero]
    have hlt : 2^(j+2) ≤ 3^(N1.c j+1) := by
      unfold N1.choice at hch
      simp only [one_mul] at hch
      rw [htwo]
      omega
    have hu := N1.c_le_of (j+2) (N1.c j+1) hlt
    omega

theorem choices_four_telescopes (L : ℕ) :
    N1.B 4 1 L + L + 3 = N1.c (L+1) + N1.c (L+2) := by
  induction L with
  | zero => decide
  | succ L ih =>
    have hs := c_two_step (L+1) (by omega)
    have hc : (if 2 ≤ L+1 ∧ N1.choice 4 1 (L+1) then 1 else 0) =
        (if N1.choice 4 1 (L+1) then 1 else 0) := by
      by_cases hL : L=0
      · subst L; decide
      · simp [show 2 ≤ L+1 by omega]
    rw [N1.B,hc]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hs ⊢
    omega

/-- Proposition 14: N_4(L)=2^(f_(L+1)+f_(L+2)-L-1), including L=0. -/
theorem proposition14_exact (L : ℕ) :
    HypMRev9Real.count 4 L = 2^(floorCount (L+1)+floorCount (L+2)-L-1) := by
  have hcount : HypMRev9Real.count 4 L = N1.N 4 1 L := by
    classical
    unfold HypMRev9Real.count N1.N
    apply List.countP_congr
    intro w hw
    simp only [decide_eq_true_eq]
    unfold HypMRev9Real.Admissible N1.Admissible
    constructor <;> intro h j hj hjw
    · refine ⟨(h j hj hjw).1,?_⟩
      have := (h j hj hjw).2
      simpa only [one_mul] using (show 3^((w.take j).count true) ≤ 4*2^j from by exact_mod_cast this)
    · refine ⟨(h j hj hjw).1,?_⟩
      have := (h j hj hjw).2
      simp only [one_mul] at this
      exact_mod_cast this
  rw [hcount,N1.N1 4 1 (by decide) (by decide) (by decide)]
  congr 1
  have ht := choices_four_telescopes L
  have hc1 := c_positive (L+1) (by omega)
  have hc2 := c_positive (L+2) (by omega)
  unfold floorCount
  omega

#check floorCount_spec
#print axioms floorCount_spec
#check proposition14_exact
#print axioms proposition14_exact
end HypMRev9Four
