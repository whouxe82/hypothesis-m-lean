import N1
import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Exact finite count for every real corridor width. For a fixed depth L, all
relevant threshold values lie on a rational grid. Rounding K down on a fine
enough grid preserves every comparison, including equality at the boundary.
The existing rational theorem can therefore be applied without continuity
assumptions on the counting function.
-/
namespace HypMRev9Real
noncomputable section

def Admissible (K : ℝ) (w : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ w.length →
    2^j ≤ 3^((w.take j).count true) ∧
    (3 : ℝ)^((w.take j).count true) ≤ K * (2 : ℝ)^j

def count (K : ℝ) (L : ℕ) : ℕ := by
  classical
  exact (N1.allWords L).countP (fun w => decide (Admissible K w))

def choice (K : ℝ) (j : ℕ) : Prop :=
  (3 : ℝ)^(N1.c j+1) ≤ K*(2 : ℝ)^j

instance (K : ℝ) (j : ℕ) : Decidable (choice K j) := Classical.propDecidable _

def choices (K : ℝ) : ℕ → ℕ
  | 0 => 0
  | L+1 => choices K L + (if 2 ≤ L+1 ∧ choice K (L+1) then 1 else 0)

theorem rational_grid (K : ℝ) (hlo : 3 < K) (hhi : K ≤ 9/2) (L : ℕ) :
    ∃ P Q : ℕ, 0 < Q ∧ 3*Q < P ∧ 2*P ≤ 9*Q ∧
      ∀ j ≤ L, ∀ a : ℕ,
        ((3 : ℝ)^a ≤ K*(2 : ℝ)^j ↔ Q*3^a ≤ P*2^j) := by
  obtain ⟨t,ht⟩ := exists_nat_gt (1/(K-3))
  have hd : 0 < K-3 := by linarith
  have ht0 : 0 < t := by
    have : (0 : ℝ) < t := lt_trans (by positivity) ht
    exact_mod_cast this
  let Q : ℕ := t*2^L
  let P : ℕ := ⌊K*(Q : ℝ)⌋₊
  have hQ : 0 < Q := Nat.mul_pos ht0 (by positivity)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hKQ : 0 ≤ K*(Q : ℝ) := by positivity
  have htQ : t ≤ Q := by
    dsimp [Q]
    exact Nat.le_mul_of_pos_right t (by positivity)
  have htQr : (t : ℝ) ≤ Q := by exact_mod_cast htQ
  have hgap : 1 < (K-3)*(t : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hd).1 ht
  have hPlo : 3*Q+1 ≤ P := by
    apply Nat.le_floor
    push_cast
    nlinarith
  have hPupper : (P : ℝ) ≤ K*(Q : ℝ) := Nat.floor_le hKQ
  have hPhi : 2*P ≤ 9*Q := by
    have : (2 : ℝ)*P ≤ 9*Q := by nlinarith
    exact_mod_cast this
  refine ⟨P,Q,hQ,by omega,hPhi,?_⟩
  intro j hj a
  let f : ℕ := t*2^(L-j)
  have hf : 0 < f := Nat.mul_pos ht0 (by positivity)
  have hfac : Q = f*2^j := by
    dsimp [Q,f]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  have hfacR : (Q : ℝ) = (f : ℝ)*(2 : ℝ)^j := by exact_mod_cast hfac
  have hfr : (0 : ℝ) < f := by exact_mod_cast hf
  have hgrid : ((f*3^a : ℕ) : ℝ) ≤ K*(Q : ℝ) ↔
      (3 : ℝ)^a ≤ K*(2 : ℝ)^j := by
    push_cast
    rw [hfacR]
    constructor
    · intro h
      apply (mul_le_mul_iff_left₀ hfr).1
      nlinarith [h]
    · intro h
      have hh := mul_le_mul_of_nonneg_left h (le_of_lt hfr)
      nlinarith [hh]
  have hnat : Q*3^a ≤ P*2^j ↔ f*3^a ≤ P := by
    rw [hfac, show f*2^j*3^a = (f*3^a)*2^j by ring]
    exact Nat.mul_le_mul_right_iff (by positivity : 0 < 2^j)
  rw [hnat]
  exact hgrid.symm.trans (Nat.le_floor_iff hKQ).symm

/-- Proposition N1, exact count, for all real K in (3,9/2].
The count and choice predicate are the literal power-inequality definitions. -/
theorem propositionN1_real_count (K : ℝ) (hlo : 3 < K) (hhi : K ≤ 9/2) (L : ℕ) :
    count K L = 2^(choices K L) := by
  classical
  obtain ⟨P,Q,hQ,hloQ,hhiQ,hgrid⟩ := rational_grid K hlo hhi L
  have hadm : ∀ w, w.length = L → (Admissible K w ↔ N1.Admissible P Q w) := by
    intro w hw
    unfold Admissible N1.Admissible
    constructor <;> intro h j hj hjw
    · exact ⟨(h j hj hjw).1, (hgrid j (by omega) _).1 (h j hj hjw).2⟩
    · exact ⟨(h j hj hjw).1, (hgrid j (by omega) _).2 (h j hj hjw).2⟩
  have hcount : count K L = N1.N P Q L := by
    unfold count N1.N
    apply List.countP_congr
    intro w hw
    simpa only [decide_eq_true_eq] using hadm w ((N1.mem_allWords L w).1 hw)
  have hchoices : ∀ j ≤ L, choices K j = N1.B P Q j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [choices, N1.B, ih (by omega)]
      have hc : choice K (j+1) ↔ N1.choice P Q (j+1) := hgrid (j+1) hj _
      simp only [hc]
  rw [hcount, N1.N1 P Q hQ hloQ hhiQ, hchoices L le_rfl]

#check propositionN1_real_count
#print axioms propositionN1_real_count
end
end HypMRev9Real
