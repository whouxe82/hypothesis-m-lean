import Rev9Residues

/-!
Independent finite base for the second proof: every seed 2≤n<2^22.
The literal residue certificate is checked by the Lean kernel using `decide`.
The proof below does not use Theorem 1 or Corollary 2.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace HypMRev9Base
open HypothesisMTarget HypMRev9

def witnesses : List ℕ := [0, 1, 3, 3, 11, 27, 59, 123, 251, 507, 1019, 1019, 3067, 7163, 7163, 23547, 23547, 23547, 154619, 416763, 941051, 1989627, 4086779, 4086779, 12475387, 29252603, 29252603, 29252603, 163470331, 163470331, 163470331, 1237212155, 3384695803, 7679663099, 16269597691, 16269597691, 50629336059, 50629336059, 188068289531, 188068289531, 737824103419, 737824103419, 737824103419, 737824103419, 737824103419]
def witness (L : ℕ) : ℕ := witnesses[L]!

theorem finite_certificate : ∀ L : Fin 45,
    witness L.val < 2^L.val ∧
    (∀ j : Fin (L.val+1), oddCount (witness L.val) j.val = N1.c j.val) ∧
    (2 ≤ L.val → 2^L.val ≤ witness L.val * witness L.val) := by
  decide

theorem residue_eq_witness (L : ℕ) (hL : L ≤ 44) : residue L = witness L := by
  have hc : witness L < 2^L ∧
      (∀ j : Fin (L+1), oddCount (witness L) j.val = N1.c j.val) ∧
      (2 ≤ L → 2^L ≤ witness L * witness L) := finite_certificate ⟨L,by omega⟩
  apply no_exit_unique L (residue L) (witness L) (residue_lt L) hc.1 (residue_no_exit L)
  apply (no_exit_iff_counts (witness L) L).2
  intro j hj
  exact hc.2.1 ⟨j,by omega⟩

/-- Finite square certificate, proved by computation rather than Corollary 2. -/
theorem finite_residue_square (L : ℕ) (hlo : 2 ≤ L) (hhi : L ≤ 44) :
    2^L ≤ residue L * residue L := by
  rw [residue_eq_witness L hhi]
  exact (finite_certificate ⟨L,by omega⟩).2.2 hlo

/-- Independent finite base used by the second proof of Theorem 1. -/
theorem second_proof_finite_base (n : ℕ) (hn : 2 ≤ n) (hsmall : n < 2^22) :
    CoefficientExitWithin n (Nat.log2 (n*n)+1) := by
  by_contra hno
  let L := Nat.log2 (n*n)+1
  have hne : n*n ≠ 0 := by nlinarith
  have hsq : n*n < 2^(2*22) := by
    have hh := Nat.mul_lt_mul_of_lt_of_lt hsmall hsmall
    simpa [← Nat.pow_add] using hh
  have hlog : Nat.log2 (n*n) < 44 := (Nat.log2_lt hne).2 hsq
  have hLlo : 2 ≤ L := by
    have hh : 1 ≤ Nat.log2 (n*n) := (Nat.le_log2 hne).2 (by norm_num; nlinarith)
    dsimp [L]; omega
  have hLhi : L ≤ 44 := by dsimp [L]; omega
  have hm := (no_exit_iff_mod n L).1 hno
  have hrn : residue L ≤ n := by rw [← hm]; exact Nat.mod_le _ _
  have hc := finite_residue_square L hLlo hLhi
  have hpow : n*n < 2^L := Nat.lt_log2_self
  nlinarith

#check finite_certificate
#print axioms finite_certificate
#check second_proof_finite_base
#print axioms second_proof_finite_base
end HypMRev9Base
