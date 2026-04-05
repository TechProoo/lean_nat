import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace NatArith

/-!
# Natural Number Arithmetic
Proofs about parity (even / odd) and the Gauss summation formula on ℕ.
-/

-- ─────────────────────────────────────────
-- Parity definitions
-- ─────────────────────────────────────────

def even (n : ℕ) : Prop := ∃ k : ℕ, n = 2 * k
def odd  (n : ℕ) : Prop := ∃ k : ℕ, n = 2 * k + 1

-- Base cases

theorem even_zero  : even 0 := ⟨0, rfl⟩
theorem even_two   : even 2 := ⟨1, rfl⟩
theorem even_four  : even 4 := ⟨2, rfl⟩
theorem odd_one    : odd  1 := ⟨0, rfl⟩
theorem odd_three  : odd  3 := ⟨1, rfl⟩
theorem odd_five   : odd  5 := ⟨2, rfl⟩

-- Every even number's successor is odd, and vice-versa

theorem succ_even {n : ℕ} (h : even n) : odd (n + 1) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

theorem succ_odd {n : ℕ} (h : odd n) : even (n + 1) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

-- ─────────────────────────────────────────
-- Parity under addition
-- ─────────────────────────────────────────

theorem even_add_even {m n : ℕ} (hm : even m) (hn : even n) : even (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by omega⟩

theorem odd_add_odd {m n : ℕ} (hm : odd m) (hn : odd n) : even (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b + 1, by omega⟩

theorem even_add_odd {m n : ℕ} (hm : even m) (hn : odd n) : odd (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by omega⟩

theorem odd_add_even {m n : ℕ} (hm : odd m) (hn : even n) : odd (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by omega⟩

-- ─────────────────────────────────────────
-- Parity under multiplication
-- ─────────────────────────────────────────

-- even * anything = even
theorem even_mul_any (m : ℕ) {n : ℕ} (hn : even n) : even (m * n) := by
  obtain ⟨k, hk⟩ := hn
  exact ⟨m * k, by rw [hk]; ring⟩

theorem any_mul_even (m : ℕ) {n : ℕ} (hn : even n) : even (n * m) := by
  rw [Nat.mul_comm]
  exact even_mul_any m hn

-- odd * odd = odd
theorem odd_mul_odd {m n : ℕ} (hm : odd m) (hn : odd n) : odd (m * n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨2 * a * b + a + b, by rw [ha, hb]; ring⟩

-- ─────────────────────────────────────────
-- Consecutive product and corollaries
-- ─────────────────────────────────────────

-- n * (n + 1) is always even (one of the two must be even)
theorem consec_even (n : ℕ) : even (n * (n + 1)) := by
  induction n with
  | zero     => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + n + 1, ?_⟩
    have : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by ring
    linarith

-- n² + n is always even  (since n² + n = n * (n + 1))
theorem n_sq_plus_n_even (n : ℕ) : even (n ^ 2 + n) := by
  have h : n ^ 2 + n = n * (n + 1) := by ring
  rw [h]
  exact consec_even n

-- ─────────────────────────────────────────
-- Gauss summation formula
-- ─────────────────────────────────────────

-- Sum of the first n natural numbers: 0 + 1 + 2 + … + n
def sumTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

-- Closed form: 2 * (0 + 1 + … + n) = n * (n + 1)
theorem gauss (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero     => rfl
  | succ n ih =>
    simp only [sumTo]
    have : 2 * (n + 1 + sumTo n) = 2 * (n + 1) + 2 * sumTo n := by ring
    rw [this, ih]
    ring

-- sumTo is monotone
theorem sumTo_mono {m n : ℕ} (h : m ≤ n) : sumTo m ≤ sumTo n := by
  induction n with
  | zero     => simp [Nat.le_zero.mp h, sumTo]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | rfl
    · have hm : m ≤ n := Nat.lt_succ_iff.mp hlt
      simp only [sumTo]
      linarith [ih hm]
    · le_refl _

-- sumTo (n+1) = sumTo n + (n+1)  (unfolding the definition cleanly)
theorem sumTo_succ (n : ℕ) : sumTo (n + 1) = sumTo n + (n + 1) := by
  simp [sumTo]; ring

end NatArith
