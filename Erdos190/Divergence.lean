import Erdos190.Main

/-!
# Divergence: `H(k)^{1/k}/k → ∞`

We prove the elementary form: for every `C`, `(C k)^k < H(k)` for all large `k`, i.e. every `N`
with `[N]` canonical for `k` satisfies `N > (C k)^k`.
-/

namespace Erdos190

theorem pow_four_lt_four_pow (k : ℕ) (hk : 30 ≤ k) : k ^ 4 < 4 ^ (k - 10) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 4 ≤ 4 * n ^ 4 := by
      have h3 : 3 ≤ n := by omega
      have hn2 : 3 * n ≤ n ^ 2 := by nlinarith
      have hn3 : 3 * n ^ 2 ≤ n ^ 3 := by nlinarith
      have hn4 : 3 * n ^ 3 ≤ n ^ 4 := by nlinarith
      nlinarith [hn2, hn3, hn4]
    have h2 : 4 ^ (n + 1 - 10) = 4 * 4 ^ (n - 10) := by
      rw [show n + 1 - 10 = (n - 10) + 1 by omega, pow_succ]; ring
    rw [h2]; omega

/-- Key numeric inequality: for `C ≥ 1` and `k ≥ max 30 (2 (4C)^12)`,
`(4C)^k * k^4 < (k/2)^(k/6)`. -/
theorem key_ineq (C k : ℕ) (hC : 1 ≤ C) (hk30 : 30 ≤ k) (hkC : 2 * (4 * C) ^ 12 ≤ k) :
    (4 * C) ^ k * k ^ 4 < (k / 2) ^ (k / 6) := by
  have h4C : 4 ≤ 4 * C := by omega
  -- (k/2)^(k/6) ≥ ((4C)^12)^(k/6) = (4C)^(12 (k/6)) ≥ (4C)^(2k-10)
  have hs : (4 * C) ^ 12 ≤ k / 2 := by omega
  have h1 : ((4 * C) ^ 12) ^ (k / 6) ≤ (k / 2) ^ (k / 6) := Nat.pow_le_pow_left hs _
  have h2 : (4 * C) ^ (2 * k - 10) ≤ ((4 * C) ^ 12) ^ (k / 6) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  -- (4C)^k * k^4 < (4C)^k * 4^(k-10) ≤ (4C)^k * (4C)^(k-10) = (4C)^(2k-10)
  have h3 : k ^ 4 < 4 ^ (k - 10) := pow_four_lt_four_pow k hk30
  have h4 : 4 ^ (k - 10) ≤ (4 * C) ^ (k - 10) := Nat.pow_le_pow_left h4C _
  have h5 : (4 * C) ^ k * (4 * C) ^ (k - 10) = (4 * C) ^ (2 * k - 10) := by
    rw [← pow_add]; congr 1; omega
  have hpos : 0 < (4 * C) ^ k := by positivity
  calc (4 * C) ^ k * k ^ 4 < (4 * C) ^ k * 4 ^ (k - 10) := Nat.mul_lt_mul_of_pos_left h3 hpos
    _ ≤ (4 * C) ^ k * (4 * C) ^ (k - 10) := Nat.mul_le_mul_left _ h4
    _ = (4 * C) ^ (2 * k - 10) := h5
    _ ≤ ((4 * C) ^ 12) ^ (k / 6) := h2
    _ ≤ (k / 2) ^ (k / 6) := h1

/-- `(C k)^k < bound k p` for large `k`. -/
theorem bound_large (C k p : ℕ) (hC : 1 ≤ C) (hk : 30 ≤ k) (hkC : 2 * (4 * C) ^ 12 ≤ k)
    (hk256 : 768 ≤ k) (hlo : (k - 1) / 2 < p) :
    (C * k) ^ k < bound k p := by
  unfold bound r₀
  set q := k / 3 with hq
  set s := k / 2 with hs
  set m := k / 6 with hm
  have hq256 : 256 ≤ q := by omega
  have hk4q : k ≤ 4 * q := by omega
  have hqk : q ≤ k := by omega
  -- p^(p - q) ≥ s^m
  have hps : s ≤ p := by omega
  have hpm : m ≤ p - q := by omega
  have hA : s ^ m ≤ p ^ (p - q) :=
    le_trans (Nat.pow_le_pow_left hps m) (Nat.pow_le_pow_right (by omega) hpm)
  -- q^(k-1) / (16 k^2) ≥ q^(k-4)
  have hD : 16 * k ^ 2 ≤ q ^ 3 := by
    calc 16 * k ^ 2 ≤ 16 * (4 * q) ^ 2 := by gcongr
      _ = 256 * q ^ 2 := by ring
      _ ≤ q * q ^ 2 := by gcongr
      _ = q ^ 3 := by ring
  have hB : q ^ (k - 4) ≤ q ^ (k - 1) / (16 * k ^ 2) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc q ^ (k - 4) * (16 * k ^ 2) ≤ q ^ (k - 4) * q ^ 3 := Nat.mul_le_mul_left _ hD
      _ = q ^ (k - 1) := by rw [← pow_add]; congr 1; omega
  -- (C k)^k ≤ (4 C q)^k = (4C)^k q^k
  have hC1 : (C * k) ^ k ≤ ((4 * C) ^ k * q ^ 4) * q ^ (k - 4) := by
    calc (C * k) ^ k ≤ (C * (4 * q)) ^ k := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hk4q) _
      _ = (4 * C) ^ k * q ^ k := by rw [show C * (4 * q) = (4 * C) * q by ring, mul_pow]
      _ = ((4 * C) ^ k * q ^ 4) * q ^ (k - 4) := by
          rw [mul_assoc, ← pow_add]; congr 2; omega
  have hkey : (4 * C) ^ k * q ^ 4 < s ^ m := by
    calc (4 * C) ^ k * q ^ 4 ≤ (4 * C) ^ k * k ^ 4 := by gcongr
      _ < s ^ m := key_ineq C k hC hk hkC
  have hqpos : 0 < q ^ (k - 4) := by positivity
  calc (C * k) ^ k ≤ ((4 * C) ^ k * q ^ 4) * q ^ (k - 4) := hC1
    _ < s ^ m * q ^ (k - 4) := Nat.mul_lt_mul_of_pos_right hkey hqpos
    _ ≤ p ^ (p - q) * (q ^ (k - 1) / (16 * k ^ 2)) := Nat.mul_le_mul hA hB

/-- **Erdős Problem #190 (qualitative form).**  For every `C` there is `K` such that for all
`k ≥ K`, every `N` for which `[N]` is canonical for `k` satisfies `N > (C k)^k`; in other words
`H(k)^{1/k}/k → ∞`. -/
theorem erdos190 (C : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ N, Canonical N k → (C * k) ^ k < N := by
  refine ⟨max 768 (2 * (4 * (C + 1)) ^ 12), fun k hk N hN => ?_⟩
  have hk768 : 768 ≤ k := le_trans (le_max_left _ _) hk
  have hkC : 2 * (4 * (C + 1)) ^ 12 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨p, hp, hlo, hhi, hrp, hbound⟩ := main_combinatorial k (by omega)
  have h1 : (C * k) ^ k ≤ ((C + 1) * k) ^ k :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.le_succ C)) _
  have h2 := bound_large (C + 1) k p (by omega) (by omega) hkC hk768 hlo
  exact lt_of_le_of_lt h1 (lt_trans h2 (hbound N hN))

end Erdos190
