import Erdos190.Divergence

/-!
# `Filter.Eventually` form of the main statement (as used in formal-conjectures)
-/

namespace Erdos190

open Filter

/-- For every `C`, for all sufficiently large `k`, every `N` such that `[N]` is canonical
for `k` satisfies `(C k)^k < N`.  Equivalently `H(k)^{1/k}/k → ∞`. -/
theorem erdos190_eventually (C : ℕ) :
    ∀ᶠ k in atTop, ∀ N, Canonical N k → (C * k) ^ k < N := by
  obtain ⟨K, hK⟩ := erdos190 C
  exact eventually_atTop.2 ⟨K, hK⟩

end Erdos190

namespace Erdos190

open Filter

/-- The canonical van der Waerden number `H(k)`: the least canonical `N` (`sInf`, hence `0`
when no canonical `N` exists; existence is Erdős–Graham's theorem, via Szemerédi's theorem,
and is not formalized here). -/
noncomputable def H (k : ℕ) : ℕ := sInf {N | Canonical N k}

/-- Assuming `H(k)` exists for every `k`: `(C k)^k < H(k)` for all large `k`, i.e.
`H(k)^{1/k}/k → ∞`. -/
theorem erdos190_H (hH : ∀ k, {N | Canonical N k}.Nonempty) (C : ℕ) :
    ∀ᶠ k in atTop, (C * k) ^ k < H k := by
  filter_upwards [erdos190_eventually C] with k hk
  exact hk (H k) (Nat.sInf_mem (hH k))

end Erdos190
