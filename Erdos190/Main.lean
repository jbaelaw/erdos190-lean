import Erdos190.Defs
import Erdos190.Pigeonhole
import Erdos190.BCT
import Erdos190.EL

/-!
# Assembly: an explicit lower bound for `H(k)` from EL + BCT + Bertrand

For `k ≥ 12` choose a prime `p` with `(k-1)/2 < p ≤ k-1` (Bertrand) and
`r₀ = ⌊k/3⌋`.  Then every `N` with `[N]` canonical for `k` satisfies
`N > p^(p - r₀) * (r₀^(k-1) / (16 k²))`.
-/

namespace Erdos190

/-- Transport of colourings along an equality of lengths. -/
theorem hasMonoAP_cast {N N' k : ℕ} {κ : Type*} (h : N = N') (c : Fin N' → κ) :
    HasMonoAP (k := k) (c ∘ Fin.cast h) ↔ HasMonoAP (k := k) c := by
  subst h; exact Iff.rfl

/-- Recolouring injectively preserves the absence of monochromatic APs. -/
theorem not_hasMonoAP_comp {N k : ℕ} {κ κ' : Type*} (c : Fin N → κ) (f : κ → κ')
    (hf : Function.Injective f) (h : ¬ HasMonoAP (k := k) c) : ¬ HasMonoAP (k := k) (f ∘ c) :=
  fun h' => h (hasMonoAP_of_comp_injective c f hf h')

/-- Lift an AP of `[N]` to `[N']` for `N ≤ N'`. -/
def AP.lift {N N' k : ℕ} (h : N ≤ N') (P : AP N k) : AP N' k :=
  ⟨P.a, P.d, P.d_pos, lt_of_lt_of_le P.last_lt h⟩

theorem AP.lift_term {N N' k : ℕ} (h : N ≤ N') (P : AP N k) (i : Fin k) :
    (P.lift h).term i = Fin.castLE h (P.term i) := rfl

/-- Being canonical is monotone in `N`. -/
theorem canonical_mono {N N' k : ℕ} (h : N ≤ N') (hc : Canonical N k) : Canonical N' k := by
  intro c
  rcases hc (c ∘ Fin.castLE h) with ⟨P, hP⟩ | ⟨P, hP⟩
  · left
    exact ⟨P.lift h, fun i j => by simpa [AP.lift_term] using hP i j⟩
  · right
    exact ⟨P.lift h, fun i j hij => hP i j (by simpa [AP.lift_term] using hij)⟩

/-- Iterating the BCT step from `r₀` colours up to `p` colours. -/
theorem iterate_bct {p k r₀ N₀ : ℕ} (hp : p.Prime) (hpk : p ≤ k) (hr₀ : 2 ≤ r₀)
    (c₀ : Fin N₀ → Fin r₀) (h₀ : ¬ HasMonoAP (k := k) c₀) :
    ∀ m, r₀ + m ≤ p → ∃ c : Fin (p ^ m * N₀) → Fin (r₀ + m), ¬ HasMonoAP (k := k) c := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨c₀ ∘ Fin.cast (by simp), ?_⟩
    rwa [hasMonoAP_cast]
  | succ m ih =>
    intro hm
    obtain ⟨c, hc⟩ := ih (by omega)
    have hcast : r₀ + m = r₀ + m + 1 - 1 := by omega
    have hc' : ¬ HasMonoAP (k := k) (Fin.cast hcast ∘ c) :=
      not_hasMonoAP_comp c (Fin.cast hcast) (Fin.cast_injective hcast) hc
    obtain ⟨c', hc''⟩ := bct_step (M := p ^ m * N₀) (r := r₀ + m + 1) hp (by omega) (by omega) hpk
      (Fin.cast hcast ∘ c) hc'
    have hlen : p ^ (m + 1) * N₀ = p * (p ^ m * N₀) := by ring
    refine ⟨c' ∘ Fin.cast hlen, ?_⟩
    rwa [hasMonoAP_cast]

/-- The number of colours used in the base: `r₀ = ⌊k/3⌋`.  (Any `r₀ = k/c` with `c > 2` works
for the qualitative statement when the prime is only guaranteed by Bertrand's postulate.) -/
def r₀ (k : ℕ) : ℕ := k / 3

theorem two_le_r₀ (k : ℕ) (hk : 6 ≤ k) : 2 ≤ r₀ k := by
  unfold r₀; omega

/-- The explicit lower bound `L(k) = p^(p - r₀) * (r₀^(k-1) / (16 k²))` for the chosen prime. -/
def bound (k p : ℕ) : ℕ := p ^ (p - r₀ k) * (r₀ k ^ (k - 1) / (16 * k ^ 2))

/-- **Main combinatorial theorem.**  For `k ≥ 12` there is a prime `p` with
`(k-1)/2 < p ≤ k-1` such that every canonical `N` exceeds `bound k p`. -/
theorem main_combinatorial (k : ℕ) (hk : 12 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ (k - 1) / 2 < p ∧ p ≤ k - 1 ∧ r₀ k < p ∧
      ∀ N, Canonical N k → bound k p < N := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul ((k - 1) / 2) (by omega)
  have hpk : p ≤ k - 1 := by omega
  have hr2 := two_le_r₀ k (by omega)
  have hrp : r₀ k < p := by unfold r₀; omega
  refine ⟨p, hp, hlo, hpk, hrp, ?_⟩
  -- the base colouring
  obtain ⟨c₀, hc₀⟩ := el_base (r₀ k) k hr2 (by omega)
  -- iterate BCT
  obtain ⟨c, hc⟩ := iterate_bct hp (by omega) hr2 c₀ hc₀ (p - r₀ k) (by omega)
  have hcol : r₀ k + (p - r₀ k) = p := by omega
  have hc' : ¬ HasMonoAP (k := k) (Fin.cast hcol ∘ c) :=
    not_hasMonoAP_comp c (Fin.cast hcol) (Fin.cast_injective hcol) hc
  have hnot : ¬ Canonical (bound k p) k :=
    not_canonical_of_coloring (by omega) hpk (Fin.cast hcol ∘ c) hc'
  intro N hN
  by_contra hle
  push_neg at hle
  exact hnot (canonical_mono hle hN)

end Erdos190
