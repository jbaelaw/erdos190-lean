/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Ho Bae
-/
import Erdos190

/-!
# Solutions to the Challenge

The declarations of `Challenge.lean`, proved.  The definitions are repeated verbatim so that they
are the same declarations as in the Challenge; the theorems are bridges to the `Erdos190` library:

* `divergence`            ← `Erdos190.erdos190`            (`Erdos190/Divergence.lean`)
* `divergence_eventually` ← `Erdos190.erdos190_eventually` (`Erdos190/Eventually.lean`)
* `H_divergence`          ← `Erdos190.erdos190_H`          (`Erdos190/Eventually.lean`)
* `explicit_bound`        ← `Erdos190.main_combinatorial`  (`Erdos190/Main.lean`)

The library's `Erdos190.AP` is a structure bundling `(a, d)` with the two side conditions; the
Challenge uses the unbundled predicate `IsAP`.  The two descriptions of an arithmetic progression
are interchangeable, which is what `hasMonoAP_iff`, `hasRainbowAP_iff` and `canonical_iff` record.
-/

open Filter

namespace Erdos190.Palomar

def IsAP (N k a d : ℕ) : Prop := 0 < d ∧ a + (k - 1) * d < N

def term (N k a d : ℕ) (h : IsAP N k a d) (i : Fin k) : Fin N :=
  ⟨a + i.1 * d, by
    have hi : i.1 ≤ k - 1 := Nat.le_sub_one_of_lt i.2
    have := h.2
    nlinarith [Nat.mul_le_mul_right d hi]⟩

def HasMonoAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ a d, ∃ h : IsAP N k a d, ∀ i j : Fin k, c (term N k a d h i) = c (term N k a d h j)

def HasRainbowAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ a d, ∃ h : IsAP N k a d, ∀ i j : Fin k, c (term N k a d h i) = c (term N k a d h j) → i = j

def Canonical (N k : ℕ) : Prop :=
  ∀ c : Fin N → ℕ, HasMonoAP (k := k) c ∨ HasRainbowAP (k := k) c

noncomputable def H (k : ℕ) : ℕ := sInf {N | Canonical N k}

theorem hasMonoAP_iff {N k : ℕ} {κ : Type*} (c : Fin N → κ) :
    HasMonoAP (k := k) c ↔ Erdos190.HasMonoAP (k := k) c := by
  constructor
  · rintro ⟨a, d, h, hc⟩
    exact ⟨⟨a, d, h.1, h.2⟩, hc⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.a, P.d, ⟨P.d_pos, P.last_lt⟩, hP⟩

theorem hasRainbowAP_iff {N k : ℕ} {κ : Type*} (c : Fin N → κ) :
    HasRainbowAP (k := k) c ↔ Erdos190.HasRainbowAP (k := k) c := by
  constructor
  · rintro ⟨a, d, h, hc⟩
    exact ⟨⟨a, d, h.1, h.2⟩, hc⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.a, P.d, ⟨P.d_pos, P.last_lt⟩, hP⟩

theorem canonical_iff (N k : ℕ) : Canonical N k ↔ Erdos190.Canonical N k := by
  unfold Canonical Erdos190.Canonical
  simp only [hasMonoAP_iff, hasRainbowAP_iff]

theorem H_eq (k : ℕ) : H k = sInf {N | Erdos190.Canonical N k} := by
  unfold H
  congr 1
  ext N
  exact canonical_iff N k

/-- Statement about canonical `N` only; see `Challenge.lean`. -/
theorem divergence (C : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ N, Canonical N k → (C * k) ^ k < N := by
  obtain ⟨K, hK⟩ := Erdos190.erdos190 C
  exact ⟨K, fun k hk N hN => hK k hk N ((canonical_iff N k).1 hN)⟩

theorem divergence_eventually (C : ℕ) :
    ∀ᶠ k in atTop, ∀ N, Canonical N k → (C * k) ^ k < N := by
  filter_upwards [Erdos190.erdos190_eventually C] with k hk N hN
  exact hk N ((canonical_iff N k).1 hN)

theorem H_divergence (hH : ∀ k, {N | Canonical N k}.Nonempty) (C : ℕ) :
    ∀ᶠ k in atTop, (C * k) ^ k < H k := by
  have hH' : ∀ k, {N | Erdos190.Canonical N k}.Nonempty := fun k => by
    obtain ⟨N, hN⟩ := hH k
    exact ⟨N, (canonical_iff N k).1 hN⟩
  filter_upwards [Erdos190.erdos190_H hH' C] with k hk
  rw [H_eq]
  exact hk

theorem explicit_bound (k : ℕ) (hk : 12 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ (k - 1) / 2 < p ∧ p ≤ k - 1 ∧
      ∀ N, Canonical N k → p ^ (p - k / 3) * ((k / 3) ^ (k - 1) / (16 * k ^ 2)) < N := by
  obtain ⟨p, hp, hlo, hhi, -, hb⟩ := Erdos190.main_combinatorial k hk
  refine ⟨p, hp, hlo, hhi, fun N hN => ?_⟩
  have := hb N ((canonical_iff N k).1 hN)
  simpa [Erdos190.bound, Erdos190.r₀] using this

end Erdos190.Palomar
