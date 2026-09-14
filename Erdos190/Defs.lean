import Mathlib

/-!
# Erdős Problem #190 — definitions

`[N]` is modelled as `Fin N`.  A `k`-term arithmetic progression in `Fin N` is given by a
start `a` and a common difference `d ≥ 1` with `a + (k-1)*d < N`; its `i`-th term is `a + i*d`.
-/

namespace Erdos190

/-- A `k`-AP in `[N]`: start `a`, difference `d ≥ 1`, last term `< N`. -/
structure AP (N k : ℕ) where
  a : ℕ
  d : ℕ
  d_pos : 0 < d
  last_lt : a + (k - 1) * d < N

/-- The `i`-th term of an AP, as an element of `Fin N` (for `i < k`). -/
def AP.term {N k : ℕ} (P : AP N k) (i : Fin k) : Fin N :=
  ⟨P.a + i.1 * P.d, by
    have hi : i.1 ≤ k - 1 := Nat.le_sub_one_of_lt i.2
    have := P.last_lt
    nlinarith [Nat.mul_le_mul_right P.d hi]⟩

/-- A colouring `c` has a monochromatic `k`-AP. -/
def HasMonoAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ P : AP N k, ∀ i j : Fin k, c (P.term i) = c (P.term j)

/-- A colouring `c` has a rainbow `k`-AP (all terms of distinct colours). -/
def HasRainbowAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ P : AP N k, ∀ i j : Fin k, c (P.term i) = c (P.term j) → i = j

/-- `[N]` is *canonical* for `k`: every colouring (with any number of colours, modelled by
colours in `ℕ`) contains a monochromatic or a rainbow `k`-AP.  `H(k)` is the least such `N`. -/
def Canonical (N k : ℕ) : Prop :=
  ∀ c : Fin N → ℕ, HasMonoAP (k := k) c ∨ HasRainbowAP (k := k) c

/-- `[N]` forces a monochromatic `k`-AP in every `r`-colouring; `W(r,k)` is the least such `N`. -/
def Forces (N r k : ℕ) : Prop :=
  ∀ c : Fin N → Fin r, HasMonoAP (k := k) c

end Erdos190
