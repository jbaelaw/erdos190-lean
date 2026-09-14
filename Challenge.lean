/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Ho Bae
-/
import Mathlib

/-!
# Erdős Problem 190: every canonical `N` exceeds `(Ck)^k` for large `k` (hence `H(k)^{1/k}/k → ∞`, given that canonical `N` exist)

This is the statement of record for the Palomar submission.  It imports Mathlib only, introduces
the definitions of the problem, and states the result of

> J. H. Bae, *A resolution of Erdős Problem #190: the canonical van der Waerden number satisfies
> $H(k)^{1/k}/k\to\infty$*, arXiv:2604.20588 (v2, September 2026), Corollary 1.2 and
> Section 4.3.

## The problem

Let `H(k)` be the smallest `N` such that every finite colouring of `{1, …, N}` (into any number of
colours) contains a monochromatic `k`-term arithmetic progression or a rainbow one (all terms of
different colours).  Erdős and Graham (1979) asked whether `H(k)^{1/k}/k → ∞`; this is
[Problem 190](https://www.erdosproblems.com/190) in Bloom's database.

## What is stated here

`[N]` is modelled as `Fin N`.  A `k`-term arithmetic progression in `[N]` is given by a start
`a` and a common difference `d ≥ 1` with `a + (k-1)d < N`; its `i`-th term is `a + i·d`.

* `Erdos190.Palomar.Canonical N k`: every colouring `Fin N → ℕ` (colours in `ℕ`, so any number of
  colours) has a monochromatic or a rainbow `k`-AP.  `H(k)` is the least such `N`; it is
  `Erdos190.Palomar.H k := sInf {N | Canonical N k}` (`0` if no canonical `N` existed; existence
  is the Erdős–Graham canonical van der Waerden theorem, via Szemerédi's theorem, and is not part
  of this development).
* `Erdos190.Palomar.divergence`: for every `C` there is `K` such that for all `k ≥ K` every
  canonical `N` exceeds `(Ck)^k`.  This is a statement about canonical `N` only; on its own it
  says nothing about `H` (it holds vacuously for a `k` with no canonical `N`, and `H k = 0`
  there).  Combined with the existence of a canonical `N` for every `k` — the Erdős–Graham
  theorem, which is not formalized here — it gives `H(k) > (Ck)^k` for all large `k`, for
  every `C`, i.e. `H(k)^{1/k}/k → ∞`, which answers the question affirmatively.  That
  conditional conclusion is stated as `H_divergence` below.
* `Erdos190.Palomar.divergence_eventually`: the same statement about canonical `N` in
  `Filter.Eventually` form.
* `Erdos190.Palomar.H_divergence`: the conclusion for `H(k)` itself — `(Ck)^k < H k` for all
  large `k` — under the explicit hypothesis that a canonical `N` exists for every `k`.
* `Erdos190.Palomar.explicit_bound`: the explicit form behind the theorem, for `k ≥ 12`: there is a
  prime `p` with `(k-1)/2 < p ≤ k-1` (Bertrand's postulate) such that every canonical `N` exceeds
  `p^(p - ⌊k/3⌋) · ⌊⌊k/3⌋^(k-1) / (16 k²)⌋` (all divisions are integer divisions, as in the Lean
  statement).

## What the proof uses

The proofs live in the `Erdos190` library of this repository and follow Section 4.3 of the paper:
the Erdős–Lovász lower bound `W(r,k) - 1 ≥ r^(k-1)/(16k²)` for van der Waerden numbers, obtained
from the symmetric Lovász local lemma (imported from the Lean 4 project
[ProbMethodCombinatorics](https://github.com/yidiq7/ProbMethodCombinatorics), a formalization of
Zhao's lecture notes, pinned by commit), applied with `r₀ = ⌊k/3⌋` colours; the restricted
Blankenship–Cummings–Taranchuk recurrence `W(r,k) - 1 ≥ p (W(r-1,k) - 1)` for primes
`r ≤ p ≤ k`; Bertrand's postulate from Mathlib; and elementary asymptotics.  Every compared
declaration is to depend on `propext`, `Classical.choice` and `Quot.sound` only.

The paper's main theorem gives the explicit rate `H(k)^{1/k}/k ≥ (1/e − ε(k)) k / log k` using
the Baker–Harman–Pintz prime-gap theorem, which is not available in Mathlib; only the qualitative
statement (the paper's Corollary 1.2, via the elementary argument of its Section 4.3) is
formalized here.
-/

open Filter

namespace Erdos190.Palomar

/-- `(a, d)` describes a `k`-term arithmetic progression inside `[N] = Fin N`: common difference
`d ≥ 1` and last term `a + (k-1) d < N`. -/
def IsAP (N k a d : ℕ) : Prop := 0 < d ∧ a + (k - 1) * d < N

/-- The `i`-th term `a + i d` of the progression, as an element of `Fin N`. -/
def term (N k a d : ℕ) (h : IsAP N k a d) (i : Fin k) : Fin N :=
  ⟨a + i.1 * d, by
    have hi : i.1 ≤ k - 1 := Nat.le_sub_one_of_lt i.2
    have := h.2
    nlinarith [Nat.mul_le_mul_right d hi]⟩

/-- The colouring `c` has a monochromatic `k`-term arithmetic progression. -/
def HasMonoAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ a d, ∃ h : IsAP N k a d, ∀ i j : Fin k, c (term N k a d h i) = c (term N k a d h j)

/-- The colouring `c` has a rainbow `k`-term arithmetic progression (all terms of distinct
colours). -/
def HasRainbowAP {N k : ℕ} {κ : Type*} (c : Fin N → κ) : Prop :=
  ∃ a d, ∃ h : IsAP N k a d, ∀ i j : Fin k, c (term N k a d h i) = c (term N k a d h j) → i = j

/-- `[N]` is canonical for `k`: every colouring of `[N]` with any number of colours contains a
monochromatic or a rainbow `k`-AP. -/
def Canonical (N k : ℕ) : Prop :=
  ∀ c : Fin N → ℕ, HasMonoAP (k := k) c ∨ HasRainbowAP (k := k) c

/-- The canonical van der Waerden number `H(k)`: the least canonical `N` (`0` if none). -/
noncomputable def H (k : ℕ) : ℕ := sInf {N | Canonical N k}

/-- **Erdős Problem 190 (statement about canonical `N`).**  For every `C` there is `K` such that
for all `k ≥ K`, every `N` for which `[N]` is canonical for `k` satisfies `(Ck)^k < N`.
By itself this does not mention `H`; together with the existence of a canonical `N` for every
`k` (Erdős–Graham, not formalized; the hypothesis of `H_divergence`) it gives `H(k) > (Ck)^k`
for all large `k`, i.e. `H(k)^{1/k}/k → ∞`. -/
theorem divergence (C : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ N, Canonical N k → (C * k) ^ k < N := by
  sorry

/-- `Filter.Eventually` form of `divergence` (again a statement about canonical `N` only). -/
theorem divergence_eventually (C : ℕ) :
    ∀ᶠ k in atTop, ∀ N, Canonical N k → (C * k) ^ k < N := by
  sorry

/-- The conclusion for `H(k)` itself: **assuming** a canonical `N` exists for every `k`
(the Erdős–Graham theorem, taken as a hypothesis), `(Ck)^k < H(k)` for all large `k`, i.e.
`H(k)^{1/k}/k → ∞`.  Without the hypothesis, for a `k` with no canonical `N` one has
`H k = sInf ∅ = 0`, and no conclusion about `H k` is available from `divergence`. -/
theorem H_divergence (hH : ∀ k, {N | Canonical N k}.Nonempty) (C : ℕ) :
    ∀ᶠ k in atTop, (C * k) ^ k < H k := by
  sorry

/-- The explicit bound: for `k ≥ 12` there is a prime `p` with `(k-1)/2 < p ≤ k-1` such that every
canonical `N` exceeds `p^(p - ⌊k/3⌋) · ⌊⌊k/3⌋^(k-1) / (16 k²)⌋` (integer divisions). -/
theorem explicit_bound (k : ℕ) (hk : 12 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ (k - 1) / 2 < p ∧ p ≤ k - 1 ∧
      ∀ N, Canonical N k → p ^ (p - k / 3) * ((k / 3) ^ (k - 1) / (16 * k ^ 2)) < N := by
  sorry

end Erdos190.Palomar
