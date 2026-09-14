# Erdős Problem #190 — Lean 4 formalization of the qualitative statement

Author: Ji Ho Bae (JRTI). Companion to arXiv:2604.20588 (v2). License: Apache-2.0.
Repository: https://github.com/jbaelaw/erdos190-lean (also shipped as arXiv ancillary files).

**Statement proved** (`Erdos190.erdos190`, file `Erdos190/Divergence.lean`):

```lean
theorem erdos190 (C : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ N, Canonical N k → (C * k) ^ k < N
```

where `Canonical N k` means: every colouring `Fin N → ℕ` (any number of colours) contains a
monochromatic or a rainbow `k`-term arithmetic progression (`Erdos190/Defs.lean`).  Since
`H(k)` is the least canonical `N`, this says `H(k) > (C k)^k` for all large `k`, for every `C`,
i.e. `H(k)^{1/k}/k → ∞` — the question of Erdős and Graham (Problem #190).

Explicit intermediate result (`Erdos190.main_combinatorial`, `Erdos190/Main.lean`): for `k ≥ 12`
there is a prime `p` with `(k-1)/2 < p ≤ k-1` such that every canonical `N` satisfies
`N > p^(p - ⌊k/3⌋) * (⌊k/3⌋^(k-1) / (16 k^2))`.

## Proof architecture (mirrors the paper, Bertrand version = Section 4.3)

| File | Content |
|---|---|
| `Defs.lean` | APs in `Fin N`, monochromatic / rainbow, `Canonical`, `Forces` |
| `Pigeonhole.lean` | `H(k) ≥ W(k-1,k)`; monotonicity in the number of colours |
| `Uniform.lean` | uniform random `r`-colouring (product measure), independence of events on disjoint coordinates |
| `EL.lean` | Erdős–Lovász base via the symmetric Lovász Local Lemma: for `r ≥ 2, k ≥ 4` an `r`-colouring of `[r^(k-1)/(16k²)]` with no monochromatic `k`-AP |
| `BCT.lean` | restricted Blankenship–Cummings–Taranchuk recurrence `W(r,k)-1 ≥ p (W(r-1,k)-1)` for primes `r ≤ p ≤ k` (block construction, residue argument in `ZMod p`) |
| `Main.lean` | Bertrand's postulate (Mathlib), iteration of BCT from `r₀ = ⌊k/3⌋` colours to `p` colours, explicit bound |
| `Divergence.lean` | elementary asymptotics: `(C k)^k < bound` for `k ≥ max(768, 2(4(C+1))^12)` |

The Local Lemma itself is imported from the Lean 4 / Mathlib project
[yidiq7/ProbMethodCombinatorics](https://github.com/yidiq7/ProbMethodCombinatorics)
(`ProbMethodCombinatorics.lovasz_local_lemma_symmetric`, fully proved there).
Bertrand's postulate is `Nat.exists_prime_lt_and_le_two_mul` from Mathlib.

## Verification

```
lake exe cache get && lake build      # Lean 4.33.0, Mathlib v4.33.0
```
`#print axioms Erdos190.erdos190` → `[propext, Classical.choice, Quot.sound]` (no `sorry`).

## What is *not* formalized

The explicit rate `H(k)^{1/k}/k ≥ (1/e − ε(k)) k/log k` of the main theorem uses the
Baker–Harman–Pintz prime-gap theorem, which is not available in Mathlib; the formalization
covers the qualitative resolution (Corollary 1.2 of the paper) via Bertrand's postulate with
`r₀ = ⌊k/3⌋` (Proposition 4.1 uses `r₀ = ⌊k/log k⌋` and gives the rate `√k/log k`; with
`r₀ = ⌊k/3⌋` the same argument gives `H(k)^{1/k}/k ≥ k^{1/6 - o(1)}`, which is all the
qualitative statement needs).

Formalized 2026-09-14.
