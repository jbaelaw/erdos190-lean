import Erdos190.Defs

/-!
# The Blankenship–Cummings–Taranchuk recurrence (restricted form)

For a prime `p` and `2 ≤ r ≤ p ≤ k`: from an `(r-1)`-colouring of `[M]` without monochromatic
`k`-AP we build an `r`-colouring of `[p*M]` without monochromatic `k`-AP.  Hence
`W(r,k) - 1 ≥ p * (W(r-1,k) - 1)`.

Construction: write `i ∈ [p*M]` as `i = j*p + s` (`j = i / p`, `s = i % p`).  Give `i` the new
colour `r-1` if `s = c₀ j`, and the old colour `c₀ j` otherwise.
-/

namespace Erdos190

/-- The block colouring. -/
def bctColor {M p r : ℕ} (hp : 0 < p) (c₀ : Fin M → Fin (r - 1)) (hr : 2 ≤ r)
    (i : Fin (p * M)) : Fin r :=
  let j : Fin M := ⟨i.1 / p, Nat.div_lt_of_lt_mul i.2⟩
  if i.1 % p = (c₀ j).1 then ⟨r - 1, by omega⟩ else ⟨(c₀ j).1, by have := (c₀ j).2; omega⟩

theorem bctColor_new {M p r : ℕ} (hp : 0 < p) (c₀ : Fin M → Fin (r - 1)) (hr : 2 ≤ r)
    (i : Fin (p * M)) (j : Fin M) (hj : (j : ℕ) = i.1 / p) :
    (bctColor hp c₀ hr i : ℕ) = r - 1 ↔ i.1 % p = (c₀ j).1 := by
  unfold bctColor
  have hjj : (⟨i.1 / p, Nat.div_lt_of_lt_mul i.2⟩ : Fin M) = j :=
    Fin.ext hj.symm
  simp only [hjj]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    have := (c₀ j).2
    omega

theorem bctColor_old {M p r : ℕ} (hp : 0 < p) (c₀ : Fin M → Fin (r - 1)) (hr : 2 ≤ r)
    (i : Fin (p * M)) (j : Fin M) (hj : (j : ℕ) = i.1 / p) (v : ℕ) (hv : v < r - 1) :
    (bctColor hp c₀ hr i : ℕ) = v ↔ (i.1 % p ≠ (c₀ j).1 ∧ (c₀ j).1 = v) := by
  unfold bctColor
  have hjj : (⟨i.1 / p, Nat.div_lt_of_lt_mul i.2⟩ : Fin M) = j :=
    Fin.ext hj.symm
  simp only [hjj]
  split_ifs with h
  · simp only [h, ne_eq, not_true_eq_false, false_and, iff_false]
    omega
  · simp [h]

end Erdos190

namespace Erdos190

/-- Block index of a term of an AP in `[p*M]` whose difference is divisible by `p`. -/
theorem bct_block_ap {M p k : ℕ} (hp : 0 < p) (P : AP (p * M) k) (hd : p ∣ P.d) :
    ∃ Q : AP M k, ∀ i : Fin k, (Q.term i : ℕ) = (P.term i : ℕ) / p ∧
      (P.term i : ℕ) % p = P.a % p := by
  obtain ⟨e, he⟩ := hd
  have he_pos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he; exact absurd he (Nat.pos_iff_ne_zero.mp P.d_pos)
    · exact h
  refine ⟨⟨P.a / p, e, he_pos, ?_⟩, fun i => ?_⟩
  · have hlast := P.last_lt
    rw [he] at hlast
    -- a/p + (k-1) e < M  since a + (k-1) p e < p M
    have : P.a / p * p ≤ P.a := Nat.div_mul_le_self _ _
    have h2 : (P.a / p + (k - 1) * e) * p < M * p := by
      calc (P.a / p + (k - 1) * e) * p = P.a / p * p + (k - 1) * (p * e) := by ring
        _ ≤ P.a + (k - 1) * (p * e) := by omega
        _ < p * M := hlast
        _ = M * p := Nat.mul_comm p M
    exact Nat.lt_of_mul_lt_mul_right h2
  · simp only [AP.term, he]
    constructor
    · -- (a + i*(p*e)) / p = a/p + i*e
      rw [show P.a + i.1 * (p * e) = P.a + p * (i.1 * e) by ring, Nat.add_mul_div_left _ _ hp]
    · rw [show P.a + i.1 * (p * e) = P.a + p * (i.1 * e) by ring, Nat.add_mul_mod_self_left]

/-- Among the first `p` terms of an AP whose difference is coprime to the prime `p`, every
residue mod `p` occurs. -/
theorem bct_residues {N k p : ℕ} (hp : p.Prime) (hpk : p ≤ k) (P : AP N k) (hd : ¬ p ∣ P.d)
    (s : ℕ) (hs : s < p) : ∃ i : Fin k, (P.term i : ℕ) % p = s := by
  haveI := Fact.mk hp
  -- work in ZMod p
  have hdz : (P.d : ZMod p) ≠ 0 := by
    intro h; exact hd ((ZMod.natCast_eq_zero_iff P.d p).1 h)
  set t : ZMod p := ((s : ZMod p) - (P.a : ZMod p)) * (P.d : ZMod p)⁻¹ with ht
  have hi : t.val < k := lt_of_lt_of_le (ZMod.val_lt t) hpk
  refine ⟨⟨t.val, hi⟩, ?_⟩
  simp only [AP.term]
  -- (a + t.val * d) ≡ s (mod p)
  have key : ((P.a + t.val * P.d : ℕ) : ZMod p) = (s : ZMod p) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ht, mul_assoc, inv_mul_cancel₀ hdz, mul_one]
    ring
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 key
  rw [Nat.mod_eq_of_lt hs] at this
  exact this

/-- **Restricted BCT**: from an `(r-1)`-colouring of `[M]` with no monochromatic `k`-AP we obtain
an `r`-colouring of `[p*M]` with no monochromatic `k`-AP, for `p` prime and `2 ≤ r ≤ p ≤ k`. -/
theorem bct_step {M p r k : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hrp : r ≤ p) (hpk : p ≤ k)
    (c₀ : Fin M → Fin (r - 1)) (h₀ : ¬ HasMonoAP (k := k) c₀) :
    ∃ c : Fin (p * M) → Fin r, ¬ HasMonoAP (k := k) c := by
  have hp0 : 0 < p := hp.pos
  refine ⟨bctColor hp0 c₀ hr, ?_⟩
  rintro ⟨P, hP⟩
  -- helper: the block index of a term
  have hblk : ∀ i : Fin k, ((P.term i : ℕ) / p) < M := fun i =>
    Nat.div_lt_of_lt_mul (P.term i).2
  by_cases hd : p ∣ P.d
  · -- Case 1: constant residue; project to an AP in [M]
    obtain ⟨Q, hQ⟩ := bct_block_ap hp0 P hd
    have hc0 : ∀ i j : Fin k, c₀ (Q.term i) = c₀ (Q.term j) := by
      intro i j
      have hij := hP i j
      -- all terms have the same residue `P.a % p`
      by_cases hnew : (bctColor hp0 c₀ hr (P.term i) : ℕ) = r - 1
      · -- new colour everywhere: residue = c₀ of block, so c₀ constant
        have hi := (bctColor_new hp0 c₀ hr (P.term i) (Q.term i) (hQ i).1).1 hnew
        have hnewj : (bctColor hp0 c₀ hr (P.term j) : ℕ) = r - 1 := by rw [← hij]; exact hnew
        have hj := (bctColor_new hp0 c₀ hr (P.term j) (Q.term j) (hQ j).1).1 hnewj
        apply Fin.ext
        rw [← hi, ← hj, (hQ i).2, (hQ j).2]
      · -- old colour v everywhere
        set v := (bctColor hp0 c₀ hr (P.term i) : ℕ) with hv
        have hvlt : v < r - 1 := by
          have := (bctColor hp0 c₀ hr (P.term i)).2
          omega
        have hi := ((bctColor_old hp0 c₀ hr (P.term i) (Q.term i) (hQ i).1 v hvlt).1 rfl).2
        have hvj : (bctColor hp0 c₀ hr (P.term j) : ℕ) = v := by rw [hv, hij]
        have hj := ((bctColor_old hp0 c₀ hr (P.term j) (Q.term j) (hQ j).1 v hvlt).1 hvj).2
        apply Fin.ext
        rw [hi, hj]
    exact h₀ ⟨Q, hc0⟩
  · -- Case 2: residues cover everything among the first p terms
    have hcolor : ∀ i j : Fin k, (bctColor hp0 c₀ hr (P.term i) : ℕ)
        = (bctColor hp0 c₀ hr (P.term j) : ℕ) := fun i j => by rw [hP i j]
    have hk0 : 0 < k := by omega
    set i0 : Fin k := ⟨0, hk0⟩ with hi0
    set v := (bctColor hp0 c₀ hr (P.term i0) : ℕ) with hv
    by_cases hnew : v = r - 1
    · -- new colour everywhere; take the term with residue p-1 ≥ r-1 > c₀ value
      obtain ⟨i, hi⟩ := bct_residues hp hpk P hd (p - 1) (by omega)
      have hci : (bctColor hp0 c₀ hr (P.term i) : ℕ) = r - 1 := by rw [hcolor i i0, ← hv, hnew]
      have := (bctColor_new hp0 c₀ hr (P.term i) ⟨(P.term i : ℕ) / p, hblk i⟩ rfl).1 hci
      have hc := (c₀ ⟨(P.term i : ℕ) / p, hblk i⟩).2
      omega
    · -- old colour v everywhere; take the term with residue v: it must be new
      have hvlt : v < r - 1 := by
        have := (bctColor hp0 c₀ hr (P.term i0)).2
        omega
      obtain ⟨i, hi⟩ := bct_residues hp hpk P hd v (by omega)
      have hci : (bctColor hp0 c₀ hr (P.term i) : ℕ) = v := by rw [hcolor i i0]
      have := (bctColor_old hp0 c₀ hr (P.term i) ⟨(P.term i : ℕ) / p, hblk i⟩ rfl v hvlt).1 hci
      exact this.1 (by rw [hi, this.2])

end Erdos190
