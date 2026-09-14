import Erdos190.Defs

/-!
# Pigeonhole reduction `H(k) ≥ W(k-1,k)` and monotonicity in the number of colours
-/

namespace Erdos190

open Function

/-- A colouring with fewer than `k` colours has no rainbow `k`-AP. -/
theorem not_hasRainbowAP_of_card_lt {N k r : ℕ} (c : Fin N → Fin r) (hrk : r < k) :
    ¬ HasRainbowAP (k := k) c := by
  rintro ⟨P, hP⟩
  have hinj : Injective (fun i : Fin k => c (P.term i)) := fun i j h => hP i j h
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

/-- Monochromatic APs are preserved under composing with an injective recolouring. -/
theorem hasMonoAP_of_comp_injective {N k : ℕ} {κ κ' : Type*} (c : Fin N → κ) (f : κ → κ')
    (hf : Injective f) (h : HasMonoAP (k := k) (f ∘ c)) : HasMonoAP (k := k) c := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun i j => hf (hP i j)⟩

/-- `H(k) ≥ W(k-1,k)`: if `[N]` is canonical for `k` then every `(k-1)`-colouring of `[N]`
has a monochromatic `k`-AP. -/
theorem forces_of_canonical {N k : ℕ} (hk : 1 ≤ k) (h : Canonical N k) : Forces N (k - 1) k := by
  intro c
  have hinj : Injective (fun x : Fin (k - 1) => (x : ℕ)) := Fin.val_injective
  rcases h (fun x => (c x : ℕ)) with hm | hr
  · exact hasMonoAP_of_comp_injective c _ hinj hm
  · exfalso
    have hlt : k - 1 < k := by omega
    exact not_hasRainbowAP_of_card_lt (k := k) (r := k - 1) c hlt (by
      obtain ⟨P, hP⟩ := hr
      exact ⟨P, fun i j hij => hP i j (by simpa using congrArg Fin.val hij)⟩)

/-- Monotonicity in the number of colours: if every `r'`-colouring is forced, so is every
`r`-colouring for `r ≤ r'`. -/
theorem forces_mono {N k r r' : ℕ} (hrr : r ≤ r') (h : Forces N r' k) : Forces N r k := by
  intro c
  have hinj : Injective (Fin.castLE hrr) := Fin.castLE_injective hrr
  exact hasMonoAP_of_comp_injective c (Fin.castLE hrr) hinj (h _)

/-- Contrapositive form used for lower bounds: a `p`-colouring of `[N]` (with `p ≤ k-1`)
without monochromatic `k`-APs shows that `[N]` is not canonical. -/
theorem not_canonical_of_coloring {N k p : ℕ} (hk : 1 ≤ k) (hp : p ≤ k - 1)
    (c : Fin N → Fin p) (hc : ¬ HasMonoAP (k := k) c) : ¬ Canonical N k := by
  intro h
  exact hc (forces_mono hp (forces_of_canonical hk h) c)

end Erdos190
