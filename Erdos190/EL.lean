import Erdos190.Defs
import Erdos190.Uniform

/-!
# The Erdős–Lovász base via the Local Lemma

For `r ≥ 2`, `k ≥ 4` and `N = r^(k-1) / (16 k^2)` there is an `r`-colouring of `Fin N` with no
monochromatic `k`-AP.  (The constant is cruder than in the paper; only the shape `r^(k-1)/poly(k)`
matters.)
-/

namespace Erdos190

open MeasureTheory ProbabilityTheory Finset ProbMethodCombinatorics

section APBasics

variable {N k : ℕ}

theorem AP.term_injective (P : AP N k) : Function.Injective P.term := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [AP.term] at h'
  have hd := P.d_pos
  have : i.1 * P.d = j.1 * P.d := by omega
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd this)

/-- The set of terms of an AP. -/
def AP.terms (P : AP N k) : Finset (Fin N) := Finset.univ.image P.term

theorem AP.card_terms (P : AP N k) : P.terms.card = k := by
  rw [AP.terms, Finset.card_image_of_injective _ P.term_injective, Finset.card_univ,
    Fintype.card_fin]

theorem AP.term_mem_terms (P : AP N k) (i : Fin k) : P.term i ∈ P.terms :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- Validity of a pair `(a,d)` as a `k`-AP in `[N]`. -/
def validPair (N k : ℕ) (q : Fin N × Fin N) : Prop := 0 < q.2.1 ∧ q.1.1 + (k - 1) * q.2.1 < N

instance (q : Fin N × Fin N) : Decidable (validPair N k q) := by
  unfold validPair; infer_instance

/-- The AP attached to a valid pair. -/
def toAP (q : Fin N × Fin N) (h : validPair N k q) : AP N k := ⟨q.1.1, q.2.1, h.1, h.2⟩

/-- Every AP comes from a valid pair (for `k ≥ 2`). -/
theorem exists_pair (hk : 2 ≤ k) (P : AP N k) :
    ∃ q : Fin N × Fin N, ∃ h : validPair N k q, toAP q h = P := by
  have ha : P.a < N := by
    have := P.last_lt; have := P.d_pos; nlinarith
  have hd : P.d < N := by
    have := P.last_lt
    have h1 : 1 ≤ k - 1 := by omega
    nlinarith [Nat.mul_le_mul_right P.d h1]
  refine ⟨(⟨P.a, ha⟩, ⟨P.d, hd⟩), ⟨P.d_pos, P.last_lt⟩, ?_⟩
  rfl

end APBasics

section LocalLemmaApplication

variable (N r k : ℕ) [NeZero r]

/-- The monochromatic event of a pair (empty for invalid pairs). -/
def monoEvent (q : Fin N × Fin N) : Set (Fin N → Fin r) :=
  if h : validPair N k q then
    {x | ∀ i j : Fin k, x ((toAP q h).term i) = x ((toAP q h).term j)}
  else ∅

/-- Neighbourhood: valid pairs whose AP shares a term with the AP of `q`. -/
def nbhd (q : Fin N × Fin N) : Finset (Fin N × Fin N) :=
  if h : validPair N k q then
    Finset.univ.filter (fun q' => ∃ h' : validPair N k q',
      ∃ i j : Fin k, (toAP q' h').term i = (toAP q h).term j)
  else ∅

variable {N r k}

theorem monoEvent_subset_iUnion (q : Fin N × Fin N) (h : validPair N k q) :
    monoEvent N r k q ⊆ ⋃ b : Fin r, {x : Fin N → Fin r | ∀ u ∈ (toAP q h).terms, x u = b} := by
  intro x hx
  rw [monoEvent, dif_pos h] at hx
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine Set.mem_iUnion.2 ⟨⟨0, NeZero.pos r⟩, ?_⟩
    intro u hu
    exact absurd hu (by simp [AP.terms])
  · refine Set.mem_iUnion.2 ⟨x ((toAP q h).term ⟨0, hk⟩), ?_⟩
    intro u hu
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
    exact hx i ⟨0, hk⟩

/-- Probability of a monochromatic `k`-AP: at most `r * r^{-k} = r^{1-k}`. -/
theorem measure_monoEvent_le (q : Fin N × Fin N) :
    (uniformRColoring (Fin N) r (monoEvent N r k q)).toReal ≤ (r : ℝ) * ((r : ℝ)⁻¹) ^ k := by
  by_cases h : validPair N k q
  · have hsub := monoEvent_subset_iUnion (r := r) q h
    calc (uniformRColoring (Fin N) r (monoEvent N r k q)).toReal
        ≤ (uniformRColoring (Fin N) r
            (⋃ b : Fin r, {x : Fin N → Fin r | ∀ u ∈ (toAP q h).terms, x u = b})).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          exact measure_mono hsub
      _ ≤ (∑ b : Fin r, uniformRColoring (Fin N) r
            {x : Fin N → Fin r | ∀ u ∈ (toAP q h).terms, x u = b}).toReal := by
          apply ENNReal.toReal_mono
          · exact ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _
          · exact measure_iUnion_fintype_le _ _
      _ = ∑ b : Fin r, (((r : ENNReal))⁻¹ ^ k).toReal := by
          rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
          congr 1; ext b
          rw [uniformRColoring_const, AP.card_terms]
      _ = (r : ℝ) * ((r : ℝ)⁻¹) ^ k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · rw [monoEvent, dif_neg h]
    simp only [measure_empty, ENNReal.toReal_zero]
    positivity

/-- Degree bound: `|nbhd q| ≤ k * k * N`. -/
theorem card_nbhd_le (q : Fin N × Fin N) : (nbhd N k q).card ≤ k * k * N := by
  by_cases h : validPair N k q
  · rw [nbhd, dif_pos h]
    classical
    -- every neighbour `q'` is determined by (index `i` in `q'`, index `j` in `q`, difference):
    -- `q'.a = (toAP q h).term j - i * q'.d`.
    let g : Fin k × Fin k × Fin N → Fin N × Fin N := fun t =>
      (⟨((toAP q h).term t.2.1).1 - t.1.1 * t.2.2.1,
        lt_of_le_of_lt (Nat.sub_le _ _) ((toAP q h).term t.2.1).2⟩, t.2.2)
    have hsub : (Finset.univ.filter (fun q' => ∃ h' : validPair N k q',
        ∃ i j : Fin k, (toAP q' h').term i = (toAP q h).term j)) ⊆ Finset.univ.image g := by
      intro q' hq'
      rw [Finset.mem_filter] at hq'
      obtain ⟨-, h', i, j, hij⟩ := hq'
      rw [Finset.mem_image]
      refine ⟨(i, j, q'.2), Finset.mem_univ _, ?_⟩
      have hval := congrArg Fin.val hij
      simp only [AP.term, toAP] at hval
      ext
      · simp only [g]
        show ((toAP q h).term j).1 - i.1 * q'.2.1 = q'.1.1
        simp only [AP.term, toAP]
        omega
      · rfl
    calc (Finset.univ.filter _).card ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin k × Fin k × Fin N)).card := Finset.card_image_le
      _ = k * k * N := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc]
  · rw [nbhd, dif_neg h]; simp

end LocalLemmaApplication

end Erdos190

namespace Erdos190

open MeasureTheory ProbabilityTheory Finset ProbMethodCombinatorics

section LLLApply

variable {N r k : ℕ} [NeZero r]

/-- The monochromatic events with the sharing-a-term neighbourhoods form a dependency graph
for the uniform colouring. -/
theorem isDependencyGraph_mono :
    IsDependencyGraph (uniformRColoring (Fin N) r) (monoEvent N r k) (nbhd N k) := by
  intro q s hs f
  by_cases h : validPair N k q
  · apply uniformRColoring_inter_eq_mul r (toAP q h).terms
    · intro x y hxy
      rw [monoEvent, dif_pos h]
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hh i j
        rw [← hxy _ (AP.term_mem_terms _ i), ← hxy _ (AP.term_mem_terms _ j)]
        exact hh i j
      · intro hh i j
        rw [hxy _ (AP.term_mem_terms _ i), hxy _ (AP.term_mem_terms _ j)]
        exact hh i j
    · intro x y hxy
      simp only [pattern, Set.mem_iInter]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro hj
      have hdisj : ∀ h' : validPair N k j, ∀ i i' : Fin k,
          (toAP j h').term i ≠ (toAP q h).term i' := by
        intro h' i i' heq
        have hnot := (hs j hj).2
        rw [nbhd, dif_pos h, Finset.mem_filter] at hnot
        exact hnot ⟨Finset.mem_univ _, h', i, i', heq⟩
      have hAj : x ∈ monoEvent N r k j ↔ y ∈ monoEvent N r k j := by
        by_cases h' : validPair N k j
        · rw [monoEvent, dif_pos h']
          simp only [Set.mem_setOf_eq]
          have hout : ∀ i, (toAP j h').term i ∉ (toAP q h).terms := by
            intro i hmem
            obtain ⟨i', -, heq⟩ := Finset.mem_image.1 hmem
            exact hdisj h' i i' heq.symm
          constructor
          · intro hh i i'
            rw [← hxy _ (hout i), ← hxy _ (hout i')]
            exact hh i i'
          · intro hh i i'
            rw [hxy _ (hout i), hxy _ (hout i')]
            exact hh i i'
        · rw [monoEvent, dif_neg h']
          simp
      split_ifs
      · exact hAj
      · simp only [Set.mem_compl_iff]
        exact not_congr hAj
  · rw [monoEvent, dif_neg h]
    simp

/-- The Local Lemma condition `e * p * (d + 1) ≤ 1` for `p = r^(1-k)`, `d = k² N`,
`N = r^(k-1) / (16 k²)`, `r ≥ 2`, `k ≥ 4`. -/
theorem lll_condition (hr : 2 ≤ r) (hk : 4 ≤ k) :
    Real.exp 1 * ((r : ℝ) * ((r : ℝ)⁻¹) ^ k) *
      ((k * k * (r ^ (k - 1) / (16 * k ^ 2)) : ℕ) + 1) ≤ 1 := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  set R : ℝ := (r : ℝ) ^ (k - 1) with hR
  have hRpos : 0 < R := pow_pos hrpos _
  have hR8 : (8 : ℝ) ≤ R := by
    have h1 : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (k - 1) ≤ (r : ℝ) ^ (k - 1) :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hr) _
    rw [hR]; linarith [h1, h2]
  -- p = R⁻¹
  have hp : (r : ℝ) * ((r : ℝ)⁻¹) ^ k = R⁻¹ := by
    have hk1 : k = (k - 1) + 1 := by omega
    rw [hR, ← inv_pow]
    conv_lhs => rw [hk1]
    rw [pow_succ]
    field_simp
  -- D := k² N ≤ R / 16
  set D : ℕ := k * k * (r ^ (k - 1) / (16 * k ^ 2)) with hD
  have hD16 : (16 : ℝ) * D ≤ R := by
    have hdiv : 16 * k ^ 2 * (r ^ (k - 1) / (16 * k ^ 2)) ≤ r ^ (k - 1) :=
      Nat.mul_div_le _ _
    have : (16 * D : ℕ) ≤ r ^ (k - 1) := by
      rw [hD]; calc 16 * (k * k * (r ^ (k - 1) / (16 * k ^ 2)))
          = 16 * k ^ 2 * (r ^ (k - 1) / (16 * k ^ 2)) := by ring
        _ ≤ r ^ (k - 1) := hdiv
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast at this
    rw [hR]; exact this
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp0 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [hp]
  have hDnn : (0 : ℝ) ≤ D := by positivity
  rw [show Real.exp 1 * R⁻¹ * ((D : ℝ) + 1) = Real.exp 1 * ((D : ℝ) + 1) / R by ring,
    div_le_one hRpos]
  nlinarith [mul_le_mul_of_nonneg_left hD16 hexp0.le, hR8, hexp, hexp0, hDnn]

/-- **Erdős–Lovász base**: for `r ≥ 2`, `k ≥ 4` there is an `r`-colouring of
`[r^(k-1) / (16 k²)]` with no monochromatic `k`-AP. -/
theorem el_base (r k : ℕ) (hr : 2 ≤ r) (hk : 4 ≤ k) :
    ∃ c : Fin (r ^ (k - 1) / (16 * k ^ 2)) → Fin r, ¬ HasMonoAP (k := k) c := by
  haveI : NeZero r := ⟨by omega⟩
  have hpos := lovasz_local_lemma_symmetric (μ := uniformRColoring (Fin (r ^ (k - 1) / (16 * k ^ 2))) r)
    (monoEvent (r ^ (k - 1) / (16 * k ^ 2)) r k) (fun _ => (Set.toFinite _).measurableSet)
    (nbhd (r ^ (k - 1) / (16 * k ^ 2)) k) isDependencyGraph_mono
    (p := (r : ℝ) * ((r : ℝ)⁻¹) ^ k) (d := k * k * (r ^ (k - 1) / (16 * k ^ 2)))
    (fun q => measure_monoEvent_le q) (fun q => card_nbhd_le q)
    (by
      have := lll_condition (r := r) (k := k) hr hk
      push_cast at this ⊢
      exact this)
  obtain ⟨x, hx⟩ : (⋂ q, (monoEvent (r ^ (k - 1) / (16 * k ^ 2)) r k q)ᶜ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hpos
    simp at hpos
  refine ⟨x, ?_⟩
  rintro ⟨P, hP⟩
  obtain ⟨q, hq, rfl⟩ := exists_pair (by omega) P
  have hxq := Set.mem_iInter.1 hx q
  apply hxq
  rw [monoEvent, dif_pos hq]
  exact hP

end LLLApply

end Erdos190
