import Mathlib
import ProbMethodCombinatorics.LocalLemma

/-!
# The uniform random `r`-colouring of `Fin N`

Generalises `ProbMethodCombinatorics.uniformColoring` (two colours) to `r` colours.
-/

namespace Erdos190

open MeasureTheory ProbabilityTheory

/-- The uniform probability measure on `Fin r` (for `r ≥ 1`). -/
noncomputable def uniformFin (r : ℕ) : Measure (Fin r) :=
  ((Fintype.card (Fin r) : ENNReal))⁻¹ • Measure.count

theorem uniformFin_univ (r : ℕ) (hr : 0 < r) : uniformFin r Set.univ = 1 := by
  have hc : Measure.count (Set.univ : Set (Fin r)) = (r : ENNReal) := by
    rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    norm_cast
  rw [uniformFin, Measure.smul_apply, smul_eq_mul, Fintype.card_fin, hc]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hr.ne') (by simp)

theorem uniformFin_singleton (r : ℕ) (b : Fin r) : uniformFin r {b} = ((r : ENNReal))⁻¹ := by
  rw [uniformFin, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one,
    Fintype.card_fin]

/-- The uniform random `r`-colouring of `κ`: independent uniform colours in each coordinate. -/
noncomputable def uniformRColoring (κ : Type*) [Fintype κ] (r : ℕ) : Measure (κ → Fin r) :=
  Measure.pi fun _ : κ => uniformFin r

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

instance uniformFin_isProb (r : ℕ) [NeZero r] : IsProbabilityMeasure (uniformFin r) :=
  ⟨uniformFin_univ r (NeZero.pos r)⟩

instance uniformRColoring_isProb (r : ℕ) [NeZero r] :
    IsProbabilityMeasure (uniformRColoring κ r) := by
  rw [uniformRColoring]; infer_instance

/-- A uniform random colouring is constant equal to `b` on a finite set `T` with probability
`r ^ -|T|`. -/
theorem uniformRColoring_const (r : ℕ) [NeZero r] (T : Finset κ) (b : Fin r) :
    uniformRColoring κ r {x : κ → Fin r | ∀ u ∈ T, x u = b} = ((r : ENNReal))⁻¹ ^ T.card := by
  have hset : {x : κ → Fin r | ∀ u ∈ T, x u = b}
      = Set.univ.pi (fun a => if a ∈ T then ({b} : Set (Fin r)) else Set.univ) := by
    ext x
    constructor
    · intro h a _
      show x a ∈ (if a ∈ T then ({b} : Set (Fin r)) else Set.univ)
      by_cases ha : a ∈ T
      · rw [if_pos ha]; exact h a ha
      · rw [if_neg ha]; exact Set.mem_univ _
    · intro h u hu
      have hxu : x u ∈ (if u ∈ T then ({b} : Set (Fin r)) else Set.univ) := h u (Set.mem_univ u)
      rw [if_pos hu] at hxu
      exact hxu
  rw [hset, uniformRColoring, Measure.pi_pi]
  have hrew : ∀ a : κ, uniformFin r (if a ∈ T then ({b} : Set (Fin r)) else Set.univ)
      = if a ∈ T then ((r : ENNReal))⁻¹ else 1 := by
    intro a
    by_cases ha : a ∈ T
    · rw [if_pos ha, if_pos ha]; exact uniformFin_singleton r b
    · rw [if_neg ha, if_neg ha]; exact uniformFin_univ r (NeZero.pos r)
  rw [Finset.prod_congr rfl (fun a _ => hrew a), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- Events determined by disjoint sets of coordinates are independent. -/
theorem uniformRColoring_inter_eq_mul (r : ℕ) [NeZero r] (T : Finset κ)
    (S₁ S₂ : Set (κ → Fin r))
    (h₁ : ∀ x y : κ → Fin r, (∀ a ∈ T, x a = y a) → (x ∈ S₁ ↔ y ∈ S₁))
    (h₂ : ∀ x y : κ → Fin r, (∀ a ∉ T, x a = y a) → (x ∈ S₂ ↔ y ∈ S₂)) :
    uniformRColoring κ r (S₁ ∩ S₂) = uniformRColoring κ r S₁ * uniformRColoring κ r S₂ := by
  have hindep : iIndepFun (fun (a : κ) (x : κ → Fin r) => x a) (uniformRColoring κ r) := by
    rw [uniformRColoring]
    exact ProbabilityTheory.iIndepFun_pi (μ := fun _ : κ => uniformFin r)
      (X := fun _ : κ => (id : Fin r → Fin r)) (fun _ => aemeasurable_id)
  have hind := hindep.indepFun_finset T Tᶜ disjoint_compl_right
    (fun a => measurable_pi_apply a)
  have e₁ : (fun (x : κ → Fin r) (u : { a // a ∈ T }) => x (u : κ)) ⁻¹'
      ((fun (x : κ → Fin r) (u : { a // a ∈ T }) => x (u : κ)) '' S₁) = S₁ := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨y, hy, hxy⟩
    exact (h₁ y x (fun a ha => congrFun hxy ⟨a, ha⟩)).1 hy
  have e₂ : (fun (x : κ → Fin r) (u : { a // a ∈ Tᶜ }) => x (u : κ)) ⁻¹'
      ((fun (x : κ → Fin r) (u : { a // a ∈ Tᶜ }) => x (u : κ)) '' S₂) = S₂ := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨y, hy, hxy⟩
    exact (h₂ y x (fun a ha => congrFun hxy ⟨a, Finset.mem_compl.2 ha⟩)).1 hy
  have hmul := hind.measure_inter_preimage_eq_mul
    ((fun (x : κ → Fin r) (u : { a // a ∈ T }) => x (u : κ)) '' S₁)
    ((fun (x : κ → Fin r) (u : { a // a ∈ Tᶜ }) => x (u : κ)) '' S₂)
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  rw [e₁, e₂] at hmul
  exact hmul

end Erdos190
