import Mathlib
import Lean
import Std
import DiscreteMath.Probability.Utils

open Lean

open BigOperators Set Function

namespace Discrete
  class Probability (Ω : Type)
    [Fintype Ω] [instDecEq : DecidableEq Ω]
    where -- all subsets are events
    -- instDec : ∀ a b : Ω, Decidable (a = b)
    pmf : Ω → ℝ
    pmf_positive : ∀ ω : Ω, pmf ω ≥ 0
    pmf_bounded_above : ∀ ω : Ω, pmf ω ≤ 1
    prob : Finset Ω → ℝ
    unit_additive : ∀ E : Finset Ω, prob E = ∑ ω in E, pmf ω
    positiveness : ∀ E : Finset Ω, prob E ≥ 0
    empty_set_prob : prob ∅ = 0
    total_prob : prob Finset.univ = 1
    two_add : ∀ (A B : Finset Ω), prob (A ∪ B) = prob A + prob B - prob (A ∩ B)



  open Probability

  --
  /-
  class RandomVariable
    (Ω : Type) [inst: Fintype Ω]
    [Probability Ω] where
    RVmap : Ω → ℝ
    probR  : Finset ℝ → ℝ
    probRule : ∀ E : Finset ℝ, probR E = Ω.prob ({x : Ω | RVmap x ∈ E})
  -- def probRV
  -/
  def IndexedFamilySets (Ω : Type)
    [DecidableEq Ω] (n : ℕ) := Fin n → Finset Ω

  def pairwiseDisjoint [DecidableEq Ω]
    (S : IndexedFamilySets Ω n) := ∀ i j : Fin n, S i ∩ S j = ∅


  variable (Ω : Type) [instDecEq: DecidableEq Ω]
    [instFin : Fintype Ω] [instProb : Probability Ω]


  @[simp]
  lemma all_positive : ∀ E : Finset Ω, prob E ≥ 0 :=  by
    intro E
    apply positiveness
    done

  lemma subset_split {α : Type} [DecidableEq α] {E F : Finset α} :
    E ⊆ F → F = E ∪ (F \ E) := by
    --simp? [Finset.subset_def]
    simp only [
      Finset.subset_def,
      Finset.union_sdiff_self_eq_union,
      Finset.right_eq_union,
      imp_self
    ]

  @[simp]
  lemma subset_split_disjoint {α : Type} [DecidableEq α] {E F : Finset α} :
    E ⊆ F → E ∩ (F \ E) = ∅ := by
    --simp? [Finset.subset_def]
    simp only [
      Finset.subset_def,
      Finset.inter_sdiff_self,
      implies_true
    ]

  lemma monotonicity :
    ∀ E F : Finset Ω, E ⊆ F → prob E ≤ prob F := by
    intros E F subsetH
    have subsetH' := subsetH
    apply subset_split at subsetH
    rw [unit_additive, unit_additive]
    have h := @pmf_positive Ω instFin instDecEq instProb
    simp at h
    rw [subsetH]
    have _ : E ∩ (F \ E) = ∅ := by
      apply (@subset_split_disjoint Ω instDecEq E F)
      exact subsetH'
    rw[Finset.sum_union]
    · simp
      apply Finset.sum_nonneg
      intro i _
      exact h i
    · exact Finset.disjoint_sdiff
    done


  lemma all_smaller_one : ∀ E : Finset Ω, prob E ≤ 1 := by
    intro E
    have E_subset_univ : E ⊆ Finset.univ := by
      simp only [Finset.subset_univ]
    simp [←(@total_prob Ω)]
    apply monotonicity
    assumption
    done

  lemma union_bound_twoset :
    ∀ E F : Finset Ω,
      prob (E ∪ F) ≤ prob E + prob F := by
    intro E F
    have this : prob (E ∪ F) = prob E + prob F - prob (E ∩ F) := by
      apply two_add
      done
    rw [this]
    simp
    done

  #eval (1 : Fin 1)



  lemma union_bound :
    ∀ n : ℕ,
    ∀ E : (Fin n → Finset Ω),
      @prob Ω instFin instDecEq instProb (⋃ i, E i).toFinset ≤ ∑ i, prob (E i) := by
    intro n E
    induction n with
    | zero =>
        simp_all
        rw [empty_set_prob]
    | succ n ih =>
        simp [(indexed_union_induct Ω n E)]

        have s₁ :
          prob (toFinset (⋃ i, ↑(E (Fin.castSucc i))) ∪ E (↑n + 1)) ≤  prob (toFinset (⋃ i, (E (Fin.castSucc i)).toSet)) + prob (E (↑n + 1)) := by
            apply union_bound_twoset

        have s₂ : prob (toFinset (⋃ i, (E (Fin.castSucc i)).toSet)) ≤  ∑ i : Fin n, prob (E i) := by
          simp[ih]
        have s₃ : prob (toFinset (⋃ i, (E (Fin.castSucc i)).toSet)) +  prob (E (↑n + 1)) ≤  ∑ i : Fin n, prob (E i) + prob (E (↑n + 1)) := by
          linarith [s₂]
        have s₄ : ∑ i : Fin n, prob (E ↑↑i) + prob (E (↑n + 1)) = ∑ i : Fin (n + 1), prob (E i) := by
          simp[indexed_finset_sum]
        have s₅ : prob (toFinset (⋃ i, ↑(E (Fin.castSucc i))) ∪ E (↑n + 1)) ≤ ∑ i : Fin n, prob (E ↑↑i) + prob (E (↑n + 1)) := by
          trans prob (toFinset (⋃ i, (E (Fin.castSucc i)).toSet)) + prob (E (↑n + 1))
          exact s₁
          exact s₃
          done
        rw [s₄] at s₅
        exact s₅









end Discrete
