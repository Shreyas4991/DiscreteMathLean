import Mathlib

open BigOperators

namespace Discrete
  lemma indexed_finset_sum [Ring α] :
    ∀ n : ℕ, ∀ F : (Fin (n + 1) → α),
    ∑ i : Fin (n+1), F i = (∑ i : Fin n, F i) + (F (n+1)) := by
      intro n F
      induction n with
      | zero =>
          norm_num
          sorry
      | succ n ih => sorry
      done

  lemma indexed_union_induct (α : Type u) :
    ∀ n : ℕ, ∀ E : (Fin (n + 1) → Finset α),
    (⋃ i, (E i).toSet) = ((⋃ (i : Fin n), (E i).toSet) ∪ E (n + 1)) := by
    sorry
end Discrete
