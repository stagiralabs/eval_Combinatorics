import VerifiedAgora.tagger
/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Order.Partition.Equipartition

/-!
# Equitabilising a partition

This file allows to blow partitions up into parts of controlled size. Given a partition `P` and
`a b m : ℕ`, we want to find a partition `Q` with `a` parts of size `m` and `b` parts of size
`m + 1` such that all parts of `P` are "as close as possible" to unions of parts of `Q`. By
"as close as possible", we mean that each part of `P` can be written as the union of some parts of
`Q` along with at most `m` other elements.

## Main declarations

* `Finpartition.equitabilise`: `P.equitabilise h` where `h : a * m + b * (m + 1)` is a partition
  with `a` parts of size `m` and `b` parts of size `m + 1` which almost refines `P`.
* `Finpartition.exists_equipartition_card_eq`: We can find equipartitions of arbitrary size.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset Nat

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} {m n a b : ℕ} {P : Finpartition s}

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`, we can
find a new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the
union of parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and
(provided `m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size
`m` and hence `a + b` parts in total. -/
@[target] theorem equitabilise_aux (hs : a * m + b * (m + 1) = #s) :
    ∃ Q : Finpartition s,
      (∀ x : Finset α, x ∈ Q.parts → #x = m ∨ #x = m + 1) ∧
        (∀ x, x ∈ P.parts → #(x \ {y ∈ Q.parts | y ⊆ x}.biUnion id) ≤ m) ∧
          #{i ∈ Q.parts | #i = m + 1} = b := by sorry


variable (h : a * m + b * (m + 1) = #s)

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = #s`, build a
new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the union of
parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and (provided
`m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size `m` and
hence `a + b` parts in total. -/
noncomputable def equitabilise : Finpartition s :=
  (P.equitabilise_aux h).choose

variable {h}

@[target] theorem card_eq_of_mem_parts_equitabilise :
    t ∈ (P.equitabilise h).parts → #t = m ∨ #t = m + 1 := by sorry


@[target] theorem equitabilise_isEquipartition : (P.equitabilise h).IsEquipartition := by sorry


variable (P h)

@[target] theorem card_filter_equitabilise_big : #{u ∈ (P.equitabilise h).parts | #u = m + 1} = b := by sorry


theorem card_filter_equitabilise_small (hm : m ≠ 0) :
    #{u ∈ (P.equitabilise h).parts | #u = m} = a := by
  refine (mul_eq_mul_right_iff.1 <| (add_left_inj (b * (m + 1))).1 ?_).resolve_right hm
  rw [h, ← (P.equitabilise h).sum_card_parts]
  have hunion :
    (P.equitabilise h).parts =
      {u ∈ (P.equitabilise h).parts | #u = m} ∪ {u ∈ (P.equitabilise h).parts | #u = m + 1} := by
    rw [← filter_or, filter_true_of_mem]
    exact fun x => card_eq_of_mem_parts_equitabilise
  nth_rw 2 [hunion]
  rw [sum_union, sum_const_nat fun x hx => (mem_filter.1 hx).2,
    sum_const_nat fun x hx => (mem_filter.1 hx).2, P.card_filter_equitabilise_big]
  refine disjoint_filter_filter' _ _ ?_
  intro x ha hb i h
  apply succ_ne_self m _
  exact (hb i h).symm.trans (ha i h)

@[target] theorem card_parts_equitabilise (hm : m ≠ 0) : #(P.equitabilise h).parts = a + b := by sorry


theorem card_parts_equitabilise_subset_le :
    t ∈ P.parts → #(t \ {u ∈ (P.equitabilise h).parts | u ⊆ t}.biUnion id) ≤ m :=
  (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

variable (s)

/-- We can find equipartitions of arbitrary size. -/
@[target] theorem exists_equipartition_card_eq (hn : n ≠ 0) (hs : n ≤ #s) :
    ∃ P : Finpartition s, P.IsEquipartition ∧ #P.parts = n := by sorry


end Finpartition
