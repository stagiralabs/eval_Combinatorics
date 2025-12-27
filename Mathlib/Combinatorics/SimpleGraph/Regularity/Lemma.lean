import VerifiedAgora.tagger
/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Increment

/-!
# Szemerédi's Regularity Lemma

In this file, we prove Szemerédi's Regularity Lemma (aka SRL). This is a landmark result in
combinatorics roughly stating that any sufficiently big graph behaves like a random graph. This is
useful because random graphs are well-behaved in many aspects.

More precisely, SRL states that for any `ε > 0` and integer `l` there exists a bound `M` such that
any graph on at least `l` vertices can be partitioned into at least `l` parts and at most `M` parts
such that the resulting partitioned graph is `ε`-uniform.

This statement is very robust to tweaking and many different versions exist. Here, we prove the
version where the resulting partition is equitable (aka an *equipartition*), namely all parts have
the same size up to a difference of `1`.

The proof we formalise goes as follows:
1. Define an auxiliary measure of edge density, the *energy* of a partition.
2. Start with an arbitrary equipartition of size `l`.
3. Repeatedly break up the parts of the current equipartition in a big but controlled number of
  parts. The key point is to break along the witnesses of non-uniformity, so that a lesser portion
  of the pairs of parts are non-`ε`-uniform.
4. Check that this results in an equipartition with an energy greater than the energy of the current
  partition, plus some constant.
5. Since the energy is between zero and one, we can't run this process forever. Check that when the
  process stops we have an `ε`-uniform equipartition.

This file only contains the final result. The supporting material is spread across the
`Combinatorics/SimpleGraph/Regularity` folder:
* `Combinatorics/SimpleGraph/Regularity/Bound`: Definition of the bound on the number of parts.
  Numerical inequalities involving the lemma constants.
* `Combinatorics/SimpleGraph/Regularity/Energy`: Definition of the energy of a simple graph along a
  partition.
* `Combinatorics/SimpleGraph/Regularity/Uniform`: Definition of uniformity of a simple graph along
  a pair of parts and along a partition.
* `Combinatorics/SimpleGraph/Regularity/Equitabilise`: Construction of an equipartition with
  a prescribed number of parts of each size and almost refining a given partition.
* `Combinatorics/SimpleGraph/Regularity/Chunk`: Break up one part of the current equipartition.
  Check that density between non-uniform parts increases, and that density between uniform parts
  doesn't decrease too much.
* `Combinatorics/SimpleGraph/Regularity/Increment`: Gather all those broken up parts into the new
  equipartition (aka *increment partition*). Check that energy increases by at least a fixed amount.
* `Combinatorics/SimpleGraph/Regularity/Lemma`: Wrap everything up into an induction on the energy.

## TODO

We currently only prove the equipartition version of SRL.

* Prove the diagonal version.
* Prove the degree version.
* Define the regularity of a partition and prove the corresponding version.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finpartition Finset Fintype Function SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ}
  {l : ℕ}

/-- Effective **Szemerédi Regularity Lemma**: For any sufficiently large graph, there is an
`ε`-uniform equipartition of bounded size (where the bound does not depend on the graph). -/
@[target] theorem szemeredi_regularity (hε : 0 < ε) (hl : l ≤ card α) :
    ∃ P : Finpartition univ,
      P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ bound ε l ∧ P.IsUniform G ε := by sorry
