import VerifiedAgora.tagger
/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Diameter of a simple graph

This module defines the diameter of a simple graph, which measures the maximum distance between
vertices.

## Main definitions

- `SimpleGraph.ediam` is the graph extended diameter.

- `SimpleGraph.diam` is the graph diameter.

## Todo

- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1` when the diameter is
  non-zero.

-/

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

section ediam

/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  ⨆ u, ⨆ v, G.edist u v

lemma ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.2 := by
  rw [ediam, iSup_prod]

lemma edist_le_ediam {u v : α} : G.edist u v ≤ G.ediam :=
  le_iSup₂ (f := G.edist) u v

@[target] lemma ediam_le_of_edist_le {k : ℕ∞} (h : ∀ u v, G.edist u v ≤ k ) : G.ediam ≤ k := by sorry


@[target] lemma ediam_le_iff {k : ℕ∞} : G.ediam ≤ k ↔ ∀ u v, G.edist u v ≤ k := by sorry


lemma ediam_eq_top : G.ediam = ⊤ ↔ ∀ b < ⊤, ∃ u v, b < G.edist u v := by
  simp only [ediam, iSup_eq_top, lt_iSup_iff]

lemma ediam_eq_zero_of_subsingleton [Subsingleton α] : G.ediam = 0 := by
  rw [ediam_def, ENat.iSup_eq_zero]
  simpa [edist_eq_zero_iff, Prod.forall] using subsingleton_iff.mp ‹_›

@[target] lemma nontrivial_of_ediam_ne_zero (h : G.ediam ≠ 0) : Nontrivial α := by sorry


@[target] lemma ediam_ne_zero [Nontrivial α] : G.ediam ≠ 0 := by sorry


@[target] lemma subsingleton_of_ediam_eq_zero (h : G.ediam = 0) : Subsingleton α := by sorry


@[target] lemma ediam_ne_zero_iff_nontrivial :
    G.ediam ≠ 0 ↔ Nontrivial α := by sorry


@[target] lemma ediam_eq_zero_iff_subsingleton :
    G.ediam = 0 ↔ Subsingleton α := by sorry


@[target] lemma ediam_eq_top_of_not_connected [Nonempty α] (h : ¬G.Connected) : G.ediam = ⊤ := by sorry


@[target] lemma ediam_eq_top_of_not_preconnected (h : ¬G.Preconnected) : G.ediam = ⊤ := by sorry


lemma exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u v, G.edist u v = G.ediam :=
  ENat.exists_eq_iSup₂_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
lemma exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.ediam :=
  Prod.exists'.mp <| ediam_def ▸ exists_eq_ciSup_of_finite

@[gcongr]
lemma ediam_anti (h : G ≤ G') : G'.ediam ≤ G.ediam :=
  iSup₂_mono fun _ _ ↦ edist_anti h

@[simp]
lemma ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤ :=
  ediam_eq_top_of_not_connected bot_not_connected

@[target] lemma ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1 := by sorry


@[target] lemma ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by sorry


end ediam

section diam

/--
The diameter is the greatest distance between any two vertices, with the value `0` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat

@[target] lemma diam_def : G.diam = (⨆ p : α × α, G.edist p.1 p.2).toNat := by sorry


@[target] lemma dist_le_diam (h : G.ediam ≠ ⊤) {u v : α} : G.dist u v ≤ G.diam := by sorry


@[target] lemma nontrivial_of_diam_ne_zero (h : G.diam ≠ 0) : Nontrivial α := by sorry


@[target] lemma diam_eq_zero_of_not_connected (h : ¬G.Connected) : G.diam = 0 := by sorry


@[target] lemma diam_eq_zero_of_ediam_eq_top (h : G.ediam = ⊤) : G.diam = 0 := by sorry


@[target] lemma ediam_ne_top_of_diam_ne_zero (h : G.diam ≠ 0) : G.ediam ≠ ⊤ := by sorry


@[target] lemma exists_dist_eq_diam [Nonempty α] :
    ∃ u v, G.dist u v = G.diam := by sorry


@[gcongr]
lemma diam_anti_of_ediam_ne_top (h : G ≤ G') (hn : G.ediam ≠ ⊤) : G'.diam ≤ G.diam :=
  ENat.toNat_le_toNat (ediam_anti h) hn

@[simp]
lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  rw [diam, ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl ediam_eq_zero_of_subsingleton
  · exact Or.inr ediam_bot

@[simp]
lemma diam_top [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1 := by
  rw [diam, ediam_top, ENat.toNat_one]

@[target] lemma diam_eq_zero : G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α := by sorry


@[target] lemma diam_eq_one [Nontrivial α] : G.diam = 1 ↔ G = ⊤ := by sorry


end diam

end SimpleGraph
