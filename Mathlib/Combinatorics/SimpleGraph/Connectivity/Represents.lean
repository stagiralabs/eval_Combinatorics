import VerifiedAgora.tagger
/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card

/-!
# Representation of components by a set of vertices

## Main definition

* `SimpleGraph.ConnectedComponent.Represents` says that a set of vertices represents a set of
  components if it contains exactly one vertex from each component.
-/

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

namespace SimpleGraph.ConnectedComponent

/-- A set of vertices represents a set of components if it contains exactly one vertex from
each component. -/
def Represents (s : Set V) (C : Set G.ConnectedComponent) : Prop := by sorry


namespace Represents

variable {C : Set G.ConnectedComponent} {s : Set V} {c : G.ConnectedComponent}

@[target] lemma image_out (C : Set G.ConnectedComponent) :
    Represents (Quot.out '' C) C := by sorry


@[target] lemma existsUnique_rep (hrep : Represents s C) (h : c ∈ C) : ∃! x, x ∈ s ∩ c.supp := by sorry


@[target] lemma exists_inter_eq_singleton (hrep : Represents s C) (h : c ∈ C) : ∃ x, s ∩ c.supp = {x} := by sorry


@[target] lemma disjoint_supp_of_not_mem (hrep : Represents s C) (h : c ∉ C) : Disjoint s c.supp := by sorry


lemma ncard_inter (hrep : Represents s C) (h : c ∈ C) : (s ∩ c.supp).ncard = 1 := by
  rw [Set.ncard_eq_one]
  exact exists_inter_eq_singleton hrep h

@[target] lemma ncard_sdiff_of_mem (hrep : Represents s C) (h : c ∈ C) :
    (c.supp \ s).ncard = c.supp.ncard - 1 := by sorry


@[target] lemma ncard_sdiff_of_not_mem (hrep : Represents s C) (h : c ∉ C) :
    (c.supp \ s).ncard = c.supp.ncard := by sorry


end SimpleGraph.ConnectedComponent.Represents
