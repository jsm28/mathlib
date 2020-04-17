/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.fintype.basic
import category_theory.limits.limits
import category_theory.limits.shapes.finite_limits
import category_theory.sparse
-- import category_theory.connected

universes v u

open category_theory category_theory.limits

variable (J : Type v)

@[derive inhabited]
def wide_pullback_shape := option J

namespace wide_pullback_shape

local attribute [tidy] tactic.case_bash

instance fintype_obj [fintype J] : fintype (wide_pullback_shape J) :=
by { rw wide_pullback_shape, apply_instance }

variable {J}

@[derive decidable_eq]
inductive hom : wide_pullback_shape J → wide_pullback_shape J → Type v
| id : Π X, hom X X
| term : Π (j : J), hom (some j) none

instance struct : category_struct (wide_pullback_shape J) :=
{ hom := hom,
  id := λ j, hom.id j,
  comp := λ j₁ j₂ j₃ f g,
  begin
    cases f,
      exact g,
    cases g,
    apply hom.term _
  end }

instance : inhabited (hom none none) := ⟨hom.id (none : wide_pullback_shape J)⟩

instance fintype_hom [decidable_eq J] (j j' : wide_pullback_shape J) :
  fintype (j ⟶ j') :=
{ elems :=
  begin
    cases j',
    { cases j,
      { exact {hom.id none} },
      { exact {hom.term j} } },
    { by_cases some j' = j,
      { rw h,
        exact {hom.id j} },
      { exact ∅ } }
  end,
  complete := by tidy }

instance subsingleton_hom (j j' : wide_pullback_shape J) : subsingleton (j ⟶ j') :=
⟨by tidy⟩

instance category : small_category (wide_pullback_shape J) := sparse_category

instance fin_category [fintype J] [decidable_eq J] : fin_category (wide_pullback_shape J) :=
{ fintype_hom := wide_pullback_shape.fintype_hom }

-- instance connected : connected (wide_pullback_shape J) :=
-- begin
--   apply connected.of_induct,
--   introv _ t,
--   cases j,
--   exact a,
--   rwa t (hom.term j),
-- end

@[simp] lemma hom_id (X : wide_pullback_shape J) : hom.id X = 𝟙 X := rfl

end wide_pullback_shape

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- `has_wide_pullbacks` represents a choice of wide pullback for every collection of morphisms -/
class has_wide_pullbacks :=
(has_limits_of_shape : Π (J : Type v), has_limits_of_shape.{v} (wide_pullback_shape J) C)

/-- `has_wide_pullbacks` represents a choice of wide pullback for every finite collection of morphisms -/
class has_finite_wide_pullbacks :=
(has_limits_of_shape : Π (J : Type v) [decidable_eq J] [fintype J], has_limits_of_shape.{v} (wide_pullback_shape J) C)

attribute [instance] has_wide_pullbacks.has_limits_of_shape

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits, it also has finite wide pullbacks -/
def has_pullbacks_of_has_finite_limits [has_finite_limits.{v} C] : has_finite_wide_pullbacks.{v} C :=
{ has_limits_of_shape := λ J _ _, by exactI (has_finite_limits.has_limits_of_shape _) }
