/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import group_theory.subgroup

/-!
# Subgroups

This file defines multiplicative and additive subgroups, in an bundled form (unbundled subgroups are
in subgroups.lean).

We prove subgroups of a group form a complete lattice, and results about images and preimages of
subgroups under group homomorphisms. The bundled subgroups use bundled monoid homomorphisms.

There are also theorems about the subgroups generated by an element or a subset of a group,
defined both inductively and as the infimum of the set of subgroups containing a given
element/subset.

This file is greatly inspired by Amelia Livingston's bundled submonoids and special thanks goes to her.

## Main definitions

Notation used here:

- `G N` are groups

- `A` is an add_group

- `H K` are subgroups of `G` or add_subgroups of `A`

- `x` is an element of type `G` or type `A`

- `f : N →* G` is a group homomorphism

- `s : set G` is a set of elements of type `G`

Definitions in the file:

* `subgroup G` : the type of subgroups of `G`

* `add_subgroup A` : the type of add_subgroups of `A`

* `gpowers x` : the cyclic group generated by `x`

* `gmultiples x` : the cyclic add_group generated by `x`

* `univ G` : the subgroup `G` of the group `G`

* `bot G` : the trivial subgroup `{1}` of an group `G`

* `inf H K` : the inf of `H` and `K` is their intersection.

* `complete_lattice (subgroup G)` : the subgroups of `G` form a complete lattice.

* `comap f H` : the preimage of a subgroup `H` along the group homomorphism `f` is also a subgroup

* `map f H` : the image of a subgroup `H` along the group homomorphism `f` is also a subgroup

* `range f` the range of the group homomorphism `f` is a subgroup

* `closure s` : the inductively defined subgroup generated by the set `s`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

## Tags
subgroup, subgroups
-/

variables {G : Type*} [group G] 

/-- A subgroup of a group `G` is a subset containing 1 and closed under multiplication. -/
structure subgroup (G : Type*) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-- An additive subgroup of an additive group `G` is a subset containing 0 and
  closed under addition. -/
structure add_subgroup (G : Type*) [add_group G] :=
(carrier : set G)
(zero_mem' : (0 : G) ∈ carrier)
(add_mem' {x y} : x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → -x ∈ carrier)

attribute [to_additive add_subgroup] subgroup

/-- Map from subgroups of group `G` to `add_subgroup`s of `additive G`. -/
def subgroup.to_add_subgroup {G : Type*} [group G] (H : subgroup G) :
  add_subgroup (additive G) :=
{ carrier := H.carrier,
  zero_mem' := H.one_mem',
  add_mem' := H.mul_mem', 
  inv_mem' := H.inv_mem' }

/-- Map from `add_subgroup`s of `additive G` to subgroups of `G`. -/
def subgroup.of_add_subgroup {G : Type*} [group G] (H : add_subgroup (additive G)) :
  subgroup G :=
{ carrier := H.carrier,
  one_mem' := H.zero_mem',
  mul_mem' := H.add_mem',
  inv_mem' := H.inv_mem' }

/-- Map from `add_subgroup`s of `add_group G` to subgroups of `multiplicative G`. -/
def add_subgroup.to_subgroup {G : Type*} [add_group G] (H : add_subgroup G) :
  subgroup (multiplicative G) :=
{ carrier := H.carrier,
  one_mem' := H.zero_mem',
  mul_mem' := H.add_mem',
  inv_mem' := H.inv_mem' }

/-- Map from subgroups of `multiplicative G` to `add_subgroup`s of `add_group G`. -/
def add_subgroup.of_subgroup {G : Type*} [add_group G] (H : subgroup (multiplicative G)) :
  add_subgroup G :=
{ carrier := H.carrier,
  zero_mem' := H.one_mem',
  add_mem' := H.mul_mem',
  inv_mem' := H.inv_mem' }

/-- Subgroups of group `G` are isomorphic to additive subgroups of `additive G`. -/
def subgroup.add_subgroup_equiv (G : Type*) [group G] :
subgroup G ≃ add_subgroup (additive G) :=
{ to_fun := subgroup.to_add_subgroup,
  inv_fun := subgroup.of_add_subgroup,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace subgroup

variables (H K : subgroup G)

@[to_additive]
instance : has_coe  (subgroup G) (set G) := ⟨subgroup.carrier⟩

@[to_additive]
instance : has_mem G (subgroup G) := ⟨λ m K, m ∈ K.carrier⟩

@[to_additive]
instance : has_le (subgroup G) := ⟨λ H K, H.carrier ⊆ K.carrier⟩

@[simp, to_additive]
lemma mem_coe {g : G} : g ∈ (K : set G) ↔ g ∈ K.carrier := iff.rfl

/- Two subgroups are equal if the underlying set are the same -/
@[to_additive "Two `add_group`s are equal if the underlying subsets are equal."]
theorem ext' {H K : subgroup G} (h : (H : set G) = K) : H = K :=
by cases H; cases K; congr'

/- Two subgroups are equal if and only if the underlying subsets are equal. -/
@[to_additive "Two `add_subgroup`s are equal if and only if the underlying subsets are equal."]
protected theorem ext'_iff {H K : subgroup G} :
  H.carrier = K.carrier ↔ H = K :=
⟨ext', λ h, h ▸ rfl⟩

/-- Two subgroups are equal if they have the same elements. -/
@[ext, to_additive "Two `add_subgroup`s are equal if they have the same elements."]
theorem ext {H K : subgroup G}
  (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := ext' $ set.ext h

attribute [ext] subgroup.ext

/-- A subgroup contains the group's 1. -/
@[to_additive "An `add_subgroup` contains the group's 0."]
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup is closed under multiplication. -/
@[to_additive "An `add_subgroup` is closed under addition."]
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := subgroup.mul_mem' _

/-- A subgroup is closed under inverse -/
@[to_additive "An `add_subgroup` is closed under inverse."]
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := subgroup.inv_mem' _ 

/-- A finite product of elements of a subgroup of a commutative group is in the subgroup. -/
@[to_additive "A finite sum of elements of an `add_subgroup` of an `add_comm_group` is in the `add_subgroup`."]
lemma prod_mem {G : Type*} [comm_group G] (K : subgroup G)
  {ι : Type*} [decidable_eq ι] {t : finset ι} {f : ι → G} :
  (∀c ∈ t, f c ∈ K) → t.prod f ∈ K :=
finset.induction_on t (by simp [one_mem]) (by simp [mul_mem] {contextual := tt})

/-- A directed union of subgroups is a subgroup. -/
@[to_additive "A directed union of `add_subgroup`s is an `add_subgroup`."]
def Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → subgroup G)
  (directed : ∀ i j, ∃ k, s i ≤ s k ∧ s j ≤ s k) :
  subgroup G :=
{ carrier := (⋃i, s i),
  one_mem' := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, subgroup.one_mem' _⟩,
  mul_mem' := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, (s k).mul_mem' (hk.1 hi) (hk.2 hj)⟩,
  inv_mem' := λ a ha,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    set.mem_Union.2 ⟨i, (s i).inv_mem hi⟩
  }

/-- A subgroup of a group inherits a multiplication. -/
@[to_additive "An `add_subgroup` of an `add_group` inherits an addition."]
instance has_mul : has_mul H := ⟨λ a b, ⟨a.1 * b.1, H.mul_mem' a.2 b.2⟩⟩

/-- A subgroup of a group inherits a 1. -/
@[to_additive "An `add_subgroup` of an `add_group` inherits a zero."]
instance has_one : has_one H := ⟨⟨_, H.one_mem'⟩⟩

/-- A subgroup of a group inherits an inverse. -/
@[to_additive "A `add_subgroup` of a `add_group` inherits an inverse."]
instance has_inv : has_inv H := ⟨λ a, ⟨(a.1)⁻¹, H.inv_mem' a.2⟩⟩

@[simp, to_additive] lemma coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y := rfl
@[simp, to_additive] lemma coe_one : ((1 : H) : G) = 1 := rfl
@[simp, to_additive] lemma coe_inv (x : H) : ((↑x)⁻¹ : G) = ↑(x⁻¹) := rfl

/-- A subgroup of a group inherits a group structure. -/
@[to_additive to_add_group "An `add_subgroup` of an `add_group` inherits an `add_group` structure."]
instance to_group {G : Type*} [group G] {H : subgroup G} : group H :=
by refine { mul := (*), one := 1, inv := has_inv.inv, ..}; by simp [mul_assoc]

/-- A subgroup of a `comm_group` is a `comm_group`. -/
@[to_additive to_add_comm_group "An `add_subgroup` of an `add_comm_group` is an `add_comm_group`."]
instance to_comm_group {G : Type*} [comm_group G] (H : subgroup G) : comm_group H :=
{ mul_comm := λ _ _, subtype.ext.2 $ mul_comm _ _, ..subgroup.to_group}

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive "The natural group hom from an `add_subgroup` of `add_group` `G` to `G`."]
def subtype : H →* G :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp, to_additive] theorem subtype_apply (x : H) : H.subtype x = x := rfl

@[to_additive] lemma subtype_eq_val : (H.subtype : H → G) = subtype.val := rfl

/-- The powers `1, x, x², ...` of an element `x` of a group `G` is a subgroup. -/
def gpowers (x : G) : subgroup G :=
{ carrier := {y | ∃ n : ℤ, x^n = y},
  one_mem' := ⟨0, pow_zero x⟩,
  mul_mem' := by rintros x₁ x₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩; exact ⟨n₁ + n₂, gpow_add _ _ _ ⟩,
  inv_mem' := λ x₁ hx, let ⟨i, hi⟩ := hx in ⟨-i, by simp [hi]⟩
  }

/-- An element `x` of a group is in the subgroup generated by `x`. -/
lemma gpowers.self_mem {x : G} : x ∈ gpowers x := ⟨1, pow_one _⟩

/-- If `a` is in a subgroup, so are all its natural number powers. -/
private lemma gpow_mem_nat {a : G} (h : a ∈ H) : ∀ {n : ℕ}, a ^ n ∈ H
| 0 := H.one_mem
| (n + 1) := H.mul_mem h gpow_mem_nat

/-- If `a` is in a subgroup, so are all its integer powers. -/
lemma gpow_mem {a : G} (h : a ∈ H) : ∀ {n : ℤ}, a ^ n ∈ H
| (n : ℕ) := gpow_mem_nat _ h
| -[1+ n] := 
begin -- Maybe use int.induction_on instead
  induction n with k hk,
    all_goals {rw [gpow_neg_succ, ←inv_pow], apply H.mul_mem, from H.inv_mem h}, 
    from H.one_mem, 
    rw [gpow_neg_succ, ←inv_pow] at hk, from hk
end

lemma gpowers_subset {a : G} (h : a ∈ H) : gpowers a ≤ H :=
λ a ⟨n, hx⟩, hx ▸ H.gpow_mem h

private lemma coe_gpow_nat (a : H) (n : ℕ) : ((a ^ n : H) : G) = a ^ n :=
by induction n; simp [*, pow_succ]

@[simp] lemma coe_gpow (a : H) (n : ℤ) : ((a ^ n : H) : G) = a ^ n :=
begin
  cases n, refine coe_gpow_nat _ a n, 
  induction n with k hk,
    all_goals {simp *},
    simp [*, pow_succ], iterate 2 {rw ←inv_pow}, refine coe_gpow_nat _ a⁻¹ k
end

end subgroup

namespace add_subgroup

variables {A : Type*} [add_group A] 
variables (H : add_subgroup A)

/-- The multiples `0, x, 2x, ...` of an element `x` of an `add_group M` are an `add_subgroup`. -/
def gmultiples (x : A) : add_subgroup A :=
{ carrier := {y | ∃ n : ℤ, gsmul n x = y},
  zero_mem' := ⟨0, zero_gsmul x⟩,
  add_mem' := by rintros x₁ x₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩; exact ⟨n₁ + n₂, add_gsmul _ _ _ ⟩,
  inv_mem' := λ x₁ hx, let ⟨i, hi⟩ := hx in ⟨-i, by simp [hi]⟩ }

/-- An element `x` of an `add_group` is in the `add_submgroup` generated by `x`. -/
lemma gmultiples.self_mem {x : A} : x ∈ gmultiples x := ⟨1, one_gsmul x⟩

lemma gsmul_mem {a : A} (h : a ∈ H) {n : ℤ} : gsmul n a ∈ H :=
subgroup.gpow_mem (add_subgroup.to_subgroup H) h

lemma gmultiples_subset {a : A} (h : a ∈ H) : gmultiples a ≤ H :=
subgroup.gpowers_subset (add_subgroup.to_subgroup H) h

@[simp] lemma coe_gsmul (a : H) (n : ℤ) : ((gsmul n a : H) : A) = gsmul n a :=
subgroup.coe_gpow (add_subgroup.to_subgroup H) a n

end add_subgroup

namespace subgroup

variables {H : subgroup G}

/-- The subgroup `G` of the group `G`. -/
@[to_additive "The `add_subgroup G` of the `add_group G`."]
def univ : subgroup G :=
{ carrier := set.univ,
  one_mem' := set.mem_univ 1,
  mul_mem' := λ _ _ _ _, set.mem_univ _,
  inv_mem' := λ _ _, set.mem_univ _ }

/-- The trivial subgroup `{1}` of an group `G`. -/
@[to_additive "The trivial `add_subgroup` `{0}` of an `add_group` `G`."]
def bot : subgroup G :=
{ carrier := {1},
  one_mem' := set.mem_singleton 1,
  mul_mem' := λ _ _ _ _, by simp * at *,
  inv_mem' := λ _, by simp * }

/-- Subgroups of a group are partially ordered (by inclusion). -/
@[to_additive "The `add_subgroup`s of an `add_group` are partially ordered (by inclusion)."]
instance : partial_order (subgroup G) :=
partial_order.lift (coe : subgroup G → set G) (λ a b, ext') (by apply_instance)

@[to_additive]
lemma le_def (p p' : subgroup G) : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

open lattice

@[to_additive]
instance : has_bot (subgroup G) := ⟨subgroup.bot⟩

@[to_additive]
instance : inhabited (subgroup G) := ⟨⊥⟩

@[simp, to_additive] lemma mem_bot {x : G} : x ∈ (⊥ : subgroup G) ↔ x = 1 := set.mem_singleton_iff

@[to_additive]
instance : order_bot (subgroup G) :=
{ bot := ⊥,
  bot_le := λ P x hx, by {simp *, rw mem_bot.mp hx, from P.one_mem},
  ..subgroup.partial_order
  }

@[to_additive]
instance : has_top (subgroup G) := ⟨univ⟩

@[simp, to_additive] lemma mem_top (x : G) : x ∈ (⊤ : subgroup G) := set.mem_univ x

@[to_additive]
instance : order_top (subgroup G) :=
{ top := ⊤,
  le_top := λ p x _, mem_top x,
  ..subgroup.partial_order}

/-- The inf of two subgroups is their intersection. -/
@[to_additive "The inf of two `add_subgroups`s is their intersection."]
def inf (H₁ H₂ : subgroup G) :
  subgroup G :=
{ carrier := H₁ ∩ H₂,
  one_mem' := ⟨H₁.one_mem, H₂.one_mem⟩,
  mul_mem' := λ _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩,
    ⟨H₁.mul_mem hx hy, H₂.mul_mem hx' hy'⟩,
  inv_mem' := λ _ ⟨hx, hx'⟩,
    ⟨H₁.inv_mem hx, H₂.inv_mem hx'⟩ }

@[to_additive]
instance : has_inf (subgroup G) := ⟨inf⟩

@[to_additive]
lemma mem_inf {p p' : subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
⟨λ h, ⟨h.1, h.2⟩, λ h, (p ⊓ p').mem_coe.2 ⟨h.1, h.2⟩⟩

@[to_additive]
instance : has_Inf (subgroup G) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, ↑t,
  one_mem' := set.mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_bInter_iff.1 hx i h) (by apply set.mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, set.mem_bInter $ λ i h,
    i.inv_mem (by apply set.mem_bInter_iff.1 hx i h) }⟩

@[to_additive]
lemma Inf_le' {S : set (subgroup G)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

@[to_additive]
lemma le_Inf' {S : set (subgroup G)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
set.subset_bInter

@[to_additive]
lemma mem_Inf {S : set (subgroup G)} {x : G} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

/-- Subgroups of a group form a lattice. -/
@[to_additive "The `add_subgroup`s of an `add_group` form a lattice."]
instance lattice.lattice : lattice (subgroup G) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c ha hb, set.subset_inter ha hb,
  inf_le_left  := λ a b, set.inter_subset_left _ _,
  inf_le_right := λ a b, set.inter_subset_right _ _, ..subgroup.partial_order}

/-- Subgroups of a group form a complete lattice. -/
@[to_additive "The `add_subgroup`s of an `add_group` form a complete lattice."]
instance : complete_lattice (subgroup G) :=
{ Sup          := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ p' hp', hp' _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..subgroup.lattice.order_top,
  ..subgroup.lattice.order_bot,
  ..subgroup.lattice.lattice}


/-- Subgroups of a group form an `add_comm_monoid`. -/
@[to_additive "The `add_subgroup`s of an `add_group` form an `add_comm_monoid."]
instance complete_lattice.add_comm_monoid :
  add_comm_monoid (subgroup G) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

/-- The preimage of a subgroup along a group homomorphism is a subgroup. -/
def comap {N : Type*} [group N] (f : G →* N)
  (H : subgroup N) : subgroup G :=
{ carrier := (f ⁻¹' H),
  one_mem' := show f 1 ∈ H, by rw f.map_one; exact H.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ H, by rw f.map_mul; exact H.mul_mem ha hb,
  inv_mem' := λ a ha, 
    show f a⁻¹ ∈ H, by rw f.map_inv; exact H.inv_mem ha }

  /-- The image of a subgroup along a group homomorphism is a subgroup. -/
def map {N : Type*} [group N] (f : G →* N) (H : subgroup G) : subgroup N :=
{ carrier := (f '' H),
  one_mem' := ⟨1, H.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, H.mul_mem hx hy, by rw f.map_mul; refl⟩ end,
  inv_mem' := begin rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, H.inv_mem hx, by rw f.map_inv; refl⟩, end
   }
  
/-- The range of a group homomorphism is a subgroup. -/
def range {N : Type*} [group N] (f : G →* N) :
  subgroup N := map f univ

end subgroup

namespace group

open subgroup

/-- The inductively defined subgroup generated by a set. -/
@[to_additive "The inductively defined `add_subgroup` generated by a set. "]
def closure' (s : set G) : subgroup G :=
{ carrier := in_closure s,
  one_mem' := in_closure.one s,
  mul_mem' := λ _ _, in_closure.mul,
  inv_mem' := λ _, in_closure.inv }

/-- The subgroup generated by a set contains the set. -/
@[to_additive "The `add_subgroup` generated by a set contains the set."]
theorem le_closure' {s : set G} : s ≤ closure' s :=
λ a, in_closure.basic

/-- The subgroup generated by a set is contained in any subgroup that contains the set. -/
@[to_additive "The `add_subgroup` generated by a set is contained in any `add_subgroup` that contains the set."]
theorem closure'_le {s : set G} {H : subgroup G} (h : s ≤ H) : closure' s ≤ H :=
λ a ha, begin induction ha with _ hb _ _ _ _ ha hb,
  {exact h hb},
  {exact H.one_mem},
  {apply H.inv_mem, assumption},
  {apply H.mul_mem, iterate 2 {assumption}}
end 

/-- Given subsets `t` and `s` of a group `G`, if `s ⊆ t`, the subgroup of `G` generated by `s` is
    contained in the subgroup generated by `t`. -/
@[to_additive "Given subsets `t` and `s` of an `add_monoid` `M`, if `s ⊆ t`, the `add_submonoid` of `M` generated by `s` is contained in the `add_submonoid` generated by `t`."]
theorem closure'_mono {s t : set G} (h : s ≤ t) : closure' s ≤ closure' t :=
closure'_le $ set.subset.trans h le_closure'

/-- The subgroup generated by an element of a group equals the set of natural number powers
    of the element. -/
theorem closure'_singleton {x : G} : closure' ({x} : set G) = gpowers x :=
ext' $ set.eq_of_subset_of_subset (closure'_le $ set.singleton_subset_iff.2 gpowers.self_mem) $
subgroup.gpowers_subset _ $ in_closure.basic $ set.mem_singleton x


/-- The image under a group hom of the subgroup generated by a set equals the subgroup generated
    by the image of the set. -/
lemma image_closure' {N : Type*} [group N] (f : G →* N) (s : set G) :
  map f (closure' s) = closure' (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [le_closure', set.mem_image_of_mem] },
    { rw f.map_one, apply subgroup.one_mem },
    { rw f.map_inv, solve_by_elim [subgroup.inv_mem] },
    { rw f.map_mul, solve_by_elim [subgroup.mul_mem] }
  end
  (closure'_le $ set.image_subset _ le_closure')

end group

namespace add_group

open add_subgroup

variables {A : Type*} [add_group A]

/-- The `add_subgroup` generated by an element of an `add_group` equals the set of natural number
    multiples of the element. -/
theorem closure'_singleton {x : A} : closure' ({x} : set A) = gmultiples x :=
ext' $ set.eq_of_subset_of_subset (closure'_le $ set.singleton_subset_iff.2 gmultiples.self_mem) $
gmultiples_subset _ $ in_closure.basic $ set.mem_singleton x

end add_group

namespace mul_equiv

variables {H K : subgroup G}

/-- Makes the identity isomorphism from a proof two subgroup of a multiplicative
    group are equal. -/
@[to_additive add_subgroup_congr "Makes the identity additive isomorphism from a proof two submonoids of an additive group are equal."]
def subgroup_congr (h : H = K) : H ≃* K :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ subgroup.ext'_iff.2 h }

end mul_equiv

