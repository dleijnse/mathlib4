/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/

import Mathlib

/-
This file defines the category of Fields.
-/

universe u v

open CategoryTheory

structure FieldCat where
  (carrier : Type u)
  [field : Field carrier]

attribute [instance] FieldCat.field

namespace FieldCat

instance : CoeSort FieldCat (Type u) :=
  ⟨FieldCat.carrier⟩

abbrev of (k : Type u) [Field k] : FieldCat :=
  ⟨k⟩

@[ext]
structure Hom (k K : FieldCat) where
  hom' : k →+* K

instance : Category FieldCat where
  Hom k K := Hom k K
  id k := ⟨RingHom.id k⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} FieldCat (fun k K => k →+* K) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

abbrev ofHom {k K : Type u} [Field k] [Field K] (f : k →+* K) : of k ⟶ of K :=
  ConcreteCategory.ofHom (C := FieldCat) f

end FieldCat
