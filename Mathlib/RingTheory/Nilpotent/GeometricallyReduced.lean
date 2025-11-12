/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic

import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Geometrically reduced algebras

In this file we introduce geometrically reduced algebras.
For a field `k`, we say that a `k`-algebra `A` is geometrically reduced (`IsGeometricallyReduced`)
if the tensor product `AlgebraicClosure k ⊗[k] A` is reduced.

## Main results
- `IsGeometricallyReduced.of_forall_fg`: for a field `k` and a commutative `k`-algebra `A`, if all
  finitely generated subalgebras `B` of `A` are geometrically reduced, then `A` is geometrically
  reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent.

## TODO
- Prove that if `A` is a geometrically reduced `k`-algebra, then for every field extension `K` of
  `k` the `K`-algebra `K ⊗[k] A` is reduced.

-/

open TensorProduct

noncomputable section

namespace Algebra

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The `k`-algebra `A` is geometrically reduced iff its base change to `AlgebraicClosure k` is
  reduced. -/
@[mk_iff]
class IsGeometricallyReduced (k A : Type*) [Field k] [Ring A] [Algebra k A] : Prop where
  isReduced_algebraicClosure_tensorProduct : IsReduced (AlgebraicClosure k ⊗[k] A)

attribute [instance] IsGeometricallyReduced.isReduced_algebraicClosure_tensorProduct

instance (k A K : Type*) [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGeometricallyReduced k A] : IsReduced (K ⊗[k] A) :=
  isReduced_of_injective
    (Algebra.TensorProduct.map ((IsAlgClosed.lift : K →ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))

lemma IsGeometricallyReduced.of_injective {B : Type*} [Ring B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A :=
  ⟨isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)⟩

variable (k) in
theorem isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective <| FaithfulSMul.algebraMap_injective _ _)

/-- If all finitely generated subalgebras of `A` are geometrically reduced, then `A` is
  geometrically reduced. The result is in https://stacks.math.columbia.edu/tag/030T -/
@[stacks 030T]
theorem IsGeometricallyReduced.of_forall_fg
    (h : ∀ B : Subalgebra k A, B.FG → IsGeometricallyReduced k B) :
    IsGeometricallyReduced k A := by
  simp_rw [isGeometricallyReduced_iff] at h
  exact ⟨IsReduced.tensorProduct_of_flat_of_forall_fg h⟩

end Algebra

theorem IsGeometricallyReduced.of_localization {k A B : Type} [CommRing B] [CommRing A]
    [h : Algebra A B] [Field k] [Algebra k A] [Algebra k B] [IsScalarTower k A B] {M : Submonoid A}
    [Algebra.IsGeometricallyReduced k A] [IsLocalization M B] :
    Algebra.IsGeometricallyReduced k B := by
  have : Algebra (AlgebraicClosure k ⊗[k] A) (AlgebraicClosure k ⊗[k] B) :=
    RingHom.toAlgebra (Algebra.TensorProduct.map
      (AlgHom.id k (AlgebraicClosure k)) (Algebra.algHom k A B))
  let M' : Submonoid (AlgebraicClosure k ⊗[k] A) :=
    M.map Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom
  have hLoc : IsLocalization M' (AlgebraicClosure k ⊗[k] B) := by
    sorry
  rw [Algebra.isGeometricallyReduced_iff]
  apply isReduced_localizationPreserves M' (AlgebraicClosure k ⊗[k] B)
  infer_instance



example (k A B : Type) [CommRing A] [CommRing B] [CommRing k] [Algebra k A] [Algebra k B]
    (M : Submonoid B) : Submonoid (A ⊗[k] B)
  := Submonoid.map Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom M

example (k A B R : Type) [CommRing A] [CommRing B] [CommRing k] [CommRing R] [Algebra k A]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] (M : Submonoid A) [IsLocalization M B]
    [Algebra k R] :
    haveI : Algebra (R ⊗[k] A) (R ⊗[k] B) := RingHom.toAlgebra (Algebra.TensorProduct.map
      (AlgHom.id k R) (Algebra.algHom k A B))
    IsLocalization (M.map Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom : Submonoid (R ⊗[k] A)) (R ⊗[k] B)
  := by

  sorry
