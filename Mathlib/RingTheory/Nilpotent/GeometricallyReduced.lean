/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic

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

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : A →+* B := by exact
  RingHom.smulOneHom

example (k A B R : Type) [Field k] [CommRing R] [CommRing A] [CommRing B] (S : Submonoid A)
    [Algebra A B] [Algebra k A] [Algebra k B] [IsScalarTower k A B] [IsLocalization S B]
    [Algebra k R] :
    haveI : Algebra (R ⊗[k] A) (R ⊗[k] B)
      := RingHom.toAlgebra (TensorProduct.map (AlgHom.id k R) (algHom k A B)).toRingHom
    IsLocalization (S.map (TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)) (R ⊗[k] B) := by
  haveI : Algebra A (R ⊗[k] A) := RingHom.toAlgebra (TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)
  haveI : Algebra B (R ⊗[k] B) := RingHom.toAlgebra (TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B)
  haveI : Algebra A (R ⊗[k] B) := RingHom.toAlgebra ((TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).toRingHom.comp (RingHom.smulOneHom : A →+* B))
  haveI : Algebra (R ⊗[k] A) (R ⊗[k] B)
      := RingHom.toAlgebra (TensorProduct.map (AlgHom.id k R) (algHom k A B)).toRingHom
  haveI : IsScalarTower A B (R ⊗[k] B) := by sorry
  haveI : IsScalarTower A (R ⊗[k] A) (R ⊗[k] B) := by sorry
  have hLoc : IsLocalization (algebraMapSubmonoid (R ⊗[k] A) S) (R ⊗[k] B) := by
    rw [isLocalization_iff_isPushout S B]
    rw [isPushout_iff]

    sorry

  sorry
end Algebra

namespace Algebra

variable (k A B R : Type) [Field k] [CommRing R] [CommRing A] [CommRing B] (S : Submonoid A)
    [Algebra A B] [Algebra k A] [Algebra k B] [IsScalarTower k A B] [IsLocalization S B]
    [Algebra k R]

instance test : Algebra (R ⊗[k] A) (R ⊗[k] B)
  := RingHom.toAlgebra (TensorProduct.map (AlgHom.id k R) (algHom k A B)).toRingHom
instance test2 : Algebra A (R ⊗[k] A)
  := RingHom.toAlgebra (TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)
instance test3 : Algebra B (R ⊗[k] B)
  := RingHom.toAlgebra (TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B)
instance test4 : Algebra A (R ⊗[k] B)
  := RingHom.toAlgebra ((TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).toRingHom.comp
    (RingHom.smulOneHom : A →+* B))
instance test5 : IsScalarTower A B (R ⊗[k] B) := by
  apply IsScalarTower.of_algebraMap_eq'

  sorry
instance test6 : IsScalarTower A (R ⊗[k] A) (R ⊗[k] B) := by
  apply IsScalarTower.of_algebraMap_eq'
  sorry
instance test7 : Algebra B ((R ⊗[k] A) ⊗[A] B) := by sorry
instance test8 : IsScalarTower A B (R ⊗[k] A ⊗[A] B) := by sorry
-- instance test9 : Algebra (R ⊗[k] A) ((R ⊗[k] A) ⊗[A] B) := by sorry
-- instance test10 : IsScalarTower A (R ⊗[k] A) (R ⊗[k] A ⊗[A] B) := by sorry

example : IsLocalization (algebraMapSubmonoid (R ⊗[k] A) S) (R ⊗[k] B) := by
  rw [isLocalization_iff_isPushout S B]
  have f : R ⊗[k] B ≃ₐ[B] (R ⊗[k] A) ⊗[A] B := by sorry
  have hPushout : IsPushout A (R ⊗[k] A) B ((R ⊗[k] A) ⊗[A] B) := by
    -- @TensorProduct.isPushout A (R ⊗[k] A) B _ _ _ _ _
    exact @TensorProduct.isPushout A (R ⊗[k] A) B _ _ _ _ _
    sorry
  have hPushout' : IsPushout A B (R ⊗[k] A) ((R ⊗[k] A) ⊗[A] B) := sorry
  rw [IsPushout.comm]
  apply (IsPushout.of_equiv f.symm)

  sorry


end Algebra
