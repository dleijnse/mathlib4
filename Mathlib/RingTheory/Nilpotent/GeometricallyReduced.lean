/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
import Mathlib

/-!
# Geometrically reduced algebras

In this file we introduce geometrically reduced algebras.
For a field `k`, we say that a `k`-algebra `A` is geometrically reduced (`IsGeometricallyReduced`)
if the tensor product `A ⊗[k] AlgebraicClosure k` is reduced.

## Main results
- `all_FG_geometricallyReduced_isGeometricallyReduced`: if all finitely generated subalgebras of `A`
  are geometrically reduced, then `A` is geometrically reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent.

-/

noncomputable section
variable (k : Type) (A : Type) [Field k] [CommRing A] [Algebra k A]
variable (B : Type) [CommRing B] [Algebra k B]


-- Definition of the baseChange of an algebra morphism
def baseChange (f : A →ₐ[k] B) (K : Type) [CommRing K] [Algebra k K] :=
    Algebra.TensorProduct.map (AlgHom.id K K) f


lemma baseChange_by_field_inj (f : A →ₐ[k] B) (h : Function.Injective f) (K : Type) [Field K]
    [Algebra k K] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) f) := by
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact h


@[mk_iff]
class IsGeometricallyReduced : Prop where
  -- The k-algebra A is geometrically reduced iff its basechange to AlgebraicClosure k is reduced
  baseChangeReduced : IsReduced (TensorProduct k (AlgebraicClosure k) A)

theorem IsGeometricallyReduced_imp_baseChange_by_closure_Reduced (h : IsGeometricallyReduced k A) :
    IsReduced (TensorProduct k (AlgebraicClosure k) A) := by
    exact h.baseChangeReduced

lemma isGeometricallyReduced_of_injective (B : Type) [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A := by
  let fK := baseChange  k A B f (AlgebraicClosure k)
  have hfK : Function.Injective fK := baseChange_by_field_inj k A _ f hf _
  expose_names
  rw [isGeometricallyReduced_iff] at *
  exact isReduced_of_injective fK hfK


theorem isGeometricallyReduced_isReduced [IsGeometricallyReduced k A] : IsReduced A := by
  -- We prove this by providing an injection A →ₐ[k] A ⊗[k] AlgebraicClosure k and then
  -- applying isReduced_of_injective
  let f : A →ₐ[k] TensorProduct k (AlgebraicClosure k) A := Algebra.TensorProduct.includeRight
  expose_names
  rw [isGeometricallyReduced_iff] at inst_3
  have hf : Function.Injective f := by
    apply Algebra.TensorProduct.includeRight_injective
    exact FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)
  exact isReduced_of_injective f hf

lemma notReduced_has_nilpotent {R : Type} [Zero R] [Pow R ℕ] (h : ¬IsReduced R) :
    ∃ x : R, x ≠ 0 ∧ IsNilpotent x := by
  by_contra h_contra
  simp only [ne_eq, not_exists, not_and] at h_contra
  simp only [isReduced_iff, not_forall] at h
  obtain ⟨x, ⟨hNil, hx⟩⟩ := h
  tauto

-- The basechange of a subalgebra gives a subalgebra
def subAlgebraBaseChange (C : Subalgebra k A) : Subalgebra B (TensorProduct k B A) :=
  AlgHom.range (baseChange k C A C.val B)

lemma FGsubalgebra_baseChange_of_element (x : TensorProduct k A B) :
    ∃ C : Subalgebra k B , C.FG ∧ x ∈ subAlgebraBaseChange k B A C := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  let S1 := Set.image (fun j ↦ j.2) S.toSet
  let C := Algebra.adjoin k S1
  use C
  constructor
  · rw [Subalgebra.fg_def]
    use S1
    refine ⟨?_, rfl⟩
    exact Set.Finite.image (fun j ↦ j.2) (Finset.finite_toSet S)
  · rw [hS]
    refine Subalgebra.sum_mem _ ?_
    intro s hs
    have hCS : ∀ i ∈ S, i.2 ∈ C := by
      intro i hi
      apply SetLike.mem_of_subset
      · apply Algebra.subset_adjoin
      · use i
        exact ⟨hi, rfl⟩
    use s.1 ⊗ₜ[k] ⟨s.2, hCS s hs⟩
    rfl

-- If all finitely generated subalgebras of A are geometrically reduced, then A is geometrically
-- reduced. The result is in https://stacks.math.columbia.edu/tag/030T
theorem all_FG_geometricallyReduced_isGeometricallyReduced
    (h : ∀ B : Subalgebra k A, B.FG → IsGeometricallyReduced k B) :
    IsGeometricallyReduced k A := by
  by_contra h_contra
  rw [isGeometricallyReduced_iff] at *
  apply notReduced_has_nilpotent at h_contra
  obtain ⟨x, hx⟩ := h_contra
  obtain ⟨C, hC⟩ := FGsubalgebra_baseChange_of_element _ _ _ x
  have hy : ∃ y : (TensorProduct k (AlgebraicClosure k) C), y ≠ 0 ∧ IsNilpotent y := by
    let f := baseChange k C A C.val (AlgebraicClosure k)
    have h_inj : Function.Injective f := by
      apply baseChange_by_field_inj
      exact (AlgHom.injective_codRestrict C.val C Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
    rw [subAlgebraBaseChange, AlgHom.mem_range] at hC
    obtain ⟨z, hz⟩ := hC.2
    use z
    simp only [f] at h_inj
    rw [← hz] at hx
    constructor
    · by_contra h_contra
      rw [h_contra] at hx
      tauto
    · exact (IsNilpotent.map_iff h_inj).mp hx.right
  obtain ⟨y, hy⟩ := hy
  have h_notReduced : ¬IsGeometricallyReduced k C := by
    rw [isGeometricallyReduced_iff, isReduced_iff, not_forall]
    use y
    tauto
  tauto

def map_to_localization (R S : Type) [CommRing R] [CommRing S] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    R →+* S := RingHom.smulOneHom


def map_to_MinimalPrimeLocalizationProduct (R : Type) [CommRing R]
    (ι : {p : Ideal R // p ∈ minimalPrimes R} → Type) [∀ p , CommRing (ι p)]
    [∀ p, Algebra R (ι p)]
    [∀ p, IsLocalization.AtPrime (ι p) p.1 (hp := (Ideal.minimalPrimes_isPrime p.2))]
    : R →+* Π (p : {p : Ideal R // p ∈ minimalPrimes R}), (ι p)
  := -- map_to_localization R (ι p) (Ideal.minimalPrimes_isPrime p.2)
  sorry


-- Note: STACKS 10.25.1 is Ring.KrullDimLE.isField_of_isReduced

/-lemma reduced_inj_field_prod (R : Type) [CommRing R] [IsReduced R] :
    Function.Injective (map_to_MinimalPrimeLocalizationProduct R) := by
  sorry-/

lemma all_minimalPrimesGeometricallyReduced_imp_GeometricallyReduced
    (h : ∀ p : Ideal A, (hp : p ∈ minimalPrimes A) →
      IsGeometricallyReduced k (@Localization.AtPrime _ _ p (Ideal.minimalPrimes_isPrime hp))) :
    IsGeometricallyReduced k A := by

  sorry

example (p : Ideal A) (h : p ∈ minimalPrimes A) : p.IsPrime := by
  exact Ideal.minimalPrimes_isPrime h

-- Final goal:
theorem IsGeometricallyReduced_all_baseChange_IsReduced (K : Type) [Field K] [Algebra k K]
    (h : IsGeometricallyReduced k A) : IsReduced (TensorProduct k K A) := by

  sorry
