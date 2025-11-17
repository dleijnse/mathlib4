/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/

import Mathlib

def separablyGeneratedBy (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) :=
  IsTranscendenceBasis k x ∧ Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K

lemma AlgebraicExtensionEmptyTranscendenceBasis (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] : IsTranscendenceBasis k (@Empty.elim K) := by
  obtain ⟨ι, y, hy⟩ := exists_isTranscendenceBasis' k K
  have hιEmpty := (IsTranscendenceBasis.isEmpty_iff_isAlgebraic hy).mpr
    Algebra.IsIntegral.isAlgebraic
  have hcomp : Empty.elim = y ∘ ⇑(Equiv.equivEmpty ι).symm := by
    ext x
    tauto
  exact hcomp ▸ @IsTranscendenceBasis.comp_equiv Empty ι k K _ _ _ (Equiv.equivEmpty ι).symm y hy

lemma Separable_imp_separablyGeneratedByEmpty (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] : separablyGeneratedBy k K (@Empty.elim K) := by
  refine ⟨AlgebraicExtensionEmptyTranscendenceBasis _ _, ?_⟩
  infer_instance

def InfiniteSeparable (k K : Type) [Field k] [Field K] [Algebra k K] :=
  ∀ K' : IntermediateField k K, Algebra.EssFiniteType k K' →
    ∃ ι : Type, ∃ x : ι → K', separablyGeneratedBy k K' x

def adjoin_equiv (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ≃ₐ[R] T) (X : Set S) : Algebra.adjoin R X ≃ₐ[R] Algebra.adjoin R (f '' X) :=
  (AlgHom.map_adjoin f.toAlgHom X) ▸ (AlgEquiv.subalgebraMap f (Algebra.adjoin R X))

example (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (X : Set S) (s : S) (h : s ∈ Algebra.adjoin R X) :
  f s ∈ Algebra.adjoin R (f '' X) := by
  rw [Algebra.adjoin_image, Subalgebra.mem_map]
  use s

example (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ≃ₐ[R] T) (h : Algebra.EssFiniteType R S) : Algebra.EssFiniteType R T := by
  rw [Algebra.essFiniteType_iff] at *
  obtain ⟨X, hX⟩ := h
  use X.map f
  intro u
  obtain ⟨s, hs⟩ := hX (f.symm.toAlgHom u)
  use f s
  have h_coercion : (X.map f).toSet = ((f : S →ₐ[R] T)) '' X := by
      simp only [Finset.coe_map, Equiv.coe_toEmbedding, EquivLike.coe_coe, AlgHom.coe_coe]
  refine ⟨?_, ?_, ?_⟩
  · rw [h_coercion, Algebra.adjoin_image, Subalgebra.mem_map]
    use s
    exact ⟨hs.1, by rfl⟩
  · rw [MulEquiv.isUnit_map]
    exact hs.right.left
  · have hu : u = f (f.symm u) := by
      rw [AlgEquiv.apply_symm_apply]
    rw [h_coercion, Algebra.adjoin_image, hu]
    simp only [AlgEquiv.apply_symm_apply, Subalgebra.mem_map, AlgHom.coe_coe]
    use f.symm u * s
    refine ⟨hs.2.2, ?_⟩
    simp only [map_mul, AlgEquiv.apply_symm_apply]

example (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ≃ₐ[R] T) (M : Submonoid R) (h : IsLocalization M S) :
  IsLocalization M T := by
  exact IsLocalization.isLocalization_of_algEquiv M f

@[stacks 030P]
lemma IntermediateOfInfiniteSeparable_InfiniteSeparable {k K : Type} [Field k] [Field K]
    [Algebra k K] (K' : IntermediateField k K) (h : InfiniteSeparable k K) :
    InfiniteSeparable k K' := by
  intro L hFin
  let f : L ≃ₐ[k] (IntermediateField.lift L) := IntermediateField.liftAlgEquiv L
  have hFin' : Algebra.EssFiniteType k (IntermediateField.lift L) := by
    sorry
  have h' := h (K'.lift L) hFin'
  obtain ⟨ι, x, hx⟩ := h'
  use ι
  -- use f ∘ x
  /- let x' : ι → L := fun i => ⟨ (x i).1, by sorry⟩
  use x' -/

  sorry

noncomputable section

lemma EssFiniteType_fieldExtension_is_fraction_ring (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : Algebra.EssFiniteType k K]
    : ∃ S : Finset K, IsFractionRing (Algebra.adjoin k S.toSet) K := by
  obtain ⟨S, hS⟩ := h.cond
  use S
  unfold IsFractionRing
  have h2 : Submonoid.comap (algebraMap (Algebra.adjoin k S.toSet) K) (IsUnit.submonoid K) =
      nonZeroDivisors (Algebra.adjoin k S.toSet) := by
    ext x
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, Subalgebra.algebraMap_apply,
      isUnit_iff_ne_zero, ne_eq, ZeroMemClass.coe_eq_zero, mem_nonZeroDivisors_iff_ne_zero]
  rw [← h2]
  exact hS

open Algebra Module
open scoped nonZeroDivisors


example (k K : Type) [CommRing k] [Field K] [Algebra k K] (h : IsFractionRing k K) :
    K ≃ₐ[k] FractionRing k := by
  exact (FractionRing.algEquiv k K).symm

example (R S M : Type) [CommRing R] [CommRing S] [AddCommMonoid M] [Module S M] (f : R ≃+* S) :
    Module R M := by sorry


lemma module_finite_of_algebraic_and_FG (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (S : Finset K) : Module.Finite k (Algebra.adjoin k S.toSet) := by
  rw [← IsNoetherian.iff_fg]
  exact isNoetherian_adjoin_finset S (fun x => fun _ => IsIntegral.isIntegral x)

lemma EssFiniteType_and_algebraic_imp_finite (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : Algebra.EssFiniteType k K] [Algebra.IsAlgebraic k K] : Module.Finite k K := by
  obtain ⟨S, hS⟩ := EssFiniteType_fieldExtension_is_fraction_ring k K

  let kEquiv : FractionRing k ≃ₐ[k] k := (FractionRing.algEquiv k k)
  let KEquiv : FractionRing (Algebra.adjoin k S.toSet) ≃ₐ[adjoin k S.toSet] K :=
      (FractionRing.algEquiv (Algebra.adjoin k S.toSet) K)

  have hFin1 : Module.Finite k (Algebra.adjoin k S.toSet) := module_finite_of_algebraic_and_FG k K S

  let alg : Algebra (FractionRing k) (FractionRing (Algebra.adjoin k S.toSet)) :=
    FractionRing.liftAlgebra _ _
  let mod : Module (FractionRing k) (FractionRing (Algebra.adjoin k S.toSet)) := alg.toModule
  let mod2 : Module (FractionRing k) K := by sorry
  have hFin2 : FiniteDimensional (FractionRing k) (FractionRing (Algebra.adjoin k S.toSet)) := by
    exact instFiniteDimensionalFractionRingOfFinite k (Algebra.adjoin k S.toSet)
  unfold FiniteDimensional at hFin2
  refine (Module.Finite.of_equiv_equiv kEquiv.toRingEquiv KEquiv.toRingEquiv ?_)

  apply IsFractionRing.ringHom_ext (A := k)
  intro x
  simp_all only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes, algebraMap_self, RingHom.id_apply, mod,
    alg, kEquiv, KEquiv]
  unfold FractionRing.algEquiv
  unfold Localization.algEquiv

  sorry


lemma deg_of_separable_closure_of_FG_finite (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (n : ℕ) (x : Fin n → K) (h : IsTranscendenceBasis k x) :
    Module.Finite (IntermediateField.adjoin k (Set.range x)) K := by
  have hAlg : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K :=
    IsTranscendenceBasis.isAlgebraic_field h

  sorry

example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsFractionRing R S] :
    S ≃ₐ[R] FractionRing R := (FractionRing.algEquiv R S).symm

-- example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] [IsDomain S]

-- possibly useful: Algebra.IsAlgebraic.rank_fractionRing_polynomial

theorem extension_decomposition_purelyInseparable_separablyGenerated (k K : Type) [Field k]
    [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    ∃ k' : Type, ∃ K' : Type, ∃ sr : Field k', k' = k' := by

  sorry


/-
TODO: Formalize the following constructions:

- construction of k' out of a polynomial P over k(x₁, ..., xᵣ) by adjoining the p-th roots of all
  coefficients occuring in P
- Construction of L out of k' and K by taking the compositum.
- Inductively making K' and k' out of K and k.


Elementary needed statements:
- Obtain that [K : K_{sep}] is finite out of the fact that K/k is finitely generated.
- Interplay between taking composita, adjoining elements and degrees of field extensions.
- Interplay of IsCompositum and stacking squares together.


-/
