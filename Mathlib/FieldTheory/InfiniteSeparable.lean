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
    ∃ ι : Type, ∃ x : ι → K, separablyGeneratedBy K' K x

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
  let hEquiv : L ≃ₐ[k] (IntermediateField.lift L) := IntermediateField.liftAlgEquiv L
  have hFin' : Algebra.EssFiniteType k (IntermediateField.lift L) := by


    sorry
  have h' := h (K'.lift L) hFin'
  obtain ⟨ι, x, hx⟩ := h'
  use ι

  sorry
