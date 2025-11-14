
/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
import Mathlib

section

variable {R : Type} [CommRing R] {p : Ideal R} [p.IsPrime]
variable (S : Type) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]

lemma localization_at_minimalPrime_of_reduced_is_field [IsReduced R] (hp : p ∈ minimalPrimes R) :
    IsField S := by
  have := Ring.KrullDimLE.of_isLocalization p hp S
  unfold IsLocalization.AtPrime at *
  have : IsReduced S := by
    apply (isReduced_localizationPreserves p.primeCompl S)
    infer_instance
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  apply (Ring.KrullDimLE.isField_of_isReduced (R := S))

lemma map_to_field_from_minimal_prime_kernel (hp : p ∈ minimalPrimes R) [IsReduced R] :
    RingHom.ker (algebraMap R S) = p := by
  have hSLocal : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  rw [RingHom.ker_eq_comap_bot]
  rw [← IsLocalRing.isField_iff_maximalIdeal_eq.mp
      (localization_at_minimalPrime_of_reduced_is_field S hp)]
  rw [IsLocalization.AtPrime.comap_maximalIdeal S p]

end

section

variable {k : Type} [Field k]
variable (R : Type) [CommRing R] [Algebra k R]
variable (S : minimalPrimes R → Type) [∀ p : minimalPrimes R, CommRing (S p)]
variable [∀ p : minimalPrimes R, Algebra R (S p)]
variable [∀ p : minimalPrimes R, Algebra k (S p)] [∀ p : minimalPrimes R, IsScalarTower k R (S p)]
variable [∀ p : minimalPrimes R, IsLocalization.AtPrime (S p) p.val (hp := p.2.1.1)]

-- Needed for Stacks 00EW
def canonical_field_product_embedding : R →+* Π p : minimalPrimes R, (S p) :=
  Pi.ringHom (fun p => algebraMap R (S p))

lemma canonical_field_product_embedding_kernel [IsReduced R] :
    RingHom.ker (canonical_field_product_embedding R S) = ⨅ p : minimalPrimes R, p.1 := by
  unfold canonical_field_product_embedding
  rw [Pi.ker_ringHom]
  apply iInf_congr
  intro p
  have hp : p.val.IsPrime := p.2.1.1
  exact (map_to_field_from_minimal_prime_kernel (S p) p.2)

end

-- Now want to prove 10.34.5 from the Stacks project
-- Can use minimalPrimes.finite_of_isNoetherianRing to show that a Noetherian ring has only
-- finitely many minimal prime ideals, and hence the codomain of canonical_field_product_embedding
-- is a finite product of fields. Actually, I think that this result only works with the stronger
-- definition of geometrically reduced...

open TensorProduct
open Algebra

lemma separable_tensor_reduced (k k' L : Type) [Field k] [Field k'] [Field L] [Algebra k k']
    [Algebra k L] [Algebra.IsSeparable k k'] [EssFiniteType k k'] :
    IsReduced (L ⊗[k] k') := by
  have hEtale : FormallyEtale k k' := by
    apply (Algebra.FormallyEtale.iff_isSeparable k k').mpr
    infer_instance
  have hEtale2 : FormallyEtale L (L ⊗[k] k') := Algebra.FormallyEtale.instTensorProduct
  have hUnramified : FormallyUnramified L (L ⊗[k] k') :=
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp hEtale2).left
  have hEssFinType : EssFiniteType L (L ⊗[k] k'):= Algebra.EssFiniteType.baseChange k k' L
  apply (Algebra.FormallyUnramified.isReduced_of_field L)

lemma purely_transcendental_tensor_reduced (k k' R : Type) [Field k] [Field k'] [Algebra k k']
    [CommRing R] [Algebra k R] (ι : Type) (x : ι → k') (hBasis : IsTranscendenceBasis k x)
    (hPurelyTranscendental : k' = Algebra.adjoin k (Set.range x)) [IsReduced R] :
    IsReduced (k' ⊗[k] R) := by

  sorry
