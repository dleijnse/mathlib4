/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/

import Mathlib
import Mathlib.Algebra.Category.FieldCat


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
  have h_coercion : SetLike.coe (X.map f) = ((f : S →ₐ[R] T)) '' X := by
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
    : ∃ S : Finset K, IsFractionRing (Algebra.adjoin k <| SetLike.coe S) K := by
  obtain ⟨S, hS⟩ := h.cond
  use S
  unfold IsFractionRing
  have h2 : Submonoid.comap (algebraMap (Algebra.adjoin k <| SetLike.coe S) K) (IsUnit.submonoid K)
      = nonZeroDivisors (Algebra.adjoin k <| SetLike.coe S) := by
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
    [Algebra.IsAlgebraic k K] (S : Finset K) : Module.Finite k (Algebra.adjoin k <| SetLike.coe S)
    := by
  rw [← IsNoetherian.iff_fg]
  exact isNoetherian_adjoin_finset S (fun x => fun _ => IsIntegral.isIntegral x)

lemma EssFiniteType_and_algebraic_imp_finite (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : Algebra.EssFiniteType k K] [Algebra.IsAlgebraic k K] : Module.Finite k K := by
  obtain ⟨S, hS⟩ := EssFiniteType_fieldExtension_is_fraction_ring k K

  let kEquiv : FractionRing k ≃ₐ[k] k := (FractionRing.algEquiv k k)
  let KEquiv : FractionRing (Algebra.adjoin k <| SetLike.coe S) ≃ₐ[adjoin k <| SetLike.coe S] K :=
      (FractionRing.algEquiv (Algebra.adjoin k <| SetLike.coe S) K)

  have hFin1 : Module.Finite k (Algebra.adjoin k <| SetLike.coe S) :=
    module_finite_of_algebraic_and_FG k K S

  let alg : Algebra (FractionRing k) (FractionRing (Algebra.adjoin k <| SetLike.coe S)) :=
    FractionRing.liftAlgebra _ _
  let mod : Module (FractionRing k) (FractionRing (Algebra.adjoin k <| SetLike.coe S))
    := alg.toModule
  let mod2 : Module (FractionRing k) K := by sorry
  have hFin2 : FiniteDimensional (FractionRing k) (FractionRing (Algebra.adjoin k <| SetLike.coe S))
      := instFiniteDimensionalFractionRingOfFinite
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

open Polynomial
open IntermediateField

-- a field extension `K/k` is purely transcendental if `K` is isomorphic to the fraction field
-- of `k[x_i]` for some
class IsPurelyTranscendental (k K : Type) [Field k] [Field K] [Algebra k K] where
  ι : Type
  [alg : Algebra (MvPolynomial ι k) K]
  -- The compatibility of the different algebra structures is not automatic, so we require the
  -- following to be a scalar tower:
  [IsScalarTower : IsScalarTower k (MvPolynomial ι k) K]
  [IsFracRing : IsFractionRing (MvPolynomial ι k) K]

instance (k K : Type) [Field k] [Field K] [Algebra k K] [h : IsPurelyTranscendental k K] :
    Algebra (MvPolynomial h.ι k) K :=
  h.alg

instance (k K : Type) [Field k] [Field K] [Algebra k K] [h : IsPurelyTranscendental k K] :
    IsFractionRing (MvPolynomial h.ι k) K :=
  h.IsFracRing

instance (k K : Type) [Field k] [Field K] [Algebra k K] [h : IsPurelyTranscendental k K] :
    IsScalarTower k (MvPolynomial h.ι k) K := h.IsScalarTower

def IsPurelyTranscendental.mvPolyFracRingEquiv (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : IsPurelyTranscendental k K] :
    FractionRing (MvPolynomial h.ι k) ≃ₐ[MvPolynomial h.ι k] K := FractionRing.algEquiv _ _

def IsPurelyTranscendental.x (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : IsPurelyTranscendental k K] : h.ι → K :=
  algebraMap (MvPolynomial h.ι k) K ∘ MvPolynomial.X

lemma IsPurelyTranscendental.x_comparison (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : IsPurelyTranscendental k K] :
    h.x = h.mvPolyFracRingEquiv ∘
      algebraMap (MvPolynomial h.ι k) (FractionRing (MvPolynomial h.ι k)) ∘ MvPolynomial.X := by
  unfold x
  ext i
  simp

lemma IsTranscendenceBasis.mvPolynomialFractionField (ι : Type) (k : Type) [Field k] :
    IsTranscendenceBasis k
      (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) ∘ MvPolynomial.X) := by
  have _ : Algebra.IsAlgebraic (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) := by
    have _ : NoZeroSMulDivisors (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) :=
      NoZeroSMulDivisors.instOfFaithfulSMul
    rw [← IsFractionRing.isAlgebraic_iff' (MvPolynomial ι k) (MvPolynomial ι k)
        (FractionRing (MvPolynomial ι k))]
    infer_instance
  exact IsTranscendenceBasis.algebraMap_comp <| mvPolynomial ι k

lemma IsPurelyTranscendental.x_transcendence_basis (k K : Type) [Field k] [Field K] [Algebra k K]
    [h : IsPurelyTranscendental k K] :
    IsTranscendenceBasis k <| IsPurelyTranscendental.x k K := by
  rw [IsPurelyTranscendental.x_comparison]
  exact AlgEquiv.isTranscendenceBasis ((h.mvPolyFracRingEquiv k K).restrictScalars k)
    (IsTranscendenceBasis.mvPolynomialFractionField h.ι k)

instance adjoin_transcendence_basis_purelyTranscendental (k K : Type) [Field k] [Field K]
    [Algebra k K] {ι : Type} (x : ι → K) (h : IsTranscendenceBasis k x) :
    IsPurelyTranscendental k (IntermediateField.adjoin k (Set.range x)) :=
  letI alg := ((Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k (Set.range x)) :
          Algebra.adjoin k (Set.range x) →ₐ[k] IntermediateField.adjoin k (Set.range x)).comp
        (AlgebraicIndependent.aevalEquiv h.1)).toAlgebra
  letI IsScalarTower := by
    exact IsScalarTower.of_algHom
        ((Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k (Set.range x)) :
          Algebra.adjoin k (Set.range x) →ₐ[k] IntermediateField.adjoin k (Set.range x)).comp
        (AlgebraicIndependent.aevalEquiv h.1).toAlgHom)
  {
    ι := ι
    alg
    IsScalarTower
    IsFracRing := by
      haveI : FaithfulSMul (MvPolynomial ι k) ↥(IntermediateField.adjoin k (Set.range x)) := sorry
      apply IsFractionRing.of_field (MvPolynomial ι k) ↥(IntermediateField.adjoin k (Set.range x))
      intro z
      obtain ⟨r, hr, s, hs, hz⟩ := IntermediateField.mem_adjoin_iff_div.mp z.2
      rw [Algebra.adjoin_eq_range, AlgHom.mem_range] at hr
      rw [Algebra.adjoin_eq_range, AlgHom.mem_range] at hs
      obtain ⟨a, ha⟩ := hr
      obtain ⟨b, hb⟩ := hs
      have hInj : x.Injective := by sorry
      let g : MvPolynomial ι k ≃ₐ[k] MvPolynomial {x1 // x1 ∈ Set.range x} k :=
        MvPolynomial.renameEquiv k (Equiv.ofInjective x hInj)
      use g.symm a
      use g.symm b
      -- rw [← ha] at hz
      -- rw [← hb] at hz
      -- rw [hz]


-- IntermediateField.algebraAdjoinAdjoin.instIsFractionRingSubtypeMemSubalgebraAdjoinAdjoin could be useful
      sorry
  }

example (k K : Type) [Field k] [Field K]
    [Algebra k K] {ι : Type} (x : ι → K) (h : AlgebraicIndependent k x) : x.Injective := by
  rw [algebraicIndependent_iff_injective_aeval] at h

  sorry


/-
example (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    (h : IsTranscendenceBasis k x) :
    FractionRing (MvPolynomial ι k) ≃ₐ[k] FractionRing (Algebra.adjoin k (Set.range x)) :=
  have _ : SMul (↥(Algebra.adjoin k (Set.range x))) (FractionRing ↥(Algebra.adjoin k (Set.range x))) := sorry
  have _ : IsScalarTower k (↥(Algebra.adjoin k (Set.range x))) (FractionRing ↥(Algebra.adjoin k (Set.range x))) := by sorry
  have _ : IsScalarTower k (↥(Algebra.adjoin k (Set.range x))) (FractionRing ↥(Algebra.adjoin k (Set.range x))) := sorry
  IsFractionRing.algEquivOfAlgEquiv (AlgebraicIndependent.aevalEquiv h.1) -/

def Ksep (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) :=
  separableClosure (IntermediateField.adjoin k (Set.range x)) K

lemma top_finrank_one (K : Type) [Field K] : Module.rank (⊤ : Subfield K) K = (1 : ℕ) := by
  rw [rank_eq_of_equiv_equiv (⊤ : Subfield K).subtype (AddEquiv.refl K)
    ⟨Subfield.subtype_injective ⊤, fun a => ⟨ ⟨a, trivial⟩, rfl⟩⟩ (fun _ => fun _ => rfl)]
  exact CommSemiring.rank_self K

lemma field_extension_degree_at_least_two_imp_nonequal (K : Type) [Field K] (k : Subfield K)
    (h : (2 : ℕ) ≤ Module.rank k K) : ⊤ ≠ k := by
  by_contra hContra
  rw [← hContra] at h
  rw [top_finrank_one K] at h
  simp at h

lemma field_extension_degree_at_least_two_imp_nonequal' (K : Type) [Field K] {k : Subfield K}
    (h : Module.rank k K ≥ (2 : ℕ)) : ∃ x : K, x ∉ k := by
  by_contra hContra
  have hTopEqk : (⊤ : Subfield K) = k := by
    ext x
    simp_all
  exact (field_extension_degree_at_least_two_imp_nonequal K k h) hTopEqk

-- Assuming that the separable closure of k(x_i) in K is not all of K, this gives an element of K
-- that is not in the separable closure. This is the element `β` used in the proof of Stacks 04KM
def beta_of_FGExtension {k K : Type} [Field k] [Field K] [Algebra k K] {ι : Type} {x : ι → K}
    (hDeg : Module.rank (Ksep k K x).toSubfield K ≥
      (2 : ℕ)) :
    K :=
  Classical.choose (field_extension_degree_at_least_two_imp_nonequal' K hDeg)

def beta_of_FGExtensionProp {k K : Type} [Field k] [Field K] [Algebra k K] {ι : Type} {x : ι → K}
    (hDeg : Module.rank (Ksep k K x).toSubfield K ≥
      (2 : ℕ)) : beta_of_FGExtension hDeg ∉ (Ksep k K x) :=
  Classical.choose_spec (field_extension_degree_at_least_two_imp_nonequal' K hDeg)

def P_of_beta (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) (β : K) :
    Polynomial (IntermediateField.adjoin k (Set.range x)) :=
  minpoly (IntermediateField.adjoin k (Set.range x)) β

-- write an element of k(x_i) as a quotient of two polynomials in the x_i, and give the union of
-- the sets of coefficients of those polynomials.
def coefficients_of_element (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) (y : K) (hy : y ∈ IntermediateField.adjoin k (Set.range x)) :
    Finset k := by
  classical
  -- rw [Set.top_eq_univ] at hy
  -- rw [Set.image_univ] at hy
  rw [IntermediateField.mem_adjoin_range_iff] at hy
  let r := Classical.choose hy
  let h2 := Classical.choose_spec hy
  let s := Classical.choose h2
  let hrs := Classical.choose_spec h2
  exact r.coeffs ∪ s.coeffs

open Classical in
lemma coefficients_of_element_prop (k : Type) {K : Type} [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) (y : K) (hy : y ∈ IntermediateField.adjoin k (Set.range x)) :
    ∃ r : MvPolynomial ι k, ∃ s : MvPolynomial ι k,
      r.coeffs ∪ s.coeffs = coefficients_of_element k x y hy ∧
      y = (MvPolynomial.aeval x) r / (MvPolynomial.aeval x) s := by
  -- rw [Set.top_eq_univ] at hy
  -- rw [Set.image_univ] at hy
  rw [IntermediateField.mem_adjoin_range_iff] at hy
  use (Classical.choose hy)
  use (Classical.choose (Classical.choose_spec hy))
  refine ⟨?_, Classical.choose_spec (Classical.choose_spec hy)⟩
  unfold coefficients_of_element
  dsimp

open Classical in
def coefficients_of_S (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    (S : Finset (IntermediateField.adjoin k (Set.range x))) : Finset k :=
  Finset.biUnion S (fun s => coefficients_of_element k x s s.prop)

open Classical in
lemma coefficients_of_S_mono (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) {S T : Finset (IntermediateField.adjoin k (Set.range x))} (hST : S ⊆ T) :
    coefficients_of_S k x S ⊆ coefficients_of_S k x T := by
  unfold coefficients_of_S
  exact Finset.biUnion_subset_biUnion_of_subset_left _ hST

/-
open Classical in
lemma coefficients_of_S_prop (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) (S : Finset (IntermediateField.adjoin k (x '' ⊤))) (y : K) (hy : y ∈ S) :
    ∃ r :  MvPolynomial ι k, ∃ s : MvPolynomial ι k,
      r.coeffs ∪ s.coeffs ⊆ coefficients_of_S k x S ∧
      y = (MvPolynomial.aeval x) r / (MvPolynomial.aeval x) s := by
  sorry -/

/- open Classical in
def coefficients_of_P (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) (P : Polynomial (IntermediateField.adjoin k (x '' ⊤))) : Finset k :=
  Finset.biUnion (⊤ : Finset (Fin P.natDegree))
    (fun i => coefficients_of_element k x (P.coeff i) (by apply (P.coeff i).property))-/

open Classical in
def adjoin_pth_roots {k : Type} [Field k] (p : ℕ) (S : Set k) [ExpChar k p] :
    IntermediateField k (AlgebraicClosure k) :=
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  IntermediateField.adjoin k <|
    (frobenius (AlgebraicClosure k) p) ⁻¹' ((algebraMap k (AlgebraicClosure k)) '' S)

lemma adjoin_pth_roots_mono {k : Type} [Field k] (p : ℕ) {S T : Set k} [ExpChar k p]
    (hST : S ⊆ T) : adjoin_pth_roots p S ≤ adjoin_pth_roots p T := by
  unfold adjoin_pth_roots
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  exact IntermediateField.adjoin.mono k _ _ <| Set.preimage_mono <| Set.image_mono hST

lemma adjoin_pth_roots_of_finite_finite {k : Type} [Field k] (p : ℕ) (S : Set k) [Finite S]
    (hp : p.Prime) [ExpChar k p] : FiniteDimensional k (adjoin_pth_roots p S) := by
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  have hFin : Finite ((frobenius (AlgebraicClosure k) p) ⁻¹'
      ((algebraMap k (AlgebraicClosure k)) '' S)) := by
    have hFin' : Finite ((algebraMap k (AlgebraicClosure k)) '' S) := by infer_instance
    exact Set.Finite.preimage (Set.injOn_of_injective (frobenius_inj _ _)) hFin'
  apply IntermediateField.finiteDimensional_adjoin
  intro s hs
  apply IsIntegral.of_pow (n := p) (Nat.Prime.pos hp)
  have hs_mem : s ^ p ∈ (algebraMap k (AlgebraicClosure k))'' S := by
    simp_all only [Set.mem_preimage, Set.mem_image]
    obtain ⟨w, hw⟩ := hs
    use w
    rw [hw.2]
    exact ⟨hw.1, rfl⟩
  rw [Set.mem_image] at hs_mem
  obtain ⟨y, hy⟩ := hs_mem
  rw [← hy.2]
  exact isIntegral_algebraMap

lemma adjoin_pth_roots_purelyInseparable {k : Type} [Field k] (p : ℕ) (S : Set k) [ExpChar k p] :
    IsPurelyInseparable k (adjoin_pth_roots p S) := by
  unfold adjoin_pth_roots
  rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (AlgebraicClosure k) p]
  intro s hs
  use 1
  simp_all only [Set.mem_preimage, Set.mem_image, pow_one, RingHom.mem_range]
  obtain ⟨w, h1, h2⟩ := hs
  use w
  rw [h2]
  rfl

lemma adjoin_pth_roots_frob_img_mem {k : Type} [Field k] (p : ℕ) (S : Set k) [ExpChar k p]
    (y : k) (hy : y ∈ S) :
    have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
    algebraMap k (AlgebraicClosure k) y ∈ Subfield.map (frobenius (AlgebraicClosure k) p)
      (adjoin_pth_roots p S).toSubfield := by
  unfold adjoin_pth_roots
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  use (frobeniusEquiv (AlgebraicClosure k) p).invFun (algebraMap k _ y)
  simp only [adjoin_toSubfield, Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring,
    Subfield.coe_toSubring, SetLike.mem_coe, ← coe_frobeniusEquiv]
  refine ⟨?_, by simp⟩
  apply Subfield.mem_closure_of_mem
  right
  use y
  refine ⟨hy, ?_⟩
  simp

-- a somewhat relative version of adjoin_pth_roots_frob_img_mem, which allows for
-- adjoin_pth_roots to be embedded in the algebraic closure of a bigger field.
lemma adjoin_pth_roots_frob_img_mem' {k : Type} [Field k] (K : Type) [Field K] [Algebra k K] (p : ℕ)
    (S : Set k) [ExpChar k p] (y : K) (hy : y ∈ (algebraMap k K) '' S) :
    have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) y ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
      ((adjoin_pth_roots p S).map IsAlgClosed.lift).toSubfield := by
  have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
  unfold adjoin_pth_roots
  rw [Subfield.mem_map]
  use (frobeniusEquiv (AlgebraicClosure K) p).invFun (algebraMap K _ y)
  simp only [← coe_frobeniusEquiv]
  refine ⟨?_, by simp⟩
  unfold IntermediateField.adjoin
  simp only [coe_frobeniusEquiv, toSubfield_map, RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
    Subfield.mem_map, mem_toSubfield, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    RingHom.coe_coe]
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  obtain ⟨z, hz⟩ := (Set.mem_image _ _ _).mp hy
  use (frobeniusEquiv (AlgebraicClosure k) p).invFun (algebraMap k _ z)
  constructor
  · apply Subfield.mem_closure_of_mem
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, Set.mem_union, Set.mem_range,
      Set.mem_preimage, Set.mem_image]
    right
    use z
    refine ⟨hz.1, ?_⟩
    rw [← coe_frobeniusEquiv]
    simp
  · rw [← hz.2]
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe]
    erw [RingHom.map_frobeniusEquiv_symm]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl

variable {k : Type} [Field k] {p : ℕ} [ExpChar k p]
instance blarg : Algebra (frobenius k p).range k := sorry

-- The first lemma not in the PR anymore:
lemma adjoin_pth_roots_mem_iff {k : Type} [Field k] (p : ℕ) (S : Set k) [ExpChar k p]
    (y : AlgebraicClosure k) :
    haveI : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
    haveI : Field (frobenius k p).range := by sorry
    y ∈ adjoin_pth_roots p S ↔
      frobenius (AlgebraicClosure k) p y ∈ (algebraMap k (AlgebraicClosure k)) ''
        (@IntermediateField.adjoin (frobenius k p).range _ k _ sorry S) := by
    constructor
    · intro hy
      unfold adjoin_pth_roots at hy

      sorry
    · sorry



def k'_of_S (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    (S : Finset (IntermediateField.adjoin k (Set.range x))) (p : ℕ) [ExpChar k p] :
    IntermediateField k (AlgebraicClosure k) :=
  adjoin_pth_roots p (coefficients_of_S k x S)

lemma k'_purely_inseparable (k K : Type) [Field k] [Field K] [Algebra k K] (p : ℕ) {ι : Type}
    (x : ι → K) [ExpChar k p] (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    IsPurelyInseparable k (k'_of_S k K x S p) :=
   adjoin_pth_roots_purelyInseparable _ _

lemma k'_of_S_mono (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) {S T : Finset (IntermediateField.adjoin k (Set.range x))} (p : ℕ) [ExpChar k p]
    (hST : S ⊆ T) : k'_of_S k K x S p ≤ k'_of_S k K x T p :=
  adjoin_pth_roots_mono _ (coefficients_of_S_mono k x hST)

-- This definition is a bit ugly, but we need it for finiteness reasons.
open Classical in
def image_of_transcendence_basis (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] : Finset (IntermediateField.adjoin k (Set.range x)) :=
  Set.toFinset (Set.range (fun i => ⟨x i,
    IntermediateField.subset_adjoin k (Set.range x) <| Set.mem_range_self i⟩))

def k_transcendental_pth_roots (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    [Fintype ι] (p : ℕ) [ExpChar k p] :
      IntermediateField ((IntermediateField.adjoin k (Set.range x))) (AlgebraicClosure K) :=
  have _ : NoZeroSMulDivisors ((IntermediateField.adjoin k (Set.range x)))
    (AlgebraicClosure (IntermediateField.adjoin k (Set.range x))) :=
      GroupWithZero.toNoZeroSMulDivisors
  have _ : NoZeroSMulDivisors ((IntermediateField.adjoin k (Set.range x))) (AlgebraicClosure K) :=
    GroupWithZero.toNoZeroSMulDivisors
  (adjoin_pth_roots p (image_of_transcendence_basis k K x)).map IsAlgClosed.lift

lemma k_transcendental_pth_roots_pth_root_mem (k K : Type) [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] (i : ι) :
    have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) (x i) ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
        (k_transcendental_pth_roots k K x p).toSubfield := by
  apply adjoin_pth_roots_frob_img_mem'
  simp [IntermediateField.algebraMap_apply, image_of_transcendence_basis, Set.coe_toFinset,
        Set.mem_image, Set.mem_range, exists_exists_eq_and, exists_apply_eq_apply]

-- The isomorphism k(x_i) ≃ k(x_i^{1/p}), which identifies the x_i with the x_i^{1/p}
def k_transcendental_pth_roots_equiv (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] (hT : IsTranscendenceBasis k x) :
    IntermediateField.adjoin k (Set.range x) ≃+* k_transcendental_pth_roots k K x p := by
  sorry


lemma intermediateField_symm_mem_iff {k K L : Type} [Field k] [Field K] [Field L] (f : K ≃+* L)
    [Algebra k K] (k' : IntermediateField k K) (y : L) :
    f.symm y ∈ k' ↔ y ∈ Subfield.map f k'.toSubfield := by
  erw [Subring.mem_map_equiv]
  simp

def x_res (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) [Fintype ι] (p : ℕ)
    [ExpChar k p] : ι → IntermediateField.adjoin k (Set.range x) :=
  fun i => ⟨x i, IntermediateField.subset_adjoin k (Set.range x) <| Set.mem_range_self i⟩

-- TODO: define the new transcendence basis x' : ι → k_transcendental_pth_roots by taking the pth
-- roots of the `x i`, and show that this is again a transcendence basis. Hopefully we can use
-- something like isTranscendenceBasis_equiv.
def x' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] : ι → k_transcendental_pth_roots k K x p :=
  have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
  fun i => ⟨(frobeniusEquiv (AlgebraicClosure K) p).symm <|
      (algebraMap K (AlgebraicClosure K)) <| x i, by
        simp only [intermediateField_symm_mem_iff]
        apply k_transcendental_pth_roots_pth_root_mem⟩

-- The map k(x_i^{1/p}) →+* k(x_i) which raises everything to the pth power.
def x_x'_frob (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) [Fintype ι]
    (p : ℕ) [ExpChar k p] : k_transcendental_pth_roots k K x p →+*
      IntermediateField.adjoin k (Set.range x) := sorry
  -- RingHom.codRestrict (frobenius (k_transcendental_pth_roots k K x p) p) (IntermediateField.adjoin k (Set.range (x_res k K x p))) (by sorry)


lemma x'_AlgebraicIndependent (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    [Fintype ι] (p : ℕ) [ExpChar k p] (hA : AlgebraicIndependent k x) :
    AlgebraicIndependent k (x' k K x p) := by
  have hA' : AlgebraicIndependent k ((x_x'_frob k K x p) ∘ x' k K x p) := by sorry
  exact AlgebraicIndependent.of_ringHom_of_comp_eq (frobenius k p) (x_x'_frob k K x p) hA'
      (frobenius_inj k p) (by sorry)


lemma x'_transcendental_basis (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    [Fintype ι] (p : ℕ) [ExpChar k p] (hT : IsTranscendenceBasis k x) :
    IsTranscendenceBasis k (x' k K x p) := by
  unfold x'
  -- maybe use something like  algebraicIndependent_adjoin
  sorry

/-def k'_transcendental_pth_roots (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    IntermediateField k (AlgebraicClosure K) :=
  (k'_of_S k K x S p).map IsAlgClosed.lift ⊔
      (restrictScalars k (k_transcendental_pth_roots k K x p))-/

def k'_transcendental_pth_roots' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    IntermediateField (IntermediateField.adjoin k (Set.range x))
      (AlgebraicClosure (IntermediateField.adjoin k (Set.range x))) :=
  @adjoin_pth_roots (IntermediateField.adjoin k (Set.range x)) _ p
    (((algebraMap k _) '' coefficients_of_S k x S) ∪ (Set.range <| x_res k K x p)) _

def k'_transcendental_pth_roots'' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    IntermediateField (IntermediateField.adjoin k (Set.range x))
      (AlgebraicClosure K) :=
  haveI : NoZeroSMulDivisors (↥(IntermediateField.adjoin k (Set.range x)))
    (AlgebraicClosure K) := NoZeroSMulDivisors.instOfFaithfulSMul
  haveI : NoZeroSMulDivisors (↥(IntermediateField.adjoin k (Set.range x)))
    (AlgebraicClosure ↥(IntermediateField.adjoin k (Set.range x))) :=
    GroupWithZero.toNoZeroSMulDivisors
  (k'_transcendental_pth_roots' k K x p S).map IsAlgClosed.lift



lemma pth_roots_inclusion (k K : Type) [Field k] [Field K] (S : Set k)
    [Algebra k K] (p : ℕ) [ExpChar k p] :
    haveI : ExpChar K p := ExpChar.of_injective_algebraMap' k _
    ((adjoin_pth_roots p S).map (IsAlgClosed.lift)) ≤
      (adjoin_pth_roots p ((algebraMap k K) '' S)).restrictScalars k := by
  -- unfold adjoin_pth_roots
  intro x hx
  simp_all only [mem_restrictScalars]
  obtain ⟨y, hy1, hy2⟩ := hx
  -- TODO: use adjoin_pth_roots_mem_iff
  sorry

def adjoin_pth_roots_to_adjoin_pth_roots_algebraMap (k K : Type) [Field k] [Field K] (S : Set k)
    [Algebra k K] (p : ℕ) [ExpChar k p] :
    haveI : ExpChar K p := ExpChar.of_injective_algebraMap' k _
    adjoin_pth_roots p S →ₐ[k] adjoin_pth_roots p ((algebraMap k K) '' S) :=
    (IntermediateField.inclusion (pth_roots_inclusion k K S p)).comp
      <| (IntermediateField.equivMap (adjoin_pth_roots p S) IsAlgClosed.lift).toAlgHom


-- maybe improve the following to a scalar tower over `k` using `IsScalarTower.of_algHom`
instance k'_of_S_k'_transcendental_algebra (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    Algebra (k'_of_S k K x S p) (k'_transcendental_pth_roots'' k K x p S) := by
  apply RingHom.toAlgebra
  unfold k'_of_S k'_transcendental_pth_roots'' k'_transcendental_pth_roots'
  -- use `IntermediateField.lift_adjoin` to deal with the IsAlgClosed.lift

  -- RingHom.toAlgebra sorry
  sorry


/-def trivial_incl1 (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] :
    (IntermediateField.adjoin k (Set.range x)) →+* k_transcendental_pth_roots k K x p :=
  algebraMap ↥(IntermediateField.adjoin k (Set.range x)) ↥(k_transcendental_pth_roots k K x p)

lemma trivial_incl2' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    restrictScalars k (k_transcendental_pth_roots k K x p) ≤
      k'_transcendental_pth_roots k K x p S := by
  unfold k'_transcendental_pth_roots
  exact le_sup_right

def trivial_incl2 (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    k_transcendental_pth_roots k K x p →ₐ[k] k'_transcendental_pth_roots k K x p S :=
  IntermediateField.inclusion (trivial_incl2' k K x p S)

instance alg_k' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) [Fintype ι]
    (p : ℕ) [ExpChar k p] (S : Finset (IntermediateField.adjoin k (Set.range x))) :
      Algebra (IntermediateField.adjoin k (Set.range x)) (k'_transcendental_pth_roots k K x p S) :=
  RingHom.toAlgebra ((trivial_incl2 k K x p S).toRingHom.comp (trivial_incl1 k K x p))
-/


lemma test (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) (p : ℕ) [Fintype ι]
    [ExpChar k p] (hp : p.Prime) (y : K) (hy : y ∈ IntermediateField.adjoin k (Set.range x)) :
    letI : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) y ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
        ((k'_transcendental_pth_roots k K x p {⟨y, hy⟩})).toSubfield := by
  unfold k'_transcendental_pth_roots k'_of_S coefficients_of_S coefficients_of_element
  unfold k_transcendental_pth_roots
  /-simp only [Set.top_eq_univ, Finset.singleton_biUnion, sup_toSubfield, toSubfield_map,
    restrictScalars_toSubfield, Subfield.mem_map]-/
  obtain ⟨r, s, hS, hyrs⟩ := coefficients_of_element_prop k x y hy

  sorry


lemma test' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) (p : ℕ) [Fintype ι]
    [ExpChar k p] (hp : p.Prime) (y : IntermediateField.adjoin k (Set.range x)) :
    (algebraMap (IntermediateField.adjoin k (Set.range x)) _) y ∈
      (frobenius (k'_transcendental_pth_roots' k K x p {y}) p).range := by

  sorry

lemma P_coeff_is_pth_power_k'_of_transcendental (k K : Type) [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) [Fintype ι] (p : ℕ) [CharP k p] (hp : p.Prime) [ExpChar k p]
    (P : Polynomial (IntermediateField.adjoin k (Set.range x))) (i : ℕ) :
    (algebraMap (IntermediateField.adjoin k (Set.range x)) _) (P.coeff i) ∈
      (frobenius (k'_transcendental_pth_roots' k K x p P.coeffs) p).range := by
  unfold k'_transcendental_pth_roots'
  have hSingleton : {P.coeff i} ⊆ P.coeffs := by sorry

  exact (adjoin_pth_roots_mono p hSingleton) (test' k K x p hp (P.coeff i))

  sorry


-- Now the main reason for defining k':
lemma P_is_pth_power_k'_transcendental (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [CharP k p] (hp : p.Prime) [ExpChar k p]
    (P : Polynomial (IntermediateField.adjoin k (Set.range x))) :
    Polynomial.mapRingHom (algebraMap (IntermediateField.adjoin k (Set.range x)) _) P ∈
      (Polynomial.mapRingHom (frobenius (k'_transcendental_pth_roots' k K x p P.coeffs) p)).range :=
    by
  rw [Polynomial.mem_map_range]
  intro n
  rw [coe_mapRingHom, coeff_map]
  exact P_coeff_is_pth_power_k'_of_transcendental k K x p hp P n

-- TODO: place this in a different file, it generalizes X_pow_sub_one_separable_iff (but does
-- require the extra assumption that n is not zero, so it is not a complete generalization)
theorem X_pow_sub_C_separable_iff {F : Type*} [Field F] {n : ℕ} (x : F) (hn : 0 < n) (hx : x ≠ 0) :
    (X ^ n - C x : F[X]).Separable ↔ (n : F) ≠ 0 := by
  refine ⟨?_, fun h => separable_X_pow_sub_C_unit (Units.mk0 x hx) (IsUnit.mk0 _ h)⟩
  rw [separable_def', derivative_sub, derivative_X_pow, derivative_C, sub_zero]
  -- Suppose `(n : F) = 0`, then the derivative is `0`, so `X ^ n - 1` is a unit, contradiction.
  rintro (h : IsCoprime _ _) hn'
  rw [hn', C_0, zero_mul, isCoprime_zero_right] at h
  have hDeg : (X ^ n - C x).natDegree = n := by simp
  exact not_isUnit_of_natDegree_pos (X ^ n - C x) (hDeg.symm ▸ hn) h

-- The minimal polynomial of a non `p`th power in a field of characteristic `p` is `X ^ p - C α`
lemma minpoly_of_non_pth_power {k K : Type*} [Field k] [Field K] [Algebra k K] {p : ℕ} {α : k}
    (hp : p.Prime) [ExpChar k p] (hα : ¬ ∃ β : k, β ^ p = α) {ρ : K}
    (hρ : ρ ^ p = algebraMap k K α) :
    X ^ p - C α = minpoly k ρ := by
  have hIrred : Irreducible (X ^ p - C α) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    tauto
  apply minpoly.eq_of_irreducible_of_monic hIrred
  · simp [hρ]
  · have hDeg : (X ^ p - C α).natDegree = p := by simp
    simp [Monic.def, leadingCoeff, hDeg,
          Polynomial.coeff_C_ne_zero (Nat.ne_zero_of_lt <| Nat.Prime.pos hp)]

@[stacks 031V "(2)"]
lemma pth_power_poly_imp_pth_power {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] {α : K} (P : Polynomial k)
    (hP : P.aeval α = 0) {p : ℕ} (hp : p.Prime) [CharP k p] [ExpChar k p]
    (hQfrob_eq_P : ∃ Q : Polynomial k, P = Polynomial.map (frobenius k p) Q)
    (hSep : P.Separable) :
    ∃ β : K, β ^ p = α := by
  by_cases hα : ∃ β : K, β ^ p = α
  · assumption
  · obtain ⟨Q, hQ⟩ := hQfrob_eq_P
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) α)
      (Nat.Prime.pos hp)
    have QX_pow_p_dvd : (X ^ p - C α) ∣ Polynomial.mapAlg k K Q := by
      -- We will prove this by proving that `Q(ρ) = 0` and using that `X ^ p - C α` is the minimal
      -- polynomial of `ρ` over `K`, the result then follows from `minpoly.dvd`
      have hRoot : aeval ρ Q = 0 := by
        have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
        rw [← map_eq_zero (frobenius (AlgebraicClosure K) p), ← Polynomial.eval_map_algebraMap,
            ← Polynomial.eval₂_at_apply, frobenius_def, hρ, Polynomial.eval₂_map,
            ← RingHom.frobenius_comm, ← Polynomial.eval₂_map, ← hQ, ← Polynomial.aeval_def,
            aeval_algebraMap_eq_zero_iff]
        exact hP
      have _ : ExpChar K p := ExpChar.of_injective_algebraMap' k _
      rw [minpoly_of_non_pth_power hp hα hρ]
      apply minpoly.dvd
      rw [← hRoot, mapAlg_eq_map, aeval_map_algebraMap]
    have hQSep : (mapAlg k K Q).Separable :=
      Polynomial.Separable.map ((Polynomial.separable_map _).mp (hQ ▸ hSep))
    apply Polynomial.Separable.of_dvd hQSep at QX_pow_p_dvd
    have hαNonZero : α ≠ 0 := fun hzero => ((hzero ▸ hα)
      (by use 0; exact zero_pow (pos_iff_ne_zero.mp (Nat.Prime.pos hp))))
    have hInsep_iff_p_ne_zero := ((ne_eq _ _) ▸
      (not_iff_not.mpr (X_pow_sub_C_separable_iff α (Nat.Prime.pos hp) hαNonZero))).trans (not_not)
    have hpzero : (p : K) = 0 := by
      rw [← (CharP.charP_iff_prime_eq_zero hp), ← Algebra.charP_iff k K p]
      assumption
    exfalso
    exact hInsep_iff_p_ne_zero.mpr hpzero QX_pow_p_dvd

@[stacks 031V "(1)"]
lemma pth_power_poly_imp_pth_power' {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [hSep : Algebra.IsSeparable k K] (α : K) {p : ℕ} (hp : p.Prime)
    [ExpChar k p] [CharP k p]
    (h_pth_power_coeff : ∃ Q : Polynomial k, ((minpoly k α)) = Polynomial.map (frobenius k p) Q) :
    ∃ β : K, β ^ p = α :=
  pth_power_poly_imp_pth_power (minpoly k α) (minpoly.aeval k α) hp h_pth_power_coeff
    ((Algebra.isSeparable_def k K).mp hSep α)




open TensorProduct


variable (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A B : Subalgebra k R)
instance : Algebra A (A ⊔ B : Subalgebra k R) :=
    RingHom.toAlgebra (Subalgebra.inclusion le_sup_left).toRingHom

lemma sup_eq_adjoin :
    (A ⊔ B : Subalgebra k R) = Subalgebra.restrictScalars k (Algebra.adjoin A (B : Set R)) := by
  rw [Algebra.sup_def]
  rw [Algebra.adjoin_union_eq_adjoin_adjoin]
  rw [Algebra.adjoin_eq]


variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (L1 L2 : IntermediateField k K)

instance : Module L1 (L1 ⊔ L2 : IntermediateField k K) := RingHom.toModule
    (IntermediateField.inclusion le_sup_left).toRingHom

-- some prerequisites on the degree in a compositum that we need
lemma compositum_deg_le (L1 L2 : IntermediateField k K) (hAlg : Algebra.IsAlgebraic k L2) :
    Module.rank L1 (L1 ⊔ L2 : IntermediateField k K) ≤ Module.rank k L2 := by
  let isom : (L1 ⊔ L2 : IntermediateField k K) ≃ₗ[L1]
      (IntermediateField.adjoin L1 (L2 : Set K)) :=
    -- The isomorphism is difficult to construct directly (the problem is with `L1`-linearity),
    -- so we show that the two sides are equal as subsets of K.
    { __ := Equiv.setCongr <| by
        ext; simp only [IntermediateField.sup_def]
        rw [← IntermediateField.restrictScalars_adjoin]
        rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hRankEq : Module.rank L1 (L1 ⊔ L2 : IntermediateField k K) =
      Module.rank L1 (IntermediateField.adjoin L1 (L2 : Set K)) := LinearEquiv.rank_eq isom
  rw [hRankEq]
  exact IntermediateField.adjoin_rank_le_of_isAlgebraic_right _ _



-- Note: See valuative criterion squares for inspiration.
open CategoryTheory

def RingHom.IsPurelyInseparable' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @IsPurelyInseparable R S _ _ f.toAlgebra

lemma purelyInseparable_comp {R S T : Type} [Field R] [Field S] [Field T] (f : R →+* S)
    (g : S →+* T) (hf : f.IsPurelyInseparable') (hg : g.IsPurelyInseparable') :
    (g.comp f).IsPurelyInseparable' := by
  unfold RingHom.IsPurelyInseparable' at *
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra S T := g.toAlgebra
  let _ : Algebra R T := (g.comp f).toAlgebra
  let _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  exact IsPurelyInseparable.trans R S T

def RingHom.IsSeparablyGeneratedBy {k K : Type} [Field k] [Field K] (f : k →+* K) {ι : Type}
    (x : ι → K) : Prop := @separablyGeneratedBy k K _ _ f.toAlgebra _ x

-- Define a separably generated morphism of fields without making the transcendental basis explicit
def RingHom.IsSeparablyGenerated {k K : Type} [Field k] [Field K] (f : k →+* K) : Prop :=
  ∃ ι : Type, ∃ x : ι → K, f.IsSeparablyGeneratedBy x

-- Given a finitely generated field extension `K/k` and a transcendence basis `x : ι → K`, this
-- gives the degree of `K` over the separable closure of `k(x)`.
def Algebra.separableDegree_of_transcendenceBasis (k K : Type) [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) [Algebra.EssFiniteType k K] : ℕ :=
  Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K

def RingHom.separableDegree_of_transcendenceBasis {k K : Type} [Field k] [Field K] (f : k →+* K)
    {ι : Type} (x : ι → K) (hf : f.EssFiniteType) : ℕ :=
  @Algebra.separableDegree_of_transcendenceBasis k K _ _ f.toAlgebra _ x hf


structure inseparable_separable_extension {k K : Type} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] where -- TODO: remove Algebra.EssFiniteType
  k' : Type
  [fieldk' : Field k']
  K' : Type
  [fieldK' : Field K']
  [alg' : Algebra k' K']
  fk : k →+* k'
  fK : K →+* K'
  commSq : CommSq (CommRingCat.ofHom fk) (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (algebraMap k' K')) (CommRingCat.ofHom fK)
  purelyInsep : fk.IsPurelyInseparable'
  separablyGen : (algebraMap k' K').IsSeparablyGenerated -- TODO: this is ugly!


structure partial_inseparable_separable_extension (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (d : ℕ) {ι : Type} (x : ι → K) (hx : IsTranscendenceBasis k x)
    where
  -- The commutative square of fields
  k' : Type
  [fieldk' : Field k']
  K' : Type
  [fieldK' : Field K']
  [alg' : Algebra k' K']
  fk : k →+* k'
  fK : K →+* K'
  commSq : CommSq (CommRingCat.ofHom fk) (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (algebraMap k' K')) (CommRingCat.ofHom fK)

  -- The new transcendence basis
  x' : ι → K'
  hx' : IsTranscendenceBasis k' x'

  -- The properties that need to be satisfied:
  d' : ℕ
  hdd' : d' < d
  purelyInsep : fk.IsPurelyInseparable'
  insepDeg_eq_d : d = Module.rank (IntermediateField.adjoin k (Set.range x)) (Ksep k K x)
  insepDeg_eq_d' : d' = Module.rank (IntermediateField.adjoin k' (Set.range x')) (Ksep k' K' x')

instance (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (d : ℕ)
    {ι : Type} (x : ι → K) (hx : IsTranscendenceBasis k x)
    (S : partial_inseparable_separable_extension k K d x hx) : Field S.k' := S.fieldk'

instance (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (d : ℕ)
    {ι : Type} (x : ι → K) (hx : IsTranscendenceBasis k x)
    (S : partial_inseparable_separable_extension k K d x hx) : Field S.K' := S.fieldK'

instance (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (d : ℕ)
    {ι : Type} (x : ι → K) (hx : IsTranscendenceBasis k x)
    (S : partial_inseparable_separable_extension k K d x hx) : Algebra S.k' S.K' := S.alg'

-- TODO: this is not yet true, need some assumptions
instance partial_inseparable_separable_extension_right_EssFiniteType (k K : Type) [Field k]
    [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (d : ℕ) {ι : Type} (x : ι → K)
    (hx : IsTranscendenceBasis k x) (sq : partial_inseparable_separable_extension k K d x hx) :
    Algebra.EssFiniteType sq.k' sq.K' := by
  sorry

def glue_partial_inseparable_separable_extension {k K : Type} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (d : ℕ) {ι : Type} (x : ι → K) (hx : IsTranscendenceBasis k x)
    (left_ext : partial_inseparable_separable_extension k K d x hx)
    (right_ext : partial_inseparable_separable_extension left_ext.k' left_ext.K' left_ext.d'
        left_ext.x' left_ext.hx') :
  partial_inseparable_separable_extension k K d x hx
  := {
    k' := right_ext.k'
    K' := right_ext.K'
    fk := RingHom.comp right_ext.fk left_ext.fk
    fK := RingHom.comp right_ext.fK left_ext.fK
    commSq := CategoryTheory.CommSq.horiz_comp left_ext.commSq right_ext.commSq
    x' := right_ext.x'
    hx' := right_ext.hx'
    d' := right_ext.d'
    hdd' := lt_trans right_ext.hdd' left_ext.hdd'
    purelyInsep := purelyInseparable_comp _ _ left_ext.purelyInsep right_ext.purelyInsep
    insepDeg_eq_d := left_ext.insepDeg_eq_d
    insepDeg_eq_d' := right_ext.insepDeg_eq_d'
  }

-- given a finitely generated field extension with `d ≥ 2`, give a partial inseparable separable
-- extension square of it
def partial_extension_square_of_FGExtension {k K : Type} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (d : ℕ) {ι : Type} (x : ι → K) (hx : IsTranscendenceBasis k x)
    (hd : Module.rank (Ksep k K x) K ≥ 2) (p : ℕ) (hp : p.Prime) [ExpChar k p] [Fintype ι] :
    partial_inseparable_separable_extension k K d x hx :=
    let β : K := beta_of_FGExtension hd
    let P : (IntermediateField.adjoin k (Set.range x))[X] := P_of_beta k K x β
    {
      k' := k'_of_S k K x P.coeffs p
      K' := (((⊤ : IntermediateField k K).map (algHom k K (AlgebraicClosure K))) ⊔
        (k'_transcendental_pth_roots'' k K x p P.coeffs).restrictScalars k :
          IntermediateField k (AlgebraicClosure K))
      alg' :=
        let i1 : k'_of_S k K x P.coeffs p →+* (k'_transcendental_pth_roots'' k K x p P.coeffs) :=
          algebraMap _ _ -- uses the instance k'_of_S_k'_transcendental_algebra
        let i2 : (k'_transcendental_pth_roots'' k K x p P.coeffs) →+*
            (((⊤ : IntermediateField k K).map (algHom k K (AlgebraicClosure K))) ⊔
            (k'_transcendental_pth_roots'' k K x p P.coeffs).restrictScalars k :
            IntermediateField k (AlgebraicClosure K)) :=
          -- (IntermediateField.inclusion le_sup_right).toRingHom
          sorry
        RingHom.toAlgebra <| i2.comp i1
      fk := RingHom.smulOneHom
      fK :=  ((IntermediateField.inclusion le_sup_left).toRingHom).comp
        ((IntermediateField.equivMap (⊤ : IntermediateField k K)
          (algHom k K (AlgebraicClosure K))).toRingHom.comp
          IntermediateField.topEquiv.symm.toRingHom)
      commSq := sorry -- should be automatic if `alg'`, `fk` and `fK` are `k`-linear
      x' := x' k K x p -- compose with a le_sup_right.toRingHom
      hx' := sorry
      d' := sorry
      hdd' := sorry -- uses `compositum_deg_le`
      purelyInsep := sorry -- uses that `adjoinPthRoots` gives a purely inseparable extension
      insepDeg_eq_d := sorry
      insepDeg_eq_d' := sorry -- should use definition of `d'`
    }

example (k K : Type) [Field k] [Field K] [Algebra k K] : K →ₐ[k] AlgebraicClosure K :=
  algHom k K (AlgebraicClosure K)

example (k K : Type) [Field k] [Field K] [Algebra k K] : IntermediateField k (AlgebraicClosure K) :=
  (⊤ : IntermediateField k K).map (algHom k K (AlgebraicClosure K))
