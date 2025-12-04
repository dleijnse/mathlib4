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

def Ksep (k K : Type) [Field k] [Field K] [Algebra k K] (ι : Type) (x : ι → K) :=
  separableClosure (IntermediateField.adjoin k (x '' ⊤)) K

def P_of_beta (k K : Type) [Field k] [Field K] [Algebra k K] (ι : Type) (x : ι → K) (β : K) :
    Polynomial (IntermediateField.adjoin k (x '' ⊤)) :=
  minpoly (IntermediateField.adjoin k (x '' ⊤)) β

-- write an element of k(x_i) as a quotient of two polynomials in the x_i, and give the union of
-- the sets of coefficients of those polynomials.
def coefficients_of_element (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) (y : K) (hy : y ∈ IntermediateField.adjoin k (x '' ⊤)) :
    Finset k := by
  classical
  rw [Set.top_eq_univ] at hy
  rw [Set.image_univ] at hy
  rw [IntermediateField.mem_adjoin_range_iff] at hy
  let r := Classical.choose hy
  let h2 := Classical.choose_spec hy
  let s := Classical.choose h2
  let hrs := Classical.choose_spec h2
  exact r.coeffs ∪ s.coeffs

open Classical in
lemma coefficients_of_element_prop (k : Type) {K : Type} [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) (y : K) (hy : y ∈ IntermediateField.adjoin k (x '' ⊤)) :
    ∃ r : MvPolynomial ι k, ∃ s : MvPolynomial ι k,
      r.coeffs ∪ s.coeffs = coefficients_of_element k x y hy ∧
      y = (MvPolynomial.aeval x) r / (MvPolynomial.aeval x) s := by
  rw [Set.top_eq_univ] at hy
  rw [Set.image_univ] at hy
  rw [IntermediateField.mem_adjoin_range_iff] at hy
  use (Classical.choose hy)
  use (Classical.choose (Classical.choose_spec hy))
  refine ⟨?_, Classical.choose_spec (Classical.choose_spec hy)⟩
  unfold coefficients_of_element
  dsimp

open Classical in
def coefficients_of_S (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    (S : Finset (IntermediateField.adjoin k (x '' ⊤))) : Finset k :=
  Finset.biUnion S (fun s => coefficients_of_element k x s s.prop)

/-
open Classical in
lemma coefficients_of_S_prop (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) (S : Finset (IntermediateField.adjoin k (x '' ⊤))) (y : K) (hy : y ∈ S) :
    ∃ r :  MvPolynomial ι k, ∃ s : MvPolynomial ι k,
      r.coeffs ∪ s.coeffs ⊆ coefficients_of_S k x S ∧
      y = (MvPolynomial.aeval x) r / (MvPolynomial.aeval x) s := by
  sorry -/

open Classical in
def coefficients_of_P {k K : Type} [Field k] [Field K] [Algebra k K] (ι : Type)
    (x : ι → K) (P : Polynomial (IntermediateField.adjoin k (x '' ⊤))) : Finset k :=
  Finset.biUnion (⊤ : Finset (Fin P.natDegree))
    (fun i => coefficients_of_element k x (P.coeff i) (by apply (P.coeff i).property))

open Classical in
def adjoin_pth_roots {k : Type} [Field k] (p : ℕ) (S : Set k) [ExpChar k p] :
    IntermediateField k (AlgebraicClosure k) :=
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  IntermediateField.adjoin k <|
    (frobenius (AlgebraicClosure k) p) ⁻¹' ((algebraMap k (AlgebraicClosure k)) '' S)

lemma adjoin_pth_roots_of_finite_finite {k : Type} [Field k] (p : ℕ) (S : Set k) [Finite S]
    (hp : p.Prime) [ExpChar k p] : FiniteDimensional k (adjoin_pth_roots p S) := by
  have _ : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _
  have hFin : Finite ((frobenius (AlgebraicClosure k) p) ⁻¹'
      ((algebraMap k (AlgebraicClosure k)) '' S)) := by
    have hFin' : Finite ((algebraMap k (AlgebraicClosure k)) '' S) := by infer_instance
    have hInj : Function.Injective (frobenius (AlgebraicClosure k) p) := frobenius_inj _ _
    exact Set.Finite.preimage (Set.injOn_of_injective hInj) hFin'
  apply IntermediateField.finiteDimensional_adjoin
  intro s hs
  apply IsIntegral.of_pow (n := p) (Nat.Prime.pos hp)
  have hs_mem : s ^ p ∈ (algebraMap k (AlgebraicClosure k))'' S := by
    simp_all only [Set.mem_preimage, Set.mem_image]
    obtain ⟨w, hw⟩ := hs
    use w
    rw [hw.2]
    exact ⟨hw.1, rfl⟩
  simp only [Set.mem_image] at hs_mem
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
    have hVeryStupid : IsAlgClosed.lift (R := k) (S := AlgebraicClosure k)
        ((EquivLike.toEquiv (frobeniusEquiv (AlgebraicClosure k) p)).symm
          ((algebraMap k (AlgebraicClosure k)) z))
        = (IsAlgClosed.lift (R := k) (S := AlgebraicClosure k) (M := AlgebraicClosure K)).toRingHom
          (((frobeniusEquiv (AlgebraicClosure k) p)).symm
            ((algebraMap k (AlgebraicClosure k)) z)) := by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rfl
    rw [hVeryStupid]
    rw [RingHom.map_frobeniusEquiv_symm]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl

def k'_of_S (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    (S : Finset (IntermediateField.adjoin k (x '' ⊤))) (p : ℕ) [ExpChar k p] :
    IntermediateField k (AlgebraicClosure k) :=
  -- letI : ExpChar K p := ExpChar.of_injective_algebraMap' k _
  adjoin_pth_roots p (coefficients_of_S k x S)

lemma k'_purely_inseparable (k K : Type) [Field k] [Field K] [Algebra k K] (p : ℕ) {ι : Type}
    (x : ι → K) [ExpChar k p] (S : Finset (IntermediateField.adjoin k (x '' ⊤))) :
    IsPurelyInseparable k (k'_of_S k K x S p) :=
   adjoin_pth_roots_purelyInseparable _ _

-- This definition is a bit ugly, but we need it for finiteness reasons.
open Classical in
def image_of_transcendence_basis (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] : Finset (IntermediateField.adjoin k (x '' ⊤)) :=
  Set.toFinset ((fun i => ⟨x i, by apply IntermediateField.algebra_adjoin_le_adjoin k _ <|
    mem_adjoin_of_mem <| Set.mem_image_of_mem x _ ; exact
      (Set.top_eq_univ ▸ Set.mem_univ i) ⟩) '' ⊤)

def k_transcendental_pth_roots (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    [Fintype ι] (p : ℕ) [ExpChar k p] : IntermediateField ((IntermediateField.adjoin k (x '' ⊤)))
      (AlgebraicClosure K) :=
  have _ : NoZeroSMulDivisors ((IntermediateField.adjoin k (x '' ⊤)))
    (AlgebraicClosure (IntermediateField.adjoin k (x '' ⊤))) := GroupWithZero.toNoZeroSMulDivisors
  have _ : NoZeroSMulDivisors ((IntermediateField.adjoin k (x '' ⊤))) (AlgebraicClosure K) :=
    GroupWithZero.toNoZeroSMulDivisors
  (adjoin_pth_roots p (image_of_transcendence_basis k K x)).map IsAlgClosed.lift

lemma k_transcendental_pth_roots_pth_root_mem (k K : Type) [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] (i : ι) :
    have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) (x i) ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
        (k_transcendental_pth_roots k K x p).toSubfield := by
  apply adjoin_pth_roots_frob_img_mem'
  simp [Set.top_eq_univ, IntermediateField.algebraMap_apply, image_of_transcendence_basis,
    Set.image_univ, Set.coe_toFinset, Set.mem_image, Set.mem_range, exists_exists_eq_and,
    exists_apply_eq_apply]

-- The isomorphism k(x_i) ≃ k(x_i^{1/p}), which identifies the x_i with the x_i^{1/p}
def k_transcendental_pth_roots_equiv (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] (hT : IsTranscendenceBasis k x) :
    IntermediateField.adjoin k (x '' ⊤) ≃+* k_transcendental_pth_roots k K x p := by
  sorry


lemma intermediateField_symm_mem_iff {k K L : Type} [Field k] [Field K] [Field L] (f : K ≃+* L)
    [Algebra k K] (k' : IntermediateField k K) (y : L) :
    f.symm y ∈ k' ↔ y ∈ Subfield.map f k'.toSubfield := by
  erw [Subring.mem_map_equiv]
  simp

def x_res (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) [Fintype ι] (p : ℕ)
    [ExpChar k p] : ι → IntermediateField.adjoin k (x '' ⊤) :=
  fun i => ⟨x i, by sorry⟩

-- TODO: define the new transcendence basis x' : ι → k_transcendental_pth_roots by taking the pth
-- roots of the `x i`, and show that this is again a transcendence basis. Hopefully we can use
-- something like isTranscendenceBasis_equiv.
def x' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] : ι → k_transcendental_pth_roots k K x p :=
  have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
  fun i => ⟨(frobeniusEquiv (AlgebraicClosure K) p).symm ∘
      (algebraMap K (AlgebraicClosure K)) ∘ x <| i, by
        simp only [Set.top_eq_univ, Function.comp_apply, intermediateField_symm_mem_iff]
        apply k_transcendental_pth_roots_pth_root_mem⟩

-- The map k(x_i^{1/p}) →+* k(x_i) which raises everything to the pth power.
def x_x'_frob (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) [Fintype ι]
    (p : ℕ) [ExpChar k p] : k_transcendental_pth_roots k K x p →+*
      IntermediateField.adjoin k (x '' ⊤) := sorry
  -- RingHom.codRestrict (frobenius (k_transcendental_pth_roots k K x p) p) (IntermediateField.adjoin k ((x_res k K x p) '' ⊤)) sorry


lemma x'_AlgebraicIndependent (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    [Fintype ι] (p : ℕ) [ExpChar k p] (hA : AlgebraicIndependent k x) :
    AlgebraicIndependent k (x' k K x p) := by
  have hA' : AlgebraicIndependent k ((x_x'_frob k K x p) ∘ x' k K x p) := sorry
  exact AlgebraicIndependent.of_ringHom_of_comp_eq (frobenius k p) (x_x'_frob k K x p) hA'
      (frobenius_inj k p) sorry


lemma x'_transcendental_basis (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K)
    [Fintype ι] (p : ℕ) [ExpChar k p] (hT : IsTranscendenceBasis k x) :
    IsTranscendenceBasis k (x' k K x p) := by
  unfold x'
  simp only [Set.top_eq_univ, Function.comp_apply]
  -- maybe use something like  algebraicIndependent_adjoin
  sorry

def k'_transcendental_pth_roots (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (x '' ⊤))) : IntermediateField k (AlgebraicClosure K) :=
  (k'_of_S k K x S p).map IsAlgClosed.lift ⊔
      (restrictScalars k (k_transcendental_pth_roots k K x p))

def trivial_incl1 (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p] :
    (IntermediateField.adjoin k (x '' ⊤)) →+* k_transcendental_pth_roots k K x p :=
  algebraMap ↥(IntermediateField.adjoin k (x '' ⊤)) ↥(k_transcendental_pth_roots k K x p)

lemma trivial_incl2' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (x '' ⊤))) :
    restrictScalars k (k_transcendental_pth_roots k K x p) ≤
      k'_transcendental_pth_roots k K x p S := by
  unfold k'_transcendental_pth_roots
  exact le_sup_right

def trivial_incl2 (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [ExpChar k p]
    (S : Finset (IntermediateField.adjoin k (x '' ⊤))) :
    k_transcendental_pth_roots k K x p →ₐ[k] k'_transcendental_pth_roots k K x p S :=
  IntermediateField.inclusion (trivial_incl2' k K x p S)

instance alg_k' (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) [Fintype ι]
    (p : ℕ) [ExpChar k p] (S : Finset (IntermediateField.adjoin k (x '' ⊤))) :
      Algebra (IntermediateField.adjoin k (x '' ⊤)) (k'_transcendental_pth_roots k K x p S) :=
  RingHom.toAlgebra ((trivial_incl2 k K x p S).toRingHom.comp (trivial_incl1 k K x p))


lemma test (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type} (x : ι → K) (p : ℕ) [Fintype ι]
    [ExpChar k p] (hp : p.Prime) (y : K) (hy : y ∈ IntermediateField.adjoin k (x '' ⊤)) :
    letI : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) y ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
        ((k'_transcendental_pth_roots k K x p {⟨y, hy⟩})).toSubfield := by
  unfold k'_transcendental_pth_roots k'_of_S coefficients_of_S coefficients_of_element
  unfold k_transcendental_pth_roots
  /-simp only [Set.top_eq_univ, Finset.singleton_biUnion, sup_toSubfield, toSubfield_map,
    restrictScalars_toSubfield, Subfield.mem_map]-/
  obtain ⟨r, s, hS, hyrs⟩ := coefficients_of_element_prop k x y hy


  sorry


lemma P_coeff_is_pth_power_k'_of_transcendental (k K : Type) [Field k] [Field K] [Algebra k K]
    {ι : Type} (x : ι → K) [Fintype ι] (p : ℕ) [CharP k p] (hp : p.Prime) [ExpChar k p]
    (P : Polynomial (IntermediateField.adjoin k (x '' ⊤))) (i : ℕ) :
    P.coeff i ∈ (frobenius _ p).range := by

  sorry

-- Now the main reason for defining k':
lemma P_is_pth_power_k'_transcendental (k K : Type) [Field k] [Field K] [Algebra k K] {ι : Type}
    (x : ι → K) [Fintype ι] (p : ℕ) [CharP k p] (hp : p.Prime) [ExpChar k p]
    (P : Polynomial (IntermediateField.adjoin k (x '' ⊤))) :
    ∃ Q : Polynomial (k'_transcendental_pth_roots k K x p P), Polynomial.map
      (algebraMap (IntermediateField.adjoin k (x '' ⊤)) _)
      P = Polynomial.map (frobenius _ p) Q := by

  sorry


-- TODO: place this in a different file, it generalizes X_pow_sub_one_separable_iff (but does
-- require the extra assumption that n is not zero, so it is not a complete generalization)
theorem X_pow_sub_C_separable_iff {F : Type} [Field F] {n : ℕ} (x : F) (hn : n > 0)
    (hx : IsUnit x) : (X ^ n - C x : F[X]).Separable ↔ (n : F) ≠ 0 := by
  refine ⟨?_, fun h => separable_X_pow_sub_C_unit hx.unit (IsUnit.mk0 _ h)⟩
  rw [separable_def', derivative_sub, derivative_X_pow, derivative_C, sub_zero]
  rintro (h : IsCoprime _ _) hn'
  rw [hn', C_0, zero_mul, isCoprime_zero_right] at h
  have hDeg : (X ^ n - C x).natDegree = n := by simp
  exact not_isUnit_of_natDegree_pos (X ^ n - C x) (hDeg.symm ▸ hn) h

-- The minimal polynomial of a non pth power in a field of characteristic p is X ^ p - C α
lemma minpoly_of_non_pth_power {k K : Type} [Field k] [Field K] [Algebra k K] {p : ℕ} {α : k}
    (hp : p.Prime) [ExpChar k p] (hα : ¬ ∃ β : k, β ^ p = α) (ρ : K)
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
lemma pth_power_poly_imp_pth_power (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] (α : K) (P : Polynomial k)
    (hP : P.aeval α = 0) (p : ℕ) (hp : p.Prime) [CharP k p] [ExpChar k p]
    (hQfrob_eq_P : ∃ Q : Polynomial k, P = Polynomial.map (frobenius k p) Q)
    (hSep : P.Separable) :
    ∃ β : K, β ^ p = α := by
  by_cases hα : ∃ β : K, β ^ p = α
  · assumption
  · obtain ⟨Q, hQ⟩ := hQfrob_eq_P
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) α)
      (Nat.Prime.pos hp)
    have QX_pow_p_dvd : (X ^ p - C α) ∣ Polynomial.mapAlg k K Q := by
      -- We will prove this by proving that X ^ p - C α is the minimal polynomial of ρ over K and
      -- that Q(ρ) = 0, the result then follows from `minpoly.dvd`
      have hRoot : aeval ρ (X ^ p - C α) = 0 ∧ aeval ρ Q = 0 := by
        constructor
        · simp [hρ]
        · have _ : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
          have hFrob : frobenius (AlgebraicClosure K) p ((aeval ρ) Q) = 0 := by
            rw [← Polynomial.eval_map_algebraMap, ← Polynomial.eval₂_at_apply, frobenius_def, hρ,
                Polynomial.eval₂_map, ← RingHom.frobenius_comm, ← Polynomial.eval₂_map, ← hQ,
                ← Polynomial.aeval_def, aeval_algebraMap_eq_zero_iff]
            exact hP
          subst hQ
          simp_all only [not_exists, map_eq_zero]
      have _ : ExpChar K p := ExpChar.of_injective_algebraMap' k _
      rw [minpoly_of_non_pth_power hp hα ρ hρ]
      apply minpoly.dvd
      rw [← hRoot.2, mapAlg_eq_map, aeval_map_algebraMap]
    have hQSep : (mapAlg k K Q).Separable :=
      Polynomial.Separable.map ((Polynomial.separable_map _).mp (hQ ▸ hSep))
    apply Polynomial.Separable.of_dvd hQSep at QX_pow_p_dvd
    have hαUnit : IsUnit α := by
      rw [isUnit_iff_ne_zero]
      by_contra hzero
      exact ((hzero ▸ hα) (by use 0; exact zero_pow (pos_iff_ne_zero.mp (Nat.Prime.pos hp))))
    have hInsep_iff_p_ne_zero := ((ne_eq _ _) ▸
      (not_iff_not.mpr (X_pow_sub_C_separable_iff α (Nat.Prime.pos hp) hαUnit))).trans (not_not)
    have hpzero : (p : K) = 0 := by
      rw [← (CharP.charP_iff_prime_eq_zero hp), ← Algebra.charP_iff k K p]
      assumption
    exfalso
    exact hInsep_iff_p_ne_zero.mpr hpzero QX_pow_p_dvd

@[stacks 031V "(1)"]
lemma pth_power_poly_imp_pth_power' (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [hSep : Algebra.IsSeparable k K] (α : K) (p : ℕ) (hp : p.Prime)
    [ExpChar k p] [CharP k p]
    (h_pth_power_coeff : ∃ Q : Polynomial k, ((minpoly k α)) = Polynomial.map (frobenius k p) Q) :
    ∃ β : K, β ^ p = α :=
  pth_power_poly_imp_pth_power k K α (minpoly k α) (minpoly.aeval k α) p hp h_pth_power_coeff
    ((Algebra.isSeparable_def k K).mp hSep α)




open TensorProduct
variable (R S : Type) [Field R] [Field S] [Algebra R S]
variable (M : Type) [AddCommGroup M] [Module R M]

example : Module.finrank S (S ⊗[R] M) = Module.finrank R M := by
  exact Module.finrank_baseChange

variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (L1 L2 : IntermediateField k K)

instance : Algebra L1 (L1 ⊔ L2 : IntermediateField k K) := RingHom.toAlgebra
      (IntermediateField.inclusion le_sup_left).toRingHom


def map_to_compositum : L1 ⊗[k] L2 →ₐ[L1] (L1 ⊔ L2 : IntermediateField k K) :=
  LinearMap.liftBaseChange (IntermediateField.inclusion le_sup_left)

lemma map_to_compositum.surjective : Function.Surjective (map_to_compositum L1 L2) := by
  sorry

-- some prerequisites on the degree in a compositum that we need
lemma compositum_deg_le (L1 L2 : IntermediateField k K) (hFin : Module.Finite k L2) :
    letI : Module L1 (L1 ⊔ L2 : IntermediateField k K) := RingHom.toModule
      (IntermediateField.inclusion le_sup_left).toRingHom
    Module.finrank L1 (L1 ⊔ L2 : IntermediateField k K) ≤ Module.finrank k L2 := by

  sorry




open CategoryTheory

variable (k : Type) [Field k]
variable (S : CategoryTheory.Square FieldCat)
variable (K : Type) [Field K]
variable (f : k →+* K) (h : RingHom.EssFiniteType f)
instance : Algebra k K := f.toAlgebra


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


-- This is the type of square we seek
def IsExtensionSquare (S : CategoryTheory.Square FieldCat) : Prop :=
  S.f₁₂.hom'.IsPurelyInseparable' ∧ S.f₁₃ = Arrow.mk (FieldCat.ofHom f) ∧
  @RingHom.IsSeparablyGenerated S.X₂ S.X₄ _ _ S.f₂₄.hom'


lemma ExtensionSquareX₁ (hE : IsExtensionSquare k K f S) : S.X₁ = k := by
  obtain ⟨_, hA, _⟩ := hE
  rw [Arrow.mk_eq_mk_iff] at hA
  obtain ⟨hX, _⟩ := hA
  simp_all only

lemma ExtensionSquareX₃ (hE : IsExtensionSquare k K f S) : S.X₃ = K := by
  obtain ⟨_, hA, _⟩ := hE
  rw [Arrow.mk_eq_mk_iff] at hA
  obtain ⟨hX, hY, _⟩ := hA
  simp_all only


/-
lemma ExtensionSquare_right_of_purely_inseparable_isExtensionSquare {k K : Type} (f : k →+* K)
    (Sl Sr : Square FieldCat) (hInsep : Sl.f₁₂.hom'.IsPurelyInseparable Sl.f₁₂)
    (hExt : IsExtensionSquare _ _ _ _ Sr) : IsExtensionSquare CategoryTheory.CommSq.horiz_comp
-/

-- Final goal:
theorem exists_ExtensionSquare : ∃ Sq : CategoryTheory.Square FieldCat,
    IsExtensionSquare k K f Sq := by sorry


-- Then have some basic API theorems, such as horizontal and vertical compositions of extension
-- squares are again an extension square. After that, build the functions needed to inductively
-- build an extension square out of a morphism of Fields of Essentially Finite Type.

example (f : k →+* K) : k ⟶ K := SemiRingCat.ofHom f


variable (C : Type) [Category C] {X Y : C} (f : X ⟶ Y)
variable (Sq : Square C)
variable (A B : Arrow C)

example (h : A = B) : A.left = B.left := by exact congrArg Comma.left h

variable (S1 S2 : Square FieldCat)
variable (hGlue : Arrow.mk S1.f₂₄ = Arrow.mk S2.f₁₃)


#check Square.mk
-- #check CategoryTheory.CommSq.horiz_comp (Square.commSq S1) (Square.commSq S2)

variable (ι : Type) (x : ι → K) [Algebra k K]
variable (h : IsTranscendenceBasis k x)
