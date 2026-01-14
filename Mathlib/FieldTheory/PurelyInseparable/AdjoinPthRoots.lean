/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The field extension obtained by adjoining pth roots to a field of characteristic p

In this file we construct the extension of a field of characteristic `p` obtained by adjoining
the `p`-th roots of a subset.

## Main definitions

- `adjoin_pth_roots`

## Main results

- `adjoin_pth_roots.finite_of_finite`: if `S` is finite, then `(adjoin_pth_roots p S) / k` is a
  finite field extension

- `adjoin_pth_roots.purelyInseparable`: the field extension `(adjoin_pth_roots p S) / k` is purely
  inseparable

- `adjoin_pth_roots.mem_frobenius_img`: every element of `S` is in the image of the frobenius
  morphism on `adjoin_pth_roots p S`.

-/

@[expose] public section

-- some prerequisites:
section Integral

open Polynomial

lemma IsIntegral_of_p_power_mem (R S : Type) [CommRing R] [CommRing S] [Algebra R S] {p : ℕ}
    [ExpChar S p] (hp : ∀ x : S, frobenius S p x ∈ (algebraMap R S).range) :
    Algebra.IsIntegral R S := by
  rw [Algebra.isIntegral_iff]
  intro x
  obtain ⟨y, hy⟩ := hp x
  use X ^ p - C y
  rw [frobenius_def] at hy
  simp [Polynomial.Monic.def, Nat.ne_zero_iff_zero_lt.mp (expChar_ne_zero S p), hy]

end Integral


open IntermediateField
open MvPolynomial

noncomputable section

section CommRing

variable {A : Type} [CommRing A]
variable (p : ℕ) [ExpChar A p]
variable (S : Set A)

def adjoinPthRootsIdeal : Ideal (MvPolynomial S A) :=
  Ideal.span <| Set.range (fun (s : S) => (X s) ^ p - C s.1)

-- TODO: need to quotient out by nilradical to get a field again if A is a field.
def adjoinPthRoots : Type :=
  MvPolynomial S A ⧸ adjoinPthRootsIdeal p S
deriving CommRing, Algebra A, Algebra (MvPolynomial S A), IsScalarTower A (MvPolynomial S A)

def adjoinPthRootsReduced : Type :=
  adjoinPthRoots p S ⧸ nilradical (adjoinPthRoots p S)
deriving Algebra A, Algebra (adjoinPthRoots p S), CommRing

omit [ExpChar A p] in
lemma algebraMap_eq_C_quot_mk (a : A) :
    (algebraMap A (adjoinPthRoots p S)) a = Ideal.Quotient.mk (adjoinPthRootsIdeal p S) (C a) := by
  rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq]
  exact IsScalarTower.algebraMap_apply A (MvPolynomial (↑S) A) (adjoinPthRoots p S) a

lemma algebraMap_inj : Function.Injective (algebraMap A (adjoinPthRoots p S)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext x

  sorry

example (X Y : Type) (f : X → Y) (hf : f.Injective) [Nontrivial X] : Nontrivial Y := by
  exact Function.Injective.nontrivial hf

instance adjoinPthRoots_nontrivial [Nontrivial A] : Nontrivial (adjoinPthRoots p S) :=
  Function.Injective.nontrivial <| algebraMap_inj p S

instance adjoinPthRootsExpChar : ExpChar (adjoinPthRoots p S) p :=
  expChar_of_injective_ringHom (algebraMap_inj p S) p

omit [ExpChar A p] in
lemma adjoinPthRootsIdeal_mem (s : S) : (X s) ^ p - C s.1 ∈ adjoinPthRootsIdeal p S :=
  Ideal.mem_span_range_self

lemma X_p_power_mem (s : S) :
    frobenius (adjoinPthRoots p S) p (Ideal.Quotient.mk  _ (X s)) ∈ (algebraMap A _).range := by
  rw [RingHom.mem_range]
  use s
  rw [frobenius_def, algebraMap_eq_C_quot_mk]
  apply Eq.symm
  erw [Ideal.Quotient.eq]
  dsimp only
  exact adjoinPthRootsIdeal_mem p S s

lemma p_power_mem (x : adjoinPthRoots p S) :
    frobenius (adjoinPthRoots p S) p x ∈ (algebraMap A _).range := by
  let ⟨y, hy⟩ := Quot.exists_rep x
  have h : y = ∑ v ∈ y.support, (monomial v) (coeff v y) := MvPolynomial.as_sum y
  rw [← hy, h, Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk]
  repeat rw [map_sum]
  apply Subring.sum_mem (algebraMap A _).range
  intro v hv
  rw [MvPolynomial.monomial_eq]
  repeat rw [map_mul]
  apply Subring.mul_mem
  · use frobenius A p (coeff v y)
    rw [RingHom.map_frobenius]
    rfl
  · unfold Finsupp.prod
    repeat rw [map_prod]
    apply Subring.prod_mem
    intro i hi
    repeat rw [map_pow]
    exact Subring.pow_mem _ (X_p_power_mem _ _ _) _

lemma units_complement_maximal (R : Type) [CommRing R] (I : Ideal R) (h1 : 1 ∉ I)
    (h : ∀ x : R, x ∉ I → IsUnit x) : I.IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨h1, ?_⟩
  intro J x hIJ hxI hxJ
  rw [← mul_one x] at hxJ
  exact (Ideal.unit_mul_mem_iff_mem J (h x hxI)).mp hxJ

lemma one_not_mem_nilradical (R : Type) [CommSemiring R] [Nontrivial R] : 1 ∉ nilradical R := by
  rw [mem_nilradical]
  exact not_isNilpotent_one

instance adjoinPthRoots_finiteType [Finite S] : Algebra.FiniteType A (adjoinPthRoots p S) := by
  unfold adjoinPthRoots
  infer_instance

instance adjoinPthRoots_Integral : Algebra.IsIntegral A (adjoinPthRoots p S) :=
  IsIntegral_of_p_power_mem p A (adjoinPthRoots p S) (p_power_mem p S)

-- Do we even need this? Or will it be automatically inferred?
lemma adjoinPthRoots_finite_of_finite [Finite S] : Module.Finite A (adjoinPthRoots p S) :=
  Algebra.IsIntegral.finite

end CommRing

section Field

variable {k : Type} [Field k]
variable (p : ℕ) [ExpChar k p]
variable (S : Set k)

instance adjoinPthRoots_of_field_nilradical_maximal [ExpChar k p] :
    (nilradical (adjoinPthRoots p S)).IsMaximal := by
  apply units_complement_maximal
  · exact one_not_mem_nilradical _
  · intro x hx
    -- use that x ^ p is a nonzero element of A. Since A is a field, x ^ p is a unit
    rw [← isUnit_pow_iff (expChar_ne_zero k p)]
    have hNonZero : x ^ p ≠ 0 := by
      rw [not_iff_not.mpr mem_nilradical] at hx
      tauto
    obtain ⟨y, hy⟩ := p_power_mem p S x
    rw [frobenius_def] at hy
    have hyz : y ≠ 0 := by
      intro h
      apply hNonZero
      rw [← hy, h]
      exact map_zero _
    rw [← hy]
    exact (isUnit_iff_ne_zero.mpr hyz).map (algebraMap _ _)

instance adjointPthRootsReducedField :
    Field (adjoinPthRootsReduced p S) := by
  unfold adjoinPthRootsReduced
  apply Ideal.Quotient.field

instance adjoinPthRoots_purelyInseparable : IsPurelyInseparable k (adjoinPthRoots p S) := by
  rw [isPurelyInseparable_iff_pow_mem]
  sorry

end Field


-- Old stuff:

lemma adjoinPthRoots_mono {S T : Set k} (hST : S ⊆ T) :
    adjoinPthRoots p S ≤ adjoinPthRoots p T :=
  IntermediateField.adjoin.mono k _ _ <| Set.preimage_mono <| Set.image_mono hST

/-- If the set `S` whose `p`-th roots we adjoin is finite, then the obtained field extension
`(adjoin_pth_roots p S) / k` is finite. -/
lemma adjoinPthRoots_finite_of_finite (S : Set k) [Finite S] :
    FiniteDimensional k (adjoinPthRoots p S) := by
  -- The set of elements to adjoin to `k` is finite:
  have hFin : Finite ((frobenius (AlgebraicClosure k) p) ⁻¹'
      ((algebraMap k (AlgebraicClosure k)) '' S)) := by
    have hFin' : Finite ((algebraMap k (AlgebraicClosure k)) '' S) := by infer_instance
    exact Set.Finite.preimage (Set.injOn_of_injective (frobenius_inj _ _)) (hFin')
  apply IntermediateField.finiteDimensional_adjoin
  -- It remains to show that every element of the set
  -- `` ((frobenius (AlgebraicClosure k) p) ⁻¹' ((algebraMap k (AlgebraicClosure k)) '' S))``
  -- is integral over `k`.
  intro s hs
  apply IsIntegral.of_pow (n := p) (expChar_pos k p)
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

/-- If `y ∈ S`, then there is an element `x ∈ adjoin_pth_roots p S` with the property that
`y = x ^ p`. -/
lemma adjoinPthRoots_mem_frobenius_img {S : Set k} {y : k} (hy : y ∈ S) :
    algebraMap k (AlgebraicClosure k) y ∈ Subfield.map (frobenius (AlgebraicClosure k) p)
      (adjoinPthRoots p S).toSubfield := by
  use (frobeniusEquiv (AlgebraicClosure k) p).symm (algebraMap k _ y)
  refine ⟨?_, by simp⟩
  apply Subfield.mem_closure_of_mem
  right
  use y
  exact ⟨hy, by simp⟩

-- a relative version of `adjoin_pth_roots.frob_img_mem`, which allows for
-- `adjoin_pth_roots` to be embedded in the algebraic closure of a bigger field.
lemma adjoinPthRoots_mem_frobenius_img' (K : Type*) [Field K] [Algebra k K] {S : Set k} {y : K}
    (hy : y ∈ (algebraMap k K) '' S) :
    haveI : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
    algebraMap K (AlgebraicClosure K) y ∈ Subfield.map (frobenius (AlgebraicClosure K) p)
      ((adjoinPthRoots p S).map IsAlgClosed.lift).toSubfield := by
  haveI : ExpChar (AlgebraicClosure K) p := ExpChar.of_injective_algebraMap' k _
  unfold adjoinPthRoots
  rw [Subfield.mem_map]
  use (frobeniusEquiv (AlgebraicClosure K) p).symm (algebraMap K _ y)
  refine ⟨?_, by simp⟩
  simp only [toSubfield_map, Subfield.mem_map, RingHom.coe_coe]
  obtain ⟨z, hz⟩ := (Set.mem_image _ _ _).mp hy
  use (frobeniusEquiv (AlgebraicClosure k) p).symm (algebraMap k _ z)
  constructor
  · apply Subfield.mem_closure_of_mem
    simp only [Set.mem_union, Set.mem_range, Set.mem_preimage, frobenius_apply_frobeniusEquiv_symm,
      Set.mem_image, algebraMap.coe_inj, exists_eq_right]
    exact Or.inr hz.left
  · rw [← hz.2, ← RingHom.coe_coe, RingHom.map_frobeniusEquiv_symm, RingHom.coe_coe,
      AlgHom.commutes]
    rfl
