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
noncomputable section -- Remove this!
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

variable (A : Type) (a : A) [CommRing A]
variable (p : ℕ)

def I : Ideal A[X] := Ideal.span {X ^ p}
def AQuot : Type := A[X] ⧸ Ideal.span {X ^ p - C a}

def f : A[X] →+* A[X] ⧸ Ideal.span {X ^ p - C a} := Ideal.Quotient.mk _
def g : A →+* A[X] := C
def fg : A →+* A[X] ⧸ Ideal.span {X ^ p - C a} := (f _ _ _).comp (g _)

lemma inj (hp : p > 0) [Nontrivial A] : Function.Injective (fg A a p) := by
  unfold fg f g
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro y hy
  rw [RingHom.coe_comp, Function.comp_apply] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
  obtain ⟨P, hP⟩ := hy
  by_cases hPZero : P = 0
  · simp_all only [gt_iff_lt, zero_mul]
    symm at hP
    rw [Polynomial.C_eq_zero] at hP
    exact hP
  · have hMonic : (X ^ p - C a).Monic :=
      monic_X_pow_sub_C a <| Nat.ne_zero_iff_zero_lt.mpr hp
    have hXpC : (X ^ p - C a).natDegree = p := by
      simp only [natDegree_sub_C]
      rw [Polynomial.Monic.natDegree_pow Polynomial.monic_X]
      rw [Polynomial.natDegree_X]
      simp
    have hDeg : (P * (X ^ p - C a)).natDegree = P.natDegree + p := by
      rw [mul_comm, add_comm]
      nth_rewrite 2 [←hXpC]
      exact Polynomial.Monic.natDegree_mul' hMonic hPZero
    rw [hP, Polynomial.natDegree_C] at hDeg
    linarith

end Integral


open IntermediateField
open MvPolynomial

noncomputable section

section CommRing

variable {A : Type} [CommRing A]
variable (p : ℕ) [ExpChar A p]
-- variable (S : Set A)
variable {ι : Type} (x : ι → A)

--def adjoinPthRootsIdeal : Ideal (MvPolynomial S A) :=
--  Ideal.span <| Set.range (fun (s : S) => (X s) ^ p - C s.1)

def adjoinPthRootsIdeal : Ideal (MvPolynomial ι A) :=
  Ideal.span <| Set.range (fun i => (X i) ^ p - C (x i))

def adjoinPthRoots : Type :=
  MvPolynomial ι A ⧸ adjoinPthRootsIdeal p x
deriving CommRing, Algebra A, Algebra (MvPolynomial ι A), IsScalarTower A (MvPolynomial ι A)

example (i j : Type) (f : i → j) : MvPolynomial i A →ₐ[A] MvPolynomial j A :=
  MvPolynomial.rename f

omit [ExpChar A p] in
lemma adjoinPthRootsIdeal_map {κ : Type} {y : κ → A} (f : ι → κ) (h : y ∘ f = x) :
    (adjoinPthRootsIdeal p x).map (MvPolynomial.rename f) ≤ adjoinPthRootsIdeal p y := by
  unfold adjoinPthRootsIdeal
  rw [Ideal.map_span]
  rw [← h]
  simp only [Function.comp_apply]
  apply Ideal.span_mono
  intro t ht
  aesop

example {κ : Type} {y : κ → A} (f : ι → κ) (h : y ∘ f = x) :
    MvPolynomial ι A →ₐ[A] MvPolynomial κ A ⧸ adjoinPthRootsIdeal p y :=
  (Ideal.Quotient.mkₐ A (adjoinPthRootsIdeal p y)).comp <| MvPolynomial.rename f

def adjoinPthRoots_induced_map {κ : Type} {y : κ → A} (f : ι → κ) (h : y ∘ f = x) :
    adjoinPthRoots p x →ₐ[A] adjoinPthRoots p y :=
  Ideal.Quotient.liftₐ (adjoinPthRootsIdeal p x)
    ((Ideal.Quotient.mkₐ A (adjoinPthRootsIdeal p y)).comp <| MvPolynomial.rename f) sorry

omit [ExpChar A p] in
lemma algebraMap_eq_C_quot_mk (a : A) :
    (algebraMap A (adjoinPthRoots p x)) a = Ideal.Quotient.mk (adjoinPthRootsIdeal p x) (C a) := by
  rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq]
  exact IsScalarTower.algebraMap_apply A (MvPolynomial ι A) (adjoinPthRoots p x) a


lemma algebraMap_inj_fin [Fintype ι] (y : A) (b : ι → MvPolynomial ι A)
    (hy : ∑ i : ι, (b i) * ((X i) ^ p - C (x i)) = C y) :
    y = 0 := by
  -- can be proven by induction on the size of ι
  sorry

lemma algebraMap_inj : Function.Injective (algebraMap A (adjoinPthRoots p x)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext y
  constructor
  · intro hy
    simp_all only [RingHom.mem_ker, Submodule.mem_bot]
    rw [algebraMap_eq_C_quot_mk] at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hy
    unfold adjoinPthRootsIdeal at hy
    rw [Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hy
    obtain ⟨c, hc⟩ := hy
    let ιc := c.support
    let Compl := {i : ι // i ∉ ιc}
    let I : Ideal (MvPolynomial ι A) := Ideal.span <| Set.range (fun i : Compl ↦ X i)
    let B := (MvPolynomial ι A) ⧸ I
    let f : MvPolynomial ι A →+* B := Ideal.Quotient.mk I
    let g : B →+* MvPolynomial ιc A := sorry
    let gf := g.comp f
    have hgf : gf (c.sum fun i a => a * (X i ^ p - C (x i))) = gf (C y) := by
      rw [hc]
    have h_gf_X : ∀ i : ιc, X i = gf (X i.val : MvPolynomial ι A) := by
      sorry
    have h_gf_C : ∀ a : A, (C a : MvPolynomial ιc A) = gf (C a : MvPolynomial ι A) := by
      sorry
    rw [map_finsuppSum] at hgf
    simp only [map_mul, map_sub, map_pow] at hgf
    simp_rw [← h_gf_C] at hgf
    have hIncl : ιc ⊆ c.support := by exact Finset.Subset.rfl
    rw [Finsupp.sum_of_support_subset c hIncl
        (fun a b => gf b * (gf (X a) ^ p - C (x a))) ?_] at hgf
    · -- rw [← h_gf_X] at hgf
      sorry
    · intro i hi
      simp
  · aesop

example (B : Type) [CommRing B] (f : A →+ B) (x : ι →₀ A) (h : ι → A → A)
    : f (x.sum h) = x.sum (fun i a ↦ f (h i a)) := by
  exact map_finsuppSum f x h

example (X Y : Type) (f : X → Y) (hf : f.Injective) [Nontrivial X] : Nontrivial Y := by
  exact Function.Injective.nontrivial hf

instance adjoinPthRoots_nontrivial [Nontrivial A] : Nontrivial (adjoinPthRoots p x) :=
  Function.Injective.nontrivial <| algebraMap_inj p x

instance adjoinPthRootsExpChar : ExpChar (adjoinPthRoots p x) p :=
  expChar_of_injective_ringHom (algebraMap_inj p x) p

omit [ExpChar A p] in
lemma adjoinPthRootsIdeal_mem (s : ι) : (X s) ^ p - C (x s) ∈ adjoinPthRootsIdeal p x :=
  Ideal.mem_span_range_self

lemma X_pow_p_mem (s : ι) :
    frobenius (adjoinPthRoots p x) p (Ideal.Quotient.mk  _ (X s)) ∈ (algebraMap A _).range := by
  rw [RingHom.mem_range]
  use x s
  rw [frobenius_def, algebraMap_eq_C_quot_mk]
  apply Eq.symm
  erw [Ideal.Quotient.eq]
  dsimp only
  exact adjoinPthRootsIdeal_mem p x s

lemma p_power_mem (z : adjoinPthRoots p x) :
    frobenius (adjoinPthRoots p x) p z ∈ (algebraMap A _).range := by
  let ⟨y, hy⟩ := Quot.exists_rep z
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
    exact Subring.pow_mem _ (X_pow_p_mem _ _ _) _

lemma units_complement_maximal (R : Type) [CommRing R] (I : Ideal R) (h1 : 1 ∉ I)
    (h : ∀ x : R, x ∉ I → IsUnit x) : I.IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨h1, ?_⟩
  intro J x hIJ hxI hxJ
  rw [← mul_one x] at hxJ
  exact (Ideal.unit_mul_mem_iff_mem J (h x hxI)).mp hxJ

lemma one_not_mem_nilradical (R : Type) [CommSemiring R] [Nontrivial R] : 1 ∉ nilradical R := by
  rw [mem_nilradical]
  exact not_isNilpotent_one

-- TODO: use [Finite ι] or [Fintype ι]?
instance adjoinPthRoots_finiteType [Fintype ι] : Algebra.FiniteType A (adjoinPthRoots p x) := by
  unfold adjoinPthRoots
  infer_instance

instance adjoinPthRoots_Integral : Algebra.IsIntegral A (adjoinPthRoots p x) :=
  IsIntegral_of_p_power_mem A (adjoinPthRoots p x) (p_power_mem p x)

-- Do we even need this? Or will it be automatically inferred?
lemma adjoinPthRoots_finite_of_finite [Fintype ι] : Module.Finite A (adjoinPthRoots p x) :=
  Algebra.IsIntegral.finite

def adjoinPthRootsReduced : Type :=
  adjoinPthRoots p x ⧸ nilradical (adjoinPthRoots p x)
deriving Algebra A, Algebra (adjoinPthRoots p x), CommRing, IsScalarTower A (adjoinPthRoots p x)

/-def adjoinPthRootsReduced_induced_map (T : Set A) (hST : S ⊆ T) :
    adjoinPthRoots p S →ₐ[A] adjoinPthRoots p T := sorry-/

lemma adjoinPthRootsReduced_algebraMap_injective [IsReduced A] :
    Function.Injective (algebraMap A (adjoinPthRootsReduced p x)) := by
  sorry

omit [ExpChar A p] in
lemma adjoinPthRoots_adjoinPthRootsReduced_algebraMap_surjective :
    Function.Surjective (algebraMap (adjoinPthRoots p x) (adjoinPthRootsReduced p x)) := by
  unfold adjoinPthRootsReduced
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

instance adjoinPthRootsReducedExpChar [IsReduced A] :
    ExpChar (adjoinPthRootsReduced p x) p :=
  expChar_of_injective_ringHom (adjoinPthRootsReduced_algebraMap_injective p x) p

-- I think this actually doesn't need the assumption that A is reduced, but we now have it so that
-- we get the ExpChar p instance on adjoinPthRootsReduced p S.
lemma p_pow_mem_reduced [IsReduced A] (t : adjoinPthRootsReduced p x) :
    frobenius (adjoinPthRootsReduced p x) p t ∈ (algebraMap A _).range := by
  obtain ⟨y, hy⟩ := Set.mem_range.mp
      ((adjoinPthRoots_adjoinPthRootsReduced_algebraMap_surjective p x) t)
  obtain ⟨z, hz⟩ := p_power_mem p x y
  use z
  rw [IsScalarTower.algebraMap_eq A (adjoinPthRoots p x) (adjoinPthRootsReduced p x)]
  rw [RingHom.coe_comp, Function.comp_apply, hz, ← hy, RingHom.map_frobenius]

end CommRing

section Field

variable {k : Type} [Field k]
variable (p : ℕ) [ExpChar k p]
variable {ι : Type} (x : ι → k)

instance adjoinPthRoots_of_field_nilradical_maximal [ExpChar k p] :
    (nilradical (adjoinPthRoots p x)).IsMaximal := by
  apply units_complement_maximal
  · exact one_not_mem_nilradical _
  · intro t ht
    -- use that x ^ p is a nonzero element of A. Since A is a field, x ^ p is a unit
    rw [← isUnit_pow_iff (expChar_ne_zero k p)]
    have hNonZero : t ^ p ≠ 0 := by
      rw [not_iff_not.mpr mem_nilradical] at ht
      tauto
    obtain ⟨y, hy⟩ := p_power_mem p x t
    rw [frobenius_def] at hy
    have hyz : y ≠ 0 := by
      intro h
      apply hNonZero
      rw [← hy, h]
      exact map_zero _
    rw [← hy]
    exact (isUnit_iff_ne_zero.mpr hyz).map (algebraMap _ _)

instance adjointPthRootsReducedField :
    Field (adjoinPthRootsReduced p x) := by
  unfold adjoinPthRootsReduced
  apply Ideal.Quotient.field

instance adjoinPthRoots_purelyInseparable : IsPurelyInseparable k (adjoinPthRootsReduced p x) := by
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro t
  use 1
  rw [pow_one, ← frobenius_def]
  exact p_pow_mem_reduced p x t

end Field
