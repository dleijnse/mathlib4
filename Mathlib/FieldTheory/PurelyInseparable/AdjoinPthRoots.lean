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
variable {ι : Type} (x : ι → A)

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

omit [ExpChar A p] in
lemma adjoinPthRootsIdeal_map' {κ : Type} {y : κ → A} {f : ι → κ} (h : y ∘ f = x) :
    ∀ a ∈ adjoinPthRootsIdeal p x,
      ((Ideal.Quotient.mkₐ A (adjoinPthRootsIdeal p y)).comp (rename f)) a = 0 := by
  intro a ha
  rw [AlgHom.comp_apply, ← RingHom.mem_ker, AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker]
  exact adjoinPthRootsIdeal_map p x f h <| Ideal.mem_map_of_mem (rename f) ha

example {κ : Type} {y : κ → A} (f : ι → κ) :
    MvPolynomial ι A →ₐ[A] MvPolynomial κ A ⧸ adjoinPthRootsIdeal p y :=
  (Ideal.Quotient.mkₐ A (adjoinPthRootsIdeal p y)).comp <| MvPolynomial.rename f

def adjoinPthRoots_induced_map {κ : Type} {y : κ → A} (f : ι → κ) (h : y ∘ f = x) :
    adjoinPthRoots p x →ₐ[A] adjoinPthRoots p y :=
  Ideal.Quotient.liftₐ (adjoinPthRootsIdeal p x)
    ((Ideal.Quotient.mkₐ A (adjoinPthRootsIdeal p y)).comp <| MvPolynomial.rename f)
      (adjoinPthRootsIdeal_map' p x h)

omit [ExpChar A p] in
lemma algebraMap_eq_C_quot_mk (a : A) :
    (algebraMap A (adjoinPthRoots p x)) a = Ideal.Quotient.mk (adjoinPthRootsIdeal p x) (C a) := by
  rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq]
  exact IsScalarTower.algebraMap_apply A (MvPolynomial ι A) (adjoinPthRoots p x) a

lemma algebraMap_inj_fin' [Fintype ι] : Function.Injective (algebraMap A (adjoinPthRoots p x)) := by
  induction hcard : Fintype.card ι generalizing ι
  · unfold adjoinPthRoots
    have hBot : (adjoinPthRootsIdeal p x : Ideal _) = ⊥ := by
      unfold adjoinPthRootsIdeal
      rw [← Ideal.span_empty]
      congr
      have hι : IsEmpty ι := by
        exact Fintype.card_eq_zero_iff.mp hcard
      apply Set.range_eq_empty
    let i1 : A →+* MvPolynomial ι A := algebraMap _ _
    let i2 : MvPolynomial ι A →+* MvPolynomial ι A ⧸ (adjoinPthRootsIdeal p x) := algebraMap _ _
    have hComp : i2.comp i1 = algebraMap A (MvPolynomial ι A ⧸ (adjoinPthRootsIdeal p x)) := by
      rfl
    rw [← hComp]
    unfold i1 i2
    rw [RingHom.coe_comp]
    apply Function.Injective.comp
    · rw [Ideal.Quotient.algebraMap_eq]
      apply Function.Bijective.injective
      rw [Ideal.Quotient.mk_bijective_iff_eq_bot]
      exact hBot
    · rw [algebraMap_eq]
      exact C_injective ι A
  · expose_names

    -- Idea: reduce to inj on line 62 of this file.
    sorry


variable {κ : Type} (y : κ → A)

def adjoinPthRoots_sum_right_x : ι ⊕ κ → adjoinPthRoots p x :=
  Sum.elim (algebraMap A (adjoinPthRoots p x) ∘ x) (algebraMap A (adjoinPthRoots p x) ∘ y)

example : ι → ι ⊕ κ := Sum.inl

example : MvPolynomial (ι ⊕ κ) A ≃+* MvPolynomial ι (MvPolynomial κ A) := sumRingEquiv A ι κ


example (f : ι → κ) : MvPolynomial ι A →ₐ[A] MvPolynomial κ A := by exact rename f
example : MvPolynomial ι A →ₐ[A] MvPolynomial (ι ⊕ κ) A := rename Sum.inl

lemma adjoinPthRoots_ideal_sum : adjoinPthRootsIdeal p (Sum.elim x y) =
    Ideal.map (rename Sum.inl) (adjoinPthRootsIdeal p x) ⊔
      Ideal.map (rename Sum.inr) (adjoinPthRootsIdeal p y) := by
  unfold adjoinPthRootsIdeal
  repeat rw [Ideal.map_span]

  sorry

example (B : Type) [CommRing B] (f : A →+* B) : MvPolynomial ι A →+* MvPolynomial ι B :=
  MvPolynomial.map f


example (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    MvPolynomial κ A →+* MvPolynomial κ ((MvPolynomial ι A) ⧸ I) := by
  #check J.map (MvPolynomial.map (algebraMap A ((MvPolynomial ι A) ⧸ I)))
  exact MvPolynomial.map ((Ideal.Quotient.mk I).comp (algebraMap A (MvPolynomial ι A)))

/-
def equiv1 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    (MvPolynomial (ι ⊕ κ) A) ⧸ (I.map (rename Sum.inl) ⊔ J.map (rename Sum.inr)) ≃+*
    ((MvPolynomial (ι ⊕ κ) A) ⧸ (I.map (rename Sum.inl))) ⧸
    ((J.map (rename Sum.inr)).map (Ideal.Quotient.mk (I.map (rename Sum.inl)))) := by
  #check (I.map (rename Sum.inl)).map (sumRingEquiv A ι κ).toRingHom
  #check (Ideal.Quotient.mk ((I.map (rename Sum.inl)).map (sumRingEquiv A ι κ).toRingHom))
  #check ((J.map (rename Sum.inr)).map (sumRingEquiv A ι κ).toRingHom).map (Ideal.Quotient.mk ((I.map (rename Sum.inl)).map (sumRingEquiv A ι κ).toRingHom))
  exact (DoubleQuot.quotQuotEquivQuotSup _ _).symm-/

def equiv1 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    (MvPolynomial (κ ⊕ ι) A ⧸ I.map (rename Sum.inr) ⊔ J.map (rename Sum.inl)) ≃ₐ[A]
    (MvPolynomial κ (MvPolynomial ι A)) ⧸
       ((I.map (rename Sum.inr) ⊔ J.map (rename Sum.inl)).map (sumAlgEquiv A κ ι).toAlgHom) :=
  Ideal.quotientEquivAlg _ _ (sumAlgEquiv A κ ι) rfl

def equiv2 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    (MvPolynomial κ (MvPolynomial ι A) ⧸ Ideal.map (sumAlgEquiv A κ ι)
      (Ideal.map (rename Sum.inr) I ⊔ Ideal.map (rename Sum.inl) J)) ≃ₐ[A]
    (MvPolynomial κ (MvPolynomial ι A)) ⧸
      ((I.map (rename Sum.inr)).map (sumAlgEquiv A κ ι).toAlgHom) ⊔
        (J.map (rename Sum.inl)).map (sumAlgEquiv A κ ι).toAlgHom :=
  Ideal.quotientEquivAlg _ _ AlgEquiv.refl (by
    simp [AlgEquiv.refl_toRingHom, Ideal.map_id, Ideal.map_sup]; rfl)

def equiv3 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    (MvPolynomial κ (MvPolynomial ι A) ⧸
    Ideal.map (sumRingEquiv A κ ι).toRingHom (Ideal.map (rename Sum.inr) I) ⊔
      Ideal.map (sumRingEquiv A κ ι).toRingHom (Ideal.map (rename Sum.inl) J)) ≃ₐ[A]
    ((MvPolynomial κ (MvPolynomial ι A)) ⧸
      ((I.map (rename Sum.inr)).map (sumAlgEquiv A κ ι).toAlgHom)) ⧸
        ((J.map (rename Sum.inl)).map (sumAlgEquiv A κ ι).toAlgHom).map (Ideal.Quotient.mk _) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ A _ _).symm

lemma ideal_equality (I : Ideal (MvPolynomial ι A)) :
    ((I.map (rename Sum.inr)).map (sumAlgEquiv A κ ι).toAlgHom) = I.map C := by
  rw [Ideal.map_mapₐ, MvPolynomial.sumAlgEquiv_comp_rename_inr]
  rfl

def equiv4' (I : Ideal (MvPolynomial ι A)) :
    (MvPolynomial κ (MvPolynomial ι A) ⧸
      Ideal.map ((sumAlgEquiv A κ ι)) (Ideal.map (rename Sum.inr) I)) ≃ₐ[A]
    ((MvPolynomial κ (MvPolynomial ι A)) ⧸ (I.map C)) :=
  Ideal.quotientEquivAlg _ _ AlgEquiv.refl (by rw [← ideal_equality I]; simp; rfl )

lemma commutes_equiv4'_quotient (I : Ideal (MvPolynomial ι A))
    (x : MvPolynomial κ (MvPolynomial ι A)) :
    (Ideal.Quotient.mk (I.map C)) x = (equiv4' I).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.map ((sumAlgEquiv A κ ι)) (Ideal.map (rename Sum.inr) I))) x := by
  rw [RingHom.comp_apply]
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe]
  unfold equiv4'
  rw [Ideal.quotientEquivAlg_mk]
  simp

lemma commutes_equiv4'_quotient' (I : Ideal (MvPolynomial ι A)) :
    (Ideal.Quotient.mk (I.map C)) = (equiv4' I).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.map ((sumAlgEquiv A κ ι)) (Ideal.map (rename Sum.inr) I))) := by
  ext x <;> exact commutes_equiv4'_quotient I _

def equiv4 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    ((MvPolynomial κ (MvPolynomial ι A) ⧸
      Ideal.map ((sumAlgEquiv A κ ι)) (Ideal.map (rename Sum.inr) I)) ⧸
        Ideal.map (Ideal.Quotient.mk _)
          (Ideal.map ((sumAlgEquiv A κ ι)) (Ideal.map (rename Sum.inl) J))) ≃ₐ[A]
    (((MvPolynomial κ (MvPolynomial ι A)) ⧸ (I.map C)) ⧸
    Ideal.map (Ideal.Quotient.mk _)
      (Ideal.map ((sumAlgEquiv A κ ι)) (Ideal.map (rename Sum.inl) J))) :=
  Ideal.quotientEquivAlg _ _ (equiv4' I) (by simp [commutes_equiv4'_quotient', Ideal.map_map])

def equiv5' (I : Ideal (MvPolynomial ι A)) :
    ((MvPolynomial κ (MvPolynomial ι A)) ⧸ (I.map C)) ≃ₐ[A]
      (MvPolynomial κ (MvPolynomial ι A ⧸ I)) :=
  ((MvPolynomial.quotientEquivQuotientMvPolynomial _).restrictScalars A).symm

lemma Ideal.map_of_equivₐ {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] {I : Ideal A}
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) :
    map f.symm (map f I) = I := by
  sorry

lemma quotientEquivQuotientMvPolynomial_comp_C {R : Type} [CommRing R] (I : Ideal R) {σ : Type} :
    ((quotientEquivQuotientMvPolynomial I).toRingHom.comp C).comp
      (Ideal.Quotient.mk I : R →+*  R ⧸ I) =
    (Ideal.Quotient.mk (Ideal.map C I)).comp (C : R →+* MvPolynomial σ R) := by
  ext x
  unfold quotientEquivQuotientMvPolynomial
  simp

lemma quotientEquivQuotientMvPolynomial_comp_C' {R : Type} [CommRing R] (I : Ideal R) (σ : Type) :
    C.comp (Ideal.Quotient.mk I : R →+*  R ⧸ I) =
    (quotientEquivQuotientMvPolynomial I).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Ideal.map C I)).comp (C : R →+* MvPolynomial σ R)) := by
  ext x
  unfold quotientEquivQuotientMvPolynomial
  simp

lemma map_equality' (I : Ideal (MvPolynomial ι A)) (x : MvPolynomial κ A) :
    (MvPolynomial.map ((Ideal.Quotient.mk I).comp C)) x =
    ((((AlgEquiv.restrictScalars A
        (@quotientEquivQuotientMvPolynomial _ κ _ I)).symm).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.map C I))).comp
      (MvPolynomial.map C)) x := by

  -- rw [quotientEquivQuotientMvPolynomial_comp_C']
  -- unfold quotientEquivQuotientMvPolynomial
  sorry

lemma map_equality (I : Ideal (MvPolynomial ι A)) :
    (MvPolynomial.map ((Ideal.Quotient.mk I).comp C)) =
    ((((AlgEquiv.restrictScalars A
        (@quotientEquivQuotientMvPolynomial _ κ _ I)).symm).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.map C I))).comp
      (MvPolynomial.map C))
    := by
  -- rw [quotientEquivQuotientMvPolynomial_comp_C']
  sorry

def equiv5 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    (((MvPolynomial κ (MvPolynomial ι A)) ⧸ (I.map C)) ⧸
    Ideal.map (Ideal.Quotient.mk _)
      (Ideal.map ((sumAlgEquiv A κ ι).toAlgHom) (Ideal.map (rename Sum.inl) J))) ≃ₐ[A]
    (MvPolynomial κ (MvPolynomial ι A ⧸ I)) ⧸
      (J.map (MvPolynomial.map ((Ideal.Quotient.mk I).comp C))) :=
  Ideal.quotientEquivAlg _ _ (equiv5' I) (by
    rw [Ideal.map_mapₐ]
    rw [MvPolynomial.sumAlgEquiv_comp_rename_inl]
    rw [Ideal.map_map]
    rw [AlgHom.coe_ideal_map]
    rw [Ideal.map_map]
    simp only [mapAlgHom_coe_ringHom, Algebra.toRingHom_ofId, algebraMap_eq]
    rw [map_equality]
    rfl)

/-
def equiv2 (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    ((MvPolynomial (ι ⊕ κ) A) ⧸ (I.map (rename Sum.inl))) ⧸
    ((J.map (rename Sum.inr)).map (Ideal.Quotient.mk (I.map (rename Sum.inl)))) ≃+*
    ((MvPolynomial ι (MvPolynomial κ A)) ⧸ (I.map (rename Sum.inl)).map (sumRingEquiv A ι κ).toRingHom) ⧸
    ((J.map (rename Sum.inr)).map (sumRingEquiv A ι κ).toRingHom).map (Ideal.Quotient.mk ((I.map (rename Sum.inl)).map (sumRingEquiv A ι κ).toRingHom))
    := -- Ideal.quotientEquiv
    sorry-/

def sum_quotient_equiv (I : Ideal (MvPolynomial ι A)) (J : Ideal (MvPolynomial κ A)) :
    (MvPolynomial (ι ⊕ κ) A) ⧸ (I.map (rename Sum.inl) ⊔ J.map (rename Sum.inr)) ≃+*
    (MvPolynomial κ ((MvPolynomial ι A) ⧸ I)) ⧸
      (J.map (MvPolynomial.map ((Ideal.Quotient.mk I).comp C))) := by

  sorry

def adjoinPthRoots_of_adjoinPthRoots_equiv :
    adjoinPthRoots p (Sum.elim x y) ≃+*
      adjoinPthRoots p (adjoinPthRoots_sum_right_x p x y) := by
  unfold adjoinPthRoots
  unfold adjoinPthRoots_sum_right_x

  -- use the following:
  -- MvPolynomial.quotientEquivQuotientMvPolynomial
  -- MvPolynomial.sumAlgEquiv
  -- third isomorphism theorem: DoubleQuot.quotQuotEquivQuotSup


  sorry

open Classical in
lemma algebraMap_inj_fin'' (s : Finset ι) (x : s → A) :
    Function.Injective (algebraMap A (adjoinPthRoots p x)) := by
  induction hcard : Finset.card s generalizing s
  · sorry
  · expose_names
    rw [Finset.card_eq_succ] at hcard
    obtain ⟨a, t, hat, hins, htcard⟩ := hcard
    have hIncl : t ⊆ s := by
      rw [← hins]
      exact (Finset.subset_insert a t)
    let incl : t → s := fun a ↦ Subtype.map (fun a ↦ a) hIncl a
    let x' : t → A := fun i => (@Set.restrict₂ ι (fun _ ↦ A) t s hIncl x i)
    have hInj := h t x' htcard
    have hComp1 : x ∘ incl = x' := rfl
    let g : adjoinPthRoots p x' →+* adjoinPthRoots p x :=
        adjoinPthRoots_induced_map p x' incl hComp1
    have ha : a ∈ s := by
      rw [← hins]
      exact Finset.mem_insert_self a t
    let x0 : ({⟨a, ha⟩} : Set s) → adjoinPthRoots p x' :=
        fun a => (algebraMap A (adjoinPthRoots p x') (x a))
    let e : adjoinPthRoots p x ≃+* adjoinPthRoots p x0 := sorry -- could be difficult
    have hComp2 : (algebraMap A (adjoinPthRoots p x)) =
        g.comp (algebraMap A (adjoinPthRoots p x')) := by
      sorry
    -- have hComp3 : e.comp g = algebraMap (adjoinPthRoots p x')
    rw [hComp2, RingHom.coe_comp]
    apply Function.Injective.comp
    ·
      sorry
    · exact hInj

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
