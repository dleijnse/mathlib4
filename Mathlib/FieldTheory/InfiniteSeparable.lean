/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/

import Mathlib

def separablyGeneratedBy (k K : Type) [Field k] [Field K] [Algebra k K] (X : Set K) :=
  IsTranscendenceBasis k (fun x => x.val : X → K)
    ∧ Algebra.IsSeparable (IntermediateField.adjoin k X) K

lemma Separable_imp_separablyGeneratedByEmpty (k K : Type) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] : separablyGeneratedBy k K ∅ := by
  constructor
  ·
    sorry
  · sorry
