module

import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.NumberTheory.Primorial

@[expose] public section

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

lemma sum_primesLE_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  apply Formalism.MainNotions.WeilJacquetShalikaLaw.Proof.sz_mertens <;> assumption

end Formalism.LogFactorialBounds
