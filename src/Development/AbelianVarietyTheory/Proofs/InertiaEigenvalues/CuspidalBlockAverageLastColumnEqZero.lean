module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CuspGeneric

theorem posM_apply_of_blkIx {R : Type} [CommRing R] {a r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM Subtype.val x i j = if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  classical
  simp only [posM, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro t _ ht
      rw [Matrix.single_apply, ite_eq_right]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, ite_eq_right]
    rintro ⟨h1, h2⟩
    have := t.2
    rw [h1, h2] at this
    exact h this

end GlobalTheory.CuspGeneric
