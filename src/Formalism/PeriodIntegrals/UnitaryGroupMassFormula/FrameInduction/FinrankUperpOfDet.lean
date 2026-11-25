module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

def Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun l i => gramVec k r z z' g i l

theorem det_ne (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : (gramM k r z z' γ).det ≠ 0 := by
  intro h0
  have h := Formalism.QuantumDeterminants.group_gram_holds k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  rw [h0, mul_zero] at h
  have : Gf k r z z' γ = 0 := by exact_mod_cast h
  linarith [hp.2]

end PI.FrameInd
