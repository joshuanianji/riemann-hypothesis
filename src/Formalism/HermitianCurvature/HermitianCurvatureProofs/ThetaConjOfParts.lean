module

public import Formalism.HermitianCurvature.StatementJF

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

def CptInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (C : Set (B.Mat k r)),
    B.CkOn ⊤ (B.GV k r) F → IsCompact C → (∀ g, g ∉ C → F g = 0) → ∀ (A : ℝ) (m : ℕ), B.InCC A m F

end Formalism.FourierDecayAlt.P.JFxG
