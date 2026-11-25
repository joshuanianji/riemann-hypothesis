module

public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

theorem k_le_x_pow_six {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : (D.R.k : ℝ) ≤ L.sc.x ^ (6 : ℝ) := by
  have hK := hS.2.2.1.2
  simp only [Formalism.MainNotions.szTh] at hK
  refine hK.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
  have h1 := L.sc.eps_lt
  have h2 := L.sc.eps_pos
  linarith

theorem ev_const (c α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, c ≤ Real.exp (x ^ α) := by
  filter_upwards [(tendsto_rpow_atTop hα).eventually_ge_atTop c] with x hx
  linarith [Real.add_one_le_exp (x ^ α)]

def rE (eps : ℝ) : ℕ := ⌈8 * (2 + 8 * eps + 2) / eps⌉₊ + 1

theorem rG_rE (s : Scale) : rG s = rE s.eps := rfl

end Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

end
