module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
public import Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.IndefR.Eqv.G5

variable {F : Type} [Field F] [NumberField F]

theorem adl_exists_place_ge_one (r : 𝓞 F) (hr : r ≠ 0) :
    ∃ w : InfinitePlace F, 1 ≤ w (r : F) := by
  classical
  by_contra! h
  have hnn : ∀ w : InfinitePlace F, 0 ≤ w (r : F) := fun w => by
    first | positivity
  have hN : (1 : ℝ) ≤ ((|Algebra.norm ℚ (r : F)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have hz : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.mpr hr
    have := Int.one_le_abs hz
    exact_mod_cast this
  rw [← InfinitePlace.prod_eq_abs_norm] at hN
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at hN
  have h1 : w0 (r : F) ^ w0.mult < 1 := pow_lt_one₀ (hnn w0) (h w0) InfinitePlace.mult_pos.ne'
  have h2 : ∏ w ∈ Finset.univ.erase w0, w (r : F) ^ w.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun w _ => pow_nonneg (hnn w) _) (fun w _ => pow_le_one₀ (hnn w) (h w).le)
  have h3 : 0 ≤ w0 (r : F) ^ w0.mult := pow_nonneg (hnn w0) _
  nlinarith

open scoped AdeleRing


theorem adl_inf_cocompact : ∃ C : Set (InfiniteAdeleRing F), IsCompact C ∧
    ∀ y, ∃ r : 𝓞 F, y - algebraMap F _ (r : F) ∈ C := by
  apply GlobalTheory.AdeleCocompact.exists_compact_infinite

theorem adl_cocompact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x, ∃ a : F, x - algebraMap F _ a ∈ K := by
  obtain ⟨C, hC, hCy⟩ := adl_inf_cocompact (F := F)
  refine ⟨C ×ˢ {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F},
    hC.prod (_root_.PI.IntAdCpctOpenWork.main F).2, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap F _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap F (InfiniteAdeleRing F) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r) =
        (x.2 - algebraMap F _ u) - algebraMap F _ (r : F) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

end Formalism.IndefR.Eqv.G5
