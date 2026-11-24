module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdMulRight
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.VacuumImageIntertwiner

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThK.SplitDict

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThKG.StdDict
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
  {ψ : AddChar (AF F) ℂ}

theorem exists_cond (hψ : IsStd ψ) (v : Pl F) : ∃ δ : (Fv F v)ˣ, ∀ x : Fv F v,
    (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔ δ.1 * x ∈ v.adicCompletionIntegers F := by
  have e : ∀ (α : Af F) (x : Fv F v), α * singleFin v x = singleFin v (x * α v) := fun α x => by
    apply af_ext
    intro u
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]
      rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  have s1 : ∀ x : Fv F v, singleFin v x v = x := fun x => evalV_singleFin_self v x
  have s0 : ∀ (x : Fv F v) u, u ≠ v → singleFin v x u = 0 := fun x u hu => evalV_singleFin_ne hu x
  have h1 : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      x ∈ GlobalTheory.Idele.localIdeal v (GlobalTheory.StdDual.codiff F) := fun x => by
    have := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) (singleFin v x)
    refine ⟨fun H => ?_, fun H y hy => ?_⟩
    · have h2 := this.2 (fun α hα => by rw [e]; exact H _ (hα v)) v
      rwa [s1] at h2
    · have h2 := this.1 (fun u => by
        by_cases hu : u = v
        · subst hu; rw [s1]; exact H
        · rw [s0 x u hu]; exact zero_mem _) (singleFin v y) (fun u => by
        by_cases hu : u = v
        · subst hu; rw [s1]; exact hy
        · rw [s0 y u hu]; exact zero_mem _)
      rwa [e, s1] at h2
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hx : Valued.v (algebraMap F (Fv F v) (π ^ FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F))) =
      WithZero.exp (-FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F)) := by
    rw [GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  have hne : algebraMap F (Fv F v) (π ^ FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F)) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  refine ⟨(Units.mk0 _ hne)⁻¹, fun x => ?_⟩
  rw [h1, GlobalTheory.Idele.mem_localIdeal_iff GlobalTheory.StdDual.codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀, hx, inv_mul_le_one₀ WithZero.exp_pos]

variable {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)}

theorem split_place_dictionary : Dict := by
  intro F E _ _ _ _ _ σ B a a' G X om om' T v τ
  have hB := T.base
  obtain ⟨b, b₀, b', c, δ, hb, hb₀, hc, hδ, hb', hP⟩ : ∃ (b : GL (Fin a) (Fv F v)) (b₀ b' : GL (Fin a') (Fv F v))
      (c : GL (Fin (a + a')) (Fv F v)) (δ : Fv F v), IsSplitBasis τ G.V.L b ∧ IsSplitBasis τ G.V'.L b₀ ∧ IsSplitBasis τ G.W.L c ∧
      (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (x * y) = 1) ↔ δ * x ∈ v.adicCompletionIntegers F) ∧
      b'.1 = δ • b₀.1 ∧ ∀ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩ → b = G.V.bas v ∧ b' = G.V'.bas v ∧ c = G.W.bas v := by
    by_cases H : ∃ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩
    · obtain ⟨hv, rfl⟩ := H
      exact ⟨_, _, _, _, 1, T.geo.hV.bas ⟨v, hv⟩, T.geo.hV'.bas ⟨v, hv⟩, T.geo.hW.bas ⟨v, hv⟩,
        fun x => by rw [one_mul]; exact hB.psiP v hv x, (one_smul _ _).symm, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
    · have := T.geo.hV.lat
      have := T.geo.hV'.lat
      have := T.geo.hW.lat
      obtain ⟨b, hb⟩ := exists_isSplitBasis τ G.V.L hB.cm
      obtain ⟨b₀, hb₀⟩ := exists_isSplitBasis τ G.V'.L hB.cm
      obtain ⟨c, hc⟩ := exists_isSplitBasis τ G.W.L hB.cm
      obtain ⟨δ, hδ⟩ := exists_cond hB.std v
      exact ⟨b, b₀, δ • b₀, c, δ, hb, hb₀, hc, hδ, rfl, fun hv e => absurd ⟨hv, e⟩ H⟩
  obtain ⟨ι, l1, v1, g1, h1⟩ := model_alt hB T.geo.hV T.geo.hW (T.geo.hM.vac v) T.weil hb hc (ν := chrW X.ν τ) (β := chrW X.β τ)
    (MonoidHom.ext fun x => by
      rw [chrW_div, chrW_conj hB.cm τ T.chars.resα, chrW_conj hB.cm τ T.chars.resβ, Chars.ν, chrW_div, inv_div_inv])
    (chrW_conj hB.cm τ T.chars.resβ)
  obtain ⟨ι', l2, v2, g2, h2⟩ := model_Bar hB T.geo.hV' T.geo.hW (T.geo.hM'.vac v) T.weil' hb₀ hc hδ hb'
  refine ⟨b, b', c, ι, ι', inB τ b, inB τ b', inB τ c, l1, l2, hP, v1, v2, g1, h1, g2, h2, fun x => ?_⟩
  obtain ⟨-, -, k, -⟩ := dictX F E σ _ _ B _ _ G.M om _ _ hB ⟨_, _, T.geo.hV⟩ ⟨_, _, T.geo.hW⟩ T.weil v τ
  obtain ⟨h, hh, e⟩ := k (c * x * c⁻¹)
  refine ⟨h, hh, ?_⟩
  rw [inB, show GeneralLinearGroup.map (piW τ) h.1 = c * x * c⁻¹ from Units.ext e]
  group

end PositivityTheory.ThK.SplitDict
