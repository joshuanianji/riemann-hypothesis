module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TorsionGenerators

variable {R : Type} [CommRing R]

theorem exists_fibre (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [CommRing k] (t : R →+* k) :
    ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left)
      (β : (𝟙_ (Over (Sp k)) ⟶ P'.A) ≃* (Over.mk (spMap t) ⟶ P.A)), IsPolFibre t P P' φ ∧
      (∀ x, (β x).left = x.left ≫ φ) ∧ ∀ (n : ℤ) x y (c : Γ(Sp k, ⊤)ˣ),
        Out.WeilIs P'.A P'.L n x y c → Out.WeilIs P.A P.L n (β x) (β y) c := by
  obtain ⟨P', φ, h⟩ := exists_isPolFibre hL.polBaseChange t P
  obtain ⟨β, hβ⟩ := UnifPoint.exists_pointEquiv h.2.1
  refine ⟨P', φ, β, h, hβ, fun n x y c H => ?_⟩
  have H' := (weilIs_grpPullback_of_comm _ _ P.A P'.A _ φ P.L P'.L P.isLB P'.isLB h.2.1 (LBIso.symm h.2.2) _ n x y
    (pushPt h.2.1.1.w x) (pushPt h.2.1.1.w y) c rfl rfl).1 H
  exact UnifPoint.weilIs_congr (Category.id_comp _) (hβ x).symm (hβ y).symm H'

theorem exists_weilIs (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [Field k]
    (t : R →+* k) {n : ℕ} {x y : Over.mk (spMap t) ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ u : kˣ, Out.WeilIs P.A P.L n x y (unitOn u) := by
  obtain ⟨P', φ, β, h, -, H⟩ := exists_fibre hL P t
  obtain ⟨x, rfl⟩ := β.surjective x
  obtain ⟨y, rfl⟩ := β.surjective y
  rw [← map_pow, MulEquiv.map_eq_one_iff] at hx hy
  obtain ⟨c, hc, -⟩ := (hL.weil _ P' n _).1 x y hx hy
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c, ?_⟩
  have e : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c) = c :=
    Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c.val)
  rw [e]
  exact H n x y c hc

alias unitOn_injective := _root_.GlobalTheory.unitOn_injective_of_commRing

section Ext

variable {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

end Ext

section System

variable {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (a : OAct O P.A) (tr : O → ℤ)

variable {P a tr} {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

end System

end GlobalTheory.TorsionGenerators

namespace GlobalTheory

end GlobalTheory
