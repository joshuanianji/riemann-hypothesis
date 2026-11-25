module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

universe u

section Square

variable {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B}

theorem isPullback_resLE (sq : IsPullback g q' q b) (V : B.Opens) (V' : B'.Opens)
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPullback (g.resLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.resLE V' (q' ⁻¹ᵁ V') le_rfl)
      (q.resLE V (q ⁻¹ᵁ V) le_rfl) (b.resLE V V' hle) := by
  have outer : IsPullback ((q' ⁻¹ᵁ V').ι ≫ g) (q' ∣_ V') q (V'.ι ≫ b) :=
    (isPullback_morphismRestrict q' V').flip.paste_horiz sq
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict]
  refine IsPullback.of_right (h₁₂ := (q ⁻¹ᵁ V).ι) (h₂₂ := V.ι) (v₁₃ := q) ?_ ?_
    (isPullback_morphismRestrict q V).flip
  · rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact outer
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, sq.w, ← Category.assoc,
      ← morphismRestrict_ι, Category.assoc]

theorem isPushout_appLE (sq : IsPullback g q' q b) (hq : IsAffineHom q) {V : B.Opens}
    (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPushout (q.app V) (b.appLE V V' hle) (g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.app V') := by
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have : IsAffine (q ⁻¹ᵁ V).toScheme := hV.preimage q
  have P := isPushout_appTop_of_isPullback (isPullback_resLE sq V V' hle hleG)
  rw [← Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appLE_eq_app]
  refine P.of_iso V.topIso (q ⁻¹ᵁ V).topIso V'.topIso (q' ⁻¹ᵁ V').topIso ?_ ?_ ?_ ?_ <;>
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

end Square

section Algebra

variable {R A R' A' : CommRingCat.{u}} {qa : R ⟶ A} {ba : R ⟶ R'} {ga : A ⟶ A'} {qa' : R' ⟶ A'}
  {X : Type u} [AddCommMonoid X]

end Algebra

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
