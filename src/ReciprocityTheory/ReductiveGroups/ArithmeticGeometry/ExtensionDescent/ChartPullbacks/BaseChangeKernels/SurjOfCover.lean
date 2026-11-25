module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Lemma

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

namespace GluingInclusion

variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))

abbrev cm (V : B.Opens) (h : V ≤ W) : AddMonoidAlgebra Γ(B, V) X →+* Γ(G, q ⁻¹ᵁ V) :=
  AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)

lemma res_res {Y : Scheme.{0}} {U₁ U₂ U₃ : Y.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (s : Γ(Y, U₃)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom s) =
      (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  have h2 := congrArg (fun f => f.hom s) (Y.presheaf.map_comp (homOfLE h₂).op (homOfLE h₁).op)
  first
  | exact h2.symm

variable (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (x : Multiplicative X),
    φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))

include hnat in
lemma cm_nat {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom.comp (cm q φ V₂ h₂) =
      (cm q φ V₁ h₁).comp (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp
  · intro x
    simp [hnat V₁ V₂ h₁ h₂ h]

include hnat in
lemma cm_nat_apply {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (p : AddMonoidAlgebra Γ(B, V₂) X) :
    cm q φ V₁ h₁ (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom p) =
      (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (cm q φ V₂ h₂ p) := (congrArg (fun f => f p) (cm_nat q φ hnat h₁ h₂ h)).symm


include hnat in
lemma inj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} (U : ι → B.Opens) (hU : ∀ i, U i ≤ V)
    (hcov : V ≤ iSup U) (hinj : ∀ i, Function.Injective (cm q φ (U i) ((hU i).trans h))) :
    Function.Injective (cm q φ V h) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom p = 0 := by
    intro i
    apply hinj i
    rw [cm_nat_apply q φ hnat ((hU i).trans h) h (hU i), hp, map_zero, map_zero]
  ext x
  apply B.sheaf.eq_of_locally_eq' U V (fun i => homOfLE (hU i)) hcov
  intro i
  have h2 := congrArg (fun r => r.coeff x) (h1 i)
  have h3 : (B.presheaf.map (homOfLE (hU i)).op).hom (p.coeff x) = 0 := by simpa using h2
  refine h3.trans ?_
  exact (map_zero _).symm


include hnat in
lemma surj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} [Finite ι] (U : ι → B.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ iSup U)
    (hsurj : ∀ i, Function.Surjective (cm q φ (U i) ((hU i).trans h)))
    (hinj2 : ∀ i j, Function.Injective (cm q φ (U i ⊓ U j) (inf_le_left.trans ((hU i).trans h)))) :
    Function.Surjective (cm q φ V h) := by
  classical
  intro s
  haveI := Fintype.ofFinite ι
  have hloc : ∀ i, ∃ p : AddMonoidAlgebra Γ(B, U i) X, cm q φ (U i) ((hU i).trans h) p =
      (G.presheaf.map (homOfLE (q.preimage_mono (hU i))).op).hom s := fun i => hsurj i _
  choose p hp using hloc
  have hcompat : ∀ i j,
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (p i) =
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (p j) := by
    intro i j
    apply hinj2 i j
    rw [cm_nat_apply q φ hnat _ ((hU i).trans h) inf_le_left,
      cm_nat_apply q φ hnat _ ((hU j).trans h) inf_le_right, hp i, hp j, res_res, res_res]
  have hcx : ∀ x : X, TopCat.Presheaf.IsCompatible B.sheaf.1 U (fun i => (p i).coeff x) := by
    intro x i j
    have e := congrArg (fun r => r.coeff x) (hcompat i j)
    simp only [AddMonoidAlgebra.coeff_mapRingHom] at e
    exact e
  have hglue : ∀ x : X, ∃ c : Γ(B, V), ∀ i, (B.presheaf.map (homOfLE (hU i)).op).hom c = (p i).coeff x := by
    intro x
    obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' B.sheaf U V (fun i => homOfLE (hU i)) hcov
      (fun i => (p i).coeff x) (hcx x)
    exact ⟨c, hc⟩
  choose c hc using hglue
  let S : Finset X := Finset.univ.biUnion (fun i => (p i).coeff.support)
  let F : X →₀ Γ(B, V) := ∑ x ∈ S, Finsupp.single x (c x)
  have hF : ∀ x, F x = if x ∈ S then c x else 0 := by
    intro x
    simp [F, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hres : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom
      (AddMonoidAlgebra.ofCoeff F) = p i := by
    intro i
    apply AddMonoidAlgebra.coeff_injective
    ext x
    rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_ofCoeff, hF]
    split_ifs with hx
    · exact hc x i
    · rw [map_zero]
      symm
      by_contra hne
      exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hne⟩)
  refine ⟨AddMonoidAlgebra.ofCoeff F, ?_⟩
  have hcovG : q ⁻¹ᵁ V ≤ iSup (fun i => q ⁻¹ᵁ U i) := by
    have e := q.preimage_mono hcov
    rw [Scheme.Hom.preimage_iSup] at e
    exact e
  apply TopCat.Sheaf.eq_of_locally_eq' G.sheaf (fun i => q ⁻¹ᵁ U i) (q ⁻¹ᵁ V)
    (fun i => homOfLE (q.preimage_mono (hU i))) hcovG
  intro i
  have e1 := cm_nat_apply q φ hnat ((hU i).trans h) h (hU i) (AddMonoidAlgebra.ofCoeff F)
  rw [hres i, hp i] at e1
  exact e1.symm

end GluingInclusion


end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
