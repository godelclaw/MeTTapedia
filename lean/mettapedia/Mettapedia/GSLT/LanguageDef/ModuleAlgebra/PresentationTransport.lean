import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluing

/-!
# Origin-preserving changes of module presentation

Bijective changes of labels and authored bodies retain declaration origins.
They commute with checked joins, including rejection. Independently proved
preservation of each contextual equation's satisfaction transports the existing
models and produces an isomorphism of their free binding-clone quotients.
The quotient maps preserve complete simultaneous substitution. This is over
one binding signature; changing that signature has separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransport

open Mettapedia.OSLF.Binding SemanticGluing

variable {Origin Label Body Label' Body' : Type}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]
  [DecidableEq Label'] [DecidableEq Body']

def entryEquiv (labels : Label ≃ Label') (bodies : Body ≃ Body') :
    Entry Origin Label Body ≃ Entry Origin Label' Body' where
  toFun entry := ⟨entry.origin, labels entry.label, bodies entry.body⟩
  invFun entry := ⟨entry.origin, labels.symm entry.label, bodies.symm entry.body⟩
  left_inv := by intro entry; cases entry; simp
  right_inv := by intro entry; cases entry; simp

def mapFragment (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Fragment (Origin := Origin) (Label := Label') (Body := Body') :=
  entries.map (entryEquiv labels bodies).toEmbedding

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]
  [DecidableEq Label'] [DecidableEq Body'] in
theorem valid_map_iff (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Valid (mapFragment labels bodies entries) ↔ Valid entries := by
  constructor
  · intro valid first firstMem second secondMem overlap
    apply (entryEquiv labels bodies).injective
    apply valid _ (Finset.mem_map.mpr ⟨first, firstMem, rfl⟩)
      _ (Finset.mem_map.mpr ⟨second, secondMem, rfl⟩)
    exact overlap.imp id (congrArg labels)
  · intro valid first firstMem second secondMem overlap
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp firstMem
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp secondMem
    apply congrArg (entryEquiv labels bodies)
    apply valid a ha b hb
    exact overlap.imp id (fun equal => labels.injective equal)

def mapPresentation (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (p : Presentation Origin Label Body) : Presentation Origin Label' Body' :=
  ⟨mapFragment labels bodies p.val, (valid_map_iff labels bodies p.val).mpr p.property⟩

theorem mapPresentation_inverse (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (p : Presentation Origin Label Body) :
    mapPresentation labels.symm bodies.symm (mapPresentation labels bodies p) = p := by
  apply Subtype.ext
  change (p.val.map (entryEquiv labels bodies).toEmbedding).map
      (entryEquiv labels.symm bodies.symm).toEmbedding = p.val
  rw [Finset.map_map]
  have identity : (entryEquiv labels bodies).toEmbedding.trans
      (entryEquiv labels.symm bodies.symm).toEmbedding =
        Function.Embedding.refl (Entry Origin Label Body) := by
    ext entry
    cases entry
    simp [entryEquiv]
  rw [identity, Finset.map_refl]

def presentationEquiv (labels : Label ≃ Label') (bodies : Body ≃ Body') :
    Presentation Origin Label Body ≃ Presentation Origin Label' Body' where
  toFun := mapPresentation labels bodies
  invFun := mapPresentation labels.symm bodies.symm
  left_inv := mapPresentation_inverse labels bodies
  right_inv := by
    intro p
    simpa using mapPresentation_inverse labels.symm bodies.symm p

theorem mapPresentation_comp {Label'' Body'' : Type}
    [DecidableEq Label''] [DecidableEq Body'']
    (firstLabels : Label ≃ Label') (secondLabels : Label' ≃ Label'')
    (firstBodies : Body ≃ Body') (secondBodies : Body' ≃ Body'')
    (p : Presentation Origin Label Body) :
    mapPresentation secondLabels secondBodies (mapPresentation firstLabels firstBodies p) =
      mapPresentation (firstLabels.trans secondLabels) (firstBodies.trans secondBodies) p := by
  apply Subtype.ext
  change (p.val.map (entryEquiv firstLabels firstBodies).toEmbedding).map
      (entryEquiv secondLabels secondBodies).toEmbedding =
    p.val.map (entryEquiv (firstLabels.trans secondLabels)
      (firstBodies.trans secondBodies)).toEmbedding
  rw [Finset.map_map]
  congr 1

theorem map_inclusion (labels : Label ≃ Label') (bodies : Body ≃ Body')
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val) :
    (mapPresentation labels bodies p).val ⊆ (mapPresentation labels bodies q).val := by
  intro entry member
  change entry ∈ p.val.map (entryEquiv labels bodies).toEmbedding at member
  obtain ⟨old, oldMember, rfl⟩ := Finset.mem_map.mp member
  exact Finset.mem_map.mpr ⟨old, included oldMember, rfl⟩

theorem map_check (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    (check entries).map (mapPresentation labels bodies) =
      check (mapFragment labels bodies entries) := by
  by_cases valid : Valid entries
  · have mapped := (valid_map_iff labels bodies entries).mpr valid
    simp [check, valid, mapped, mapPresentation]
  · have mapped : ¬ Valid (mapFragment labels bodies entries) :=
      fun h => valid ((valid_map_iff labels bodies entries).mp h)
    simp [check, valid, mapped]

/-- Both successful joins and collisions are preserved. -/
theorem map_join (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (p q : Presentation Origin Label Body) :
    (join p q).map (mapPresentation labels bodies) =
      join (mapPresentation labels bodies p) (mapPresentation labels bodies q) := by
  rw [join, map_check]
  simp only [join, mapPresentation, mapFragment, Finset.map_union]

theorem map_join_none_iff (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (p q : Presentation Origin Label Body) :
    join (mapPresentation labels bodies p) (mapPresentation labels bodies q) = none ↔
      join p q = none := by
  rw [← map_join]
  cases join p q <;> simp

/-- Changing notation retains each declaration's origin, including shared
ancestors and independently generated declarations. -/
theorem origins_map (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (p : Presentation Origin Label Body) :
    origins (mapPresentation labels bodies p).val = origins p.val := by
  ext origin
  simp only [origins, Finset.mem_image, mapPresentation, mapFragment, Finset.mem_map]
  constructor
  · rintro ⟨entry, ⟨old, member, rfl⟩, same⟩
    exact ⟨old, member, same⟩
  · rintro ⟨entry, member, same⟩
    exact ⟨entryEquiv labels bodies entry, ⟨entry, member, rfl⟩, same⟩

universe u

variable {S : Signature} {M : List (MetaArity S)}

/-- Generator satisfaction is checked against the existing independent
binding semantics, including captured metavariables and both environments. -/
theorem satisfies_map_iff (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (schema : Body → EqAxiom S M) (targetSchema : Body' → EqAxiom S M)
    (preserves : ∀ (A : BindingCloneAlgebra.Algebra.{u} S) body,
      equationSat targetSchema A (bodies body) ↔ equationSat schema A body)
    (A : BindingCloneAlgebra.Algebra.{u} S) (p : Presentation Origin Label Body) :
    BindingEquationInterpretation.Satisfies A
        (equations targetSchema (mapPresentation labels bodies p)) ↔
      BindingEquationInterpretation.Satisfies A (equations schema p) := by
  simp only [satisfies_iff_models]
  constructor
  · intro satisfied body ⟨entry, member, same⟩
    subst body
    apply (preserves A entry.body).mp
    apply satisfied
    exact ⟨entryEquiv labels bodies entry, Finset.mem_map.mpr ⟨entry, member, rfl⟩, rfl⟩
  · intro satisfied body ⟨entry, member, same⟩
    change entry ∈ p.val.map (entryEquiv labels bodies).toEmbedding at member
    obtain ⟨old, oldMember, rfl⟩ := Finset.mem_map.mp member
    subst body
    apply (preserves A old.body).mpr
    exact satisfied ⟨old, oldMember, rfl⟩

/-- Transport changes the equation presentation and retains the entire
binding algebra, rather than only its output values. -/
def modelEquiv (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (schema : Body → EqAxiom S M) (targetSchema : Body' → EqAxiom S M)
    (preserves : ∀ (A : BindingCloneAlgebra.Algebra.{u} S) body,
      equationSat targetSchema A (bodies body) ↔ equationSat schema A body)
    (p : Presentation Origin Label Body) :
    Model.{u} schema p ≃ Model.{u} targetSchema (mapPresentation labels bodies p) where
  toFun model := ⟨model.algebra,
    (satisfies_map_iff labels bodies schema targetSchema preserves model.algebra p).mpr
      model.satisfies⟩
  invFun model := ⟨model.algebra,
    (satisfies_map_iff labels bodies schema targetSchema preserves model.algebra p).mp
      model.satisfies⟩
  left_inv := fun _ => model_ext rfl
  right_inv := fun _ => model_ext rfl

/-- The semantic transport commutes with the already qualified gluing map. -/
theorem modelEquiv_glue (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (schema : Body → EqAxiom S M) (targetSchema : Body' → EqAxiom S M)
    (preserves : ∀ (A : BindingCloneAlgebra.Algebra.{u} S) body,
      equationSat targetSchema A (bodies body) ↔ equationSat schema A body)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (pair : CompatibleModels.{u} schema p q) :
    modelEquiv labels bodies schema targetSchema preserves r (glueModel schema joined pair) =
      glueModel targetSchema
        (by rw [← map_join, joined]; rfl)
        ⟨(modelEquiv labels bodies schema targetSchema preserves p pair.val.1,
          modelEquiv labels bodies schema targetSchema preserves q pair.val.2), pair.property⟩ :=
  model_ext rfl

open _root_.CategoryTheory

/-- A different authored equation presentation receives a genuine
isomorphism of free binding clones, obtained from their initiality. -/
noncomputable def quotientIso (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (schema : Body → EqAxiom S M) (targetSchema : Body' → EqAxiom S M)
    (preserves : ∀ (A : BindingCloneAlgebra.Algebra.{0} S) body,
      equationSat targetSchema A (bodies body) ↔ equationSat schema A body)
    (p : Presentation Origin Label Body) :
    (FreeBindingEquationModel.presented (equations schema p)).algebra ≅
      (FreeBindingEquationModel.presented
        (equations targetSchema (mapPresentation labels bodies p))).algebra where
  hom := FreeBindingEquationModel.interpretHom
    ((modelEquiv labels bodies schema targetSchema preserves p).symm
      (FreeBindingEquationModel.presented
        (equations targetSchema (mapPresentation labels bodies p))))
  inv := FreeBindingEquationModel.interpretHom
    (modelEquiv labels bodies schema targetSchema preserves p
      (FreeBindingEquationModel.presented (equations schema p)))
  hom_inv_id := by
    exact (FreeBindingEquationModel.hom_unique
      (FreeBindingEquationModel.presented (equations schema p)) _).trans
      (FreeBindingEquationModel.hom_unique
        (FreeBindingEquationModel.presented (equations schema p)) _).symm
  inv_hom_id := by
    exact (FreeBindingEquationModel.hom_unique
      (FreeBindingEquationModel.presented
        (equations targetSchema (mapPresentation labels bodies p))) _).trans
      (FreeBindingEquationModel.hom_unique
        (FreeBindingEquationModel.presented
          (equations targetSchema (mapPresentation labels bodies p))) _).symm

/-- Interpreting after quotient transport gives the original interpretation
in every model. This is naturality of the actual binding-clone comparison. -/
theorem quotientIso_interpretation (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (schema : Body → EqAxiom S M) (targetSchema : Body' → EqAxiom S M)
    (preserves : ∀ (A : BindingCloneAlgebra.Algebra.{0} S) body,
      equationSat targetSchema A (bodies body) ↔ equationSat schema A body)
    (p : Presentation Origin Label Body) (model : Model.{0} schema p) :
    FreeBindingClone.Hom.comp (quotientIso labels bodies schema targetSchema preserves p).hom
        (FreeBindingEquationModel.interpretHom
          (modelEquiv labels bodies schema targetSchema preserves p model)) =
      FreeBindingEquationModel.interpretHom model :=
  FreeBindingEquationModel.hom_unique model _

/-- Changing a presentation commutes with its canonical quotient inclusion.
This is the free-model comparison behind transport of module joins. -/
theorem quotientIso_inclusion (labels : Label ≃ Label') (bodies : Body ≃ Body')
    (schema : Body → EqAxiom S M) (targetSchema : Body' → EqAxiom S M)
    (preserves : ∀ (A : BindingCloneAlgebra.Algebra.{0} S) body,
      equationSat targetSchema A (bodies body) ↔ equationSat schema A body)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val) :
    FreeBindingClone.Hom.comp (quotientInclusion schema included)
        (quotientIso labels bodies schema targetSchema preserves q).hom =
      FreeBindingClone.Hom.comp (quotientIso labels bodies schema targetSchema preserves p).hom
        (quotientInclusion targetSchema (map_inclusion labels bodies included)) := by
  let model := restrict schema included
    ((modelEquiv labels bodies schema targetSchema preserves q).symm
      (FreeBindingEquationModel.presented
        (equations targetSchema (mapPresentation labels bodies q))))
  exact (FreeBindingEquationModel.hom_unique model _).trans
    (FreeBindingEquationModel.hom_unique model _).symm

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransport
