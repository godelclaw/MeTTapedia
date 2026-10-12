import Mettapedia.Logic.InstitutionCategory
import Mettapedia.Logic.InstitutionCanary
import Mathlib.CategoryTheory.Grothendieck

/-!
# The Grothendieck institution of a logic graph

A logic graph is a diagram of institutions and comorphisms, a functor from an
index category into the heterogeneous category of institutions.  Its
Grothendieck institution (Diaconescu) flattens the diagram into one
institution:

* a signature is a node of the graph together with a native signature of that
  node; a signature morphism is a graph arrow together with a native morphism
  out of the translated signature;
* sentences and models are those of the node, and satisfaction is the node's
  own satisfaction;
* translation along a heterogeneous signature morphism first applies the
  comorphism of the graph arrow and then the native signature morphism, and
  model reduct goes back the same way.

The construction is made once, over the whole category of institutions
(`universal`), where identities and composites of comorphisms are the
identity and composite routes by definition.  The flattening of a particular
graph is the reindexing of the universal institution along the comparison
functor of Grothendieck constructions (`flatten`).

Each node embeds into its flattening by a canonical comorphism (`node`).  The
embedding covers models, so a node's consequence relation is exactly the
flattening's consequence relation at the node's signatures
(`node_entails_iff`): flattening hosts every node faithfully and adds no
commitment.  Every graph arrow becomes a signature morphism of the
flattening (`arrow`) whose sentence translation and model reduct are those of
the arrow's comorphism (`arrow_sentence`, `arrow_satisfaction`), and the
embeddings of the two endpoints are related by it (`node_arrow_sentence`):
the node embeddings form a lax cocone.

Control: inside the universal construction the collapsing comorphism of the
canary module is a signature morphism along which consequence is not
reflected (`Control.collapse_not_conservative`), while the node embedding of
its source logic reflects every consequence
(`Control.source_node_faithful`): flattening neither hides nor repairs a
non-conservative arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic

open CategoryTheory
open scoped CategoryTheory

universe uIndex uIndexHom uSignature uSignatureHom uSentence uModel uModelHom
  uSignature' uSignatureHom'

/-! ## Reindexing an institution along a signature functor -/

namespace Institution

variable {Signature : Type uSignature} [Category.{uSignatureHom} Signature]
  {Signature' : Type uSignature'} [Category.{uSignatureHom'} Signature']

/-- An institution read along a functor into its signature category: the
signatures of the new institution name signatures of the old one, and
sentences, models and satisfaction are those of the named signature. -/
def reindex
    (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature)
    (along : Signature' ⥤ Signature) :
    Institution.{uSignature', uSignatureHom', uSentence, uModel, uModelHom} Signature' where
  sentence := along ⋙ institution.sentence
  model := along.op ⋙ institution.model
  satisfies signature := institution.satisfies (along.obj signature)
  satisfaction_condition translation targetModel sentence :=
    institution.satisfaction_condition (along.map translation) targetModel sentence

@[simp]
theorem reindex_satisfies
    (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature)
    (along : Signature' ⥤ Signature) (signature : Signature')
    (model : (institution.reindex along).model.obj (Opposite.op signature))
    (sentence : (institution.reindex along).sentence.obj signature) :
    (institution.reindex along).satisfies signature model sentence ↔
      institution.satisfies (along.obj signature) model sentence :=
  Iff.rfl

/-- Reindexing does not change consequence at a named signature. -/
theorem reindex_entails_iff
    (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature)
    (along : Signature' ⥤ Signature) (signature : Signature')
    (premises : Set ((institution.reindex along).sentence.obj signature))
    (conclusion : (institution.reindex along).sentence.obj signature) :
    (institution.reindex along).Entails signature premises conclusion ↔
      institution.Entails (along.obj signature) premises conclusion :=
  Iff.rfl

end Institution

namespace GrothendieckInstitution

/-! ## The universal construction over all institutions -/

section Universal

/-- The signature category of each institution, and the signature functor of
each comorphism. -/
def signatureFunctor :
    InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} ⥤
      Cat.{uSignatureHom, uSignature} where
  obj institution := institution.Signature
  map route := route.mapSignature.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

set_option linter.checkUnivs false in
/-- Signatures of the universal Grothendieck institution: an institution and
one of its native signatures.  Its universe is that of the bundled
institutions, so all five levels occur together. -/
abbrev UniversalSignature :=
  Grothendieck signatureFunctor.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}

/-- Sentences of a heterogeneous signature are the sentences of its native
signature; translation applies the comorphism and then the native morphism. -/
def universalSentence :
    UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} ⥤
      Type uSentence :=
  Grothendieck.functorFrom
    (fun institution => institution.logic.sentence)
    (fun route => route.mapSentence)
    (fun institution => by
      ext signature sentence
      rfl)
    (fun first middle last earlier later => by
      ext signature sentence
      rfl)

@[simp]
theorem universalSentence_obj
    (signature : UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :
    universalSentence.obj signature = signature.base.logic.sentence.obj signature.fiber :=
  rfl

theorem universalSentence_map
    {source target : UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (translation : source ⟶ target) (sentence : universalSentence.obj source) :
    universalSentence.map translation sentence =
      target.base.logic.sentence.map translation.fiber
        (translation.base.mapSentence.app source.fiber sentence) :=
  rfl

/-- The reduct of a target model along a heterogeneous signature morphism:
first the native reduct along the fibre morphism, then the comorphism's
model view. -/
def universalReduct
    {source target : UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (translation : source ⟶ target) :
    target.base.logic.model.obj (Opposite.op target.fiber) ⟶
      source.base.logic.model.obj (Opposite.op source.fiber) :=
  target.base.logic.model.map translation.fiber.op ≫
    translation.base.mapModel.app (Opposite.op source.fiber)

theorem universalReduct_id
    (signature : UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :
    universalReduct (𝟙 signature) = 𝟙 _ := by
  simp only [universalReduct, Grothendieck.id_fiber, Grothendieck.id_base, eqToHom_op,
    eqToHom_map]
  change eqToHom _ ≫
      ((Functor.isoWhiskerRight (Functor.opId _) signature.base.logic.model) ≪≫
        Functor.leftUnitor signature.base.logic.model).hom.app (Opposite.op signature.fiber) = _
  simp

theorem universalReduct_comp
    {first middle last :
      UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    universalReduct (earlier ≫ later) = universalReduct later ≫ universalReduct earlier := by
  simp only [universalReduct, Grothendieck.comp_fiber, Grothendieck.comp_base, op_comp,
    Functor.map_comp, eqToHom_op, eqToHom_map, Category.assoc]
  change _ ≫ _ ≫ _ ≫
      (Functor.whiskerLeft earlier.base.mapSignature.op later.base.mapModel ≫
        earlier.base.mapModel).app (Opposite.op first.fiber) = _
  have naturality := later.base.mapModel.naturality earlier.fiber.op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at naturality
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.op_obj]
  rw [← Category.assoc (later.base.mapModel.app _), ← naturality]
  rfl

/-- Models of a heterogeneous signature are the native models, reduced
contravariantly along heterogeneous signature morphisms. -/
def universalModel :
    UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}ᵒᵖ ⥤
      Cat.{uModelHom, uModel} where
  obj signature := signature.unop.base.logic.model.obj (Opposite.op signature.unop.fiber)
  map translation := universalReduct translation.unop
  map_id signature := universalReduct_id signature.unop
  map_comp earlier later := universalReduct_comp later.unop earlier.unop

/-- **The universal Grothendieck institution.**  Satisfaction at a
heterogeneous signature is the native satisfaction of its institution; the
satisfaction condition composes the native one with the comorphism's. -/
def universal :
    Institution.{max (uSignature + 1) (uSignatureHom + 1) (uSentence + 1) (uModel + 1)
        (uModelHom + 1), max uSignature uSignatureHom uSentence uModel uModelHom,
        uSentence, uModel, uModelHom}
      UniversalSignature.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} where
  sentence := universalSentence
  model := universalModel
  satisfies signature model sentence :=
    signature.base.logic.satisfies signature.fiber model sentence
  satisfaction_condition := by
    intro source target translation targetModel sentence
    change target.base.logic.satisfies target.fiber targetModel
        (target.base.logic.sentence.map translation.fiber
          (translation.base.mapSentence.app source.fiber sentence)) ↔
      source.base.logic.satisfies source.fiber
        ((translation.base.mapModel.app (Opposite.op source.fiber)).toFunctor.obj
          ((target.base.logic.model.map translation.fiber.op).toFunctor.obj targetModel))
        sentence
    exact (target.base.logic.satisfaction_condition translation.fiber targetModel _).trans
      (translation.base.satisfaction_condition source.fiber _ sentence)

end Universal

/-! ## The flattening of a logic graph -/

section Flattening

variable {Index : Type uSignature} [Category.{uSignatureHom} Index]
  (graph : Index ⥤
    InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})

/-- Signatures of the flattened graph: a node and one of its native
signatures. -/
abbrev Signature := Grothendieck (graph ⋙ signatureFunctor)

/-- **The Grothendieck institution of a logic graph**: the universal
institution read along the comparison of Grothendieck constructions. -/
def flatten :
    Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} (Signature graph) :=
  universal.reindex (Grothendieck.pre signatureFunctor graph)

/-- The flattening as an object of the category of institutions. -/
def flattenObject :
    InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} where
  Signature := Cat.of (Signature graph)
  logic := flatten graph

@[simp]
theorem flatten_satisfies (signature : Signature graph)
    (model : (flatten graph).model.obj (Opposite.op signature))
    (sentence : (flatten graph).sentence.obj signature) :
    (flatten graph).satisfies signature model sentence ↔
      (graph.obj signature.base).logic.satisfies signature.fiber model sentence :=
  Iff.rfl

/-- Translation along a heterogeneous signature morphism of the flattening. -/
theorem flatten_sentence_map {source target : Signature graph} (translation : source ⟶ target)
    (sentence : (flatten graph).sentence.obj source) :
    (flatten graph).sentence.map translation sentence =
      (graph.obj target.base).logic.sentence.map translation.fiber
        ((graph.map translation.base).mapSentence.app source.fiber sentence) :=
  rfl

/-! ### Routes equal to the identity

A graph sends identities to identity routes only up to equality, so the
canonical embeddings meet that equality once, through these two lemmas. -/

theorem identity_mapModel_app
    (institution :
      InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})
    (signature : institution.Signature) :
    (𝟙 institution : institution ⟶ institution).mapModel.app (Opposite.op signature) = 𝟙 _ := by
  change institution.logic.model.map ((Functor.opId _).hom.app (Opposite.op signature)) ≫ 𝟙 _ =
    𝟙 _
  rw [Category.comp_id]
  exact institution.logic.model.map_id _

theorem identity_route_sentence
    {institution :
      InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (route : institution ⟶ institution) (identity : route = 𝟙 institution)
    {signature signature' : institution.Signature}
    (equal : route.mapSignature.obj signature = signature) (map : signature ⟶ signature')
    (sentence : institution.logic.sentence.obj signature) :
    institution.logic.sentence.map (eqToHom equal ≫ map) (route.mapSentence.app signature sentence) =
      institution.logic.sentence.map map sentence := by
  subst identity
  change institution.logic.sentence.map (𝟙 signature ≫ map) sentence = _
  rw [Category.id_comp]

theorem identity_route_model
    {institution :
      InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (route : institution ⟶ institution) (identity : route = 𝟙 institution)
    {signature signature' : institution.Signature}
    (equal : route.mapSignature.obj signature = signature) (map : signature ⟶ signature') :
    institution.logic.model.map (eqToHom equal ≫ map).op ≫
        route.mapModel.app (Opposite.op signature) =
      institution.logic.model.map map.op := by
  subst identity
  rw [identity_mapModel_app]
  change institution.logic.model.map (𝟙 signature ≫ map).op ≫
    𝟙 (institution.logic.model.obj (Opposite.op signature)) = _
  rw [Category.comp_id, Category.id_comp]

/-! ### The canonical embedding of each node -/

/-- **Each node embeds into the flattening.**  Signatures are included as the
node's fibre; sentences and models are unchanged. -/
def node (index : Index) : Institution.Comorphism (graph.obj index).logic (flatten graph) where
  mapSignature := Grothendieck.ι (graph ⋙ signatureFunctor) index
  mapSentence :=
    { app := fun _ => 𝟙 _
      naturality := by
        intro signature signature' map
        ext sentence
        exact (identity_route_sentence (graph.map (𝟙 index)) (graph.map_id index) _ map
          sentence).symm }
  mapModel :=
    { app := fun _ => 𝟙 _
      naturality := by
        intro signature signature' map
        simp only [Category.comp_id, Category.id_comp]
        exact identity_route_model (graph.map (𝟙 index)) (graph.map_id index) _ map.unop }
  satisfaction_condition := by
    intro signature model sentence
    exact Iff.rfl

/-- The embedding of a node reduces every model to itself, so it covers
models. -/
theorem node_coversModels (index : Index) : (node graph index).CoversModels := by
  intro signature model
  exact ⟨model, rfl⟩

/-- **Flattening hosts every node faithfully**: consequence at a node's
signature in the flattening is the node's own consequence. -/
theorem node_entails_iff (index : Index) (signature : (graph.obj index).Signature)
    (premises : Set ((graph.obj index).logic.sentence.obj signature))
    (conclusion : (graph.obj index).logic.sentence.obj signature) :
    (graph.obj index).logic.Entails signature premises conclusion ↔
      (flatten graph).Entails ((node graph index).mapSignature.obj signature)
        (Set.image ((node graph index).mapSentence.app signature) premises)
        ((node graph index).mapSentence.app signature conclusion) :=
  (node graph index).entails_mapped_iff_of_coversModels (node_coversModels graph index)
    signature premises conclusion

/-! ### Graph arrows inside the flattening -/

/-- A graph arrow, at a source signature, is a signature morphism of the
flattening into the translated signature. -/
def arrow {index index' : Index} (route : index ⟶ index')
    (signature : (graph.obj index).Signature) :
    (⟨index, signature⟩ : Signature graph) ⟶
      ⟨index', (graph.map route).mapSignature.obj signature⟩ :=
  ⟨route, 𝟙 _⟩

/-- Translation along the arrow is the comorphism's sentence translation. -/
theorem arrow_sentence {index index' : Index} (route : index ⟶ index')
    (signature : (graph.obj index).Signature)
    (sentence : (graph.obj index).logic.sentence.obj signature) :
    (flatten graph).sentence.map (arrow graph route signature) sentence =
      (graph.map route).mapSentence.app signature sentence := by
  change (graph.obj index').logic.sentence.map (𝟙 _)
      ((graph.map route).mapSentence.app signature sentence) = _
  simp

/-- Reduct along the arrow is the comorphism's model view. -/
theorem arrow_reduct {index index' : Index} (route : index ⟶ index')
    (signature : (graph.obj index).Signature)
    (model : (graph.obj index').logic.model.obj
      (Opposite.op ((graph.map route).mapSignature.obj signature))) :
    ((flatten graph).model.map (arrow graph route signature).op).toFunctor.obj model =
      ((graph.map route).mapModel.app (Opposite.op signature)).toFunctor.obj model := by
  change (((graph.obj index').logic.model.map (𝟙 _).op ≫
      (graph.map route).mapModel.app (Opposite.op signature)).toFunctor.obj model) = _
  simp

/-- **The satisfaction condition of a graph arrow is an instance of the
flattening's satisfaction condition.** -/
theorem arrow_satisfaction {index index' : Index} (route : index ⟶ index')
    (signature : (graph.obj index).Signature)
    (model : (graph.obj index').logic.model.obj
      (Opposite.op ((graph.map route).mapSignature.obj signature)))
    (sentence : (graph.obj index).logic.sentence.obj signature) :
    (graph.obj index').logic.satisfies ((graph.map route).mapSignature.obj signature) model
        ((graph.map route).mapSentence.app signature sentence) ↔
      (graph.obj index).logic.satisfies signature
        (((graph.map route).mapModel.app (Opposite.op signature)).toFunctor.obj model)
        sentence := by
  have law := (flatten graph).satisfaction_condition (arrow graph route signature) model sentence
  rw [arrow_sentence, arrow_reduct] at law
  exact law

/-- **The node embeddings form a lax cocone**: embedding at the source node
and translating along the arrow is embedding the translated sentence at the
target node. -/
theorem node_arrow_sentence {index index' : Index} (route : index ⟶ index')
    (signature : (graph.obj index).Signature)
    (sentence : (graph.obj index).logic.sentence.obj signature) :
    (flatten graph).sentence.map (arrow graph route signature)
        ((node graph index).mapSentence.app signature sentence) =
      (node graph index').mapSentence.app _
        ((graph.map route).mapSentence.app signature sentence) :=
  arrow_sentence graph route signature sentence

/-- Consequence is transported along graph arrows inside the flattening: a
consequence at the source node translates to a consequence at the target
node. -/
theorem arrow_entails {index index' : Index} (route : index ⟶ index')
    (signature : (graph.obj index).Signature)
    (premises : Set ((graph.obj index).logic.sentence.obj signature))
    (conclusion : (graph.obj index).logic.sentence.obj signature)
    (entails : (graph.obj index).logic.Entails signature premises conclusion) :
    (graph.obj index').logic.Entails ((graph.map route).mapSignature.obj signature)
      (Set.image ((graph.map route).mapSentence.app signature) premises)
      ((graph.map route).mapSentence.app signature conclusion) := by
  intro model satisfiesPremises
  rw [arrow_satisfaction]
  apply entails
  intro premise member
  rw [← arrow_satisfaction]
  exact satisfiesPremises _ ⟨premise, member, rfl⟩

end Flattening

/-! ## Control -/

namespace Control

open Mettapedia.Logic.InstitutionCanary

/-- The Boolean predicate logic of the canary module. -/
def boolLogic : InstitutionCategory.Object.{0, 0, 0, 0, 0} where
  Signature := Cat.of OneSignature
  logic := PredicateInstitution.ofCarrier boolCarrier

/-- The one-sentence predicate logic of the canary module. -/
def unitLogic : InstitutionCategory.Object.{0, 0, 0, 0, 0} where
  Signature := Cat.of OneSignature
  logic := PredicateInstitution.ofCarrier unitCarrier

/-- The collapse as an arrow of the category of institutions. -/
def collapseRoute : boolLogic ⟶ unitLogic := collapseComorphism

/-- The collapse as a signature morphism of the universal Grothendieck
institution. -/
def collapseSignatureMorphism :
    (⟨boolLogic, CategoryTheory.Discrete.mk ()⟩ : UniversalSignature.{0, 0, 0, 0, 0}) ⟶
      ⟨unitLogic, CategoryTheory.Discrete.mk ()⟩ :=
  ⟨collapseRoute, 𝟙 _⟩

/-- **Negative control**: after translation along the collapse, the translated
`false` entails the translated `true` at the target signature, while `false`
does not entail `true` at the source signature. -/
theorem collapse_not_conservative :
    universal.Entails ⟨unitLogic, CategoryTheory.Discrete.mk ()⟩
        (Set.image (universal.sentence.map collapseSignatureMorphism) ({false} : Set Bool))
        (universal.sentence.map collapseSignatureMorphism true) ∧
      ¬ universal.Entails ⟨boolLogic, CategoryTheory.Discrete.mk ()⟩ ({false} : Set Bool) true :=
  collapseComorphism_does_not_reflect_entailment

/-- **Positive control**: the universal construction computes the source
logic's own consequence at its signatures. -/
theorem source_node_faithful (premises : Set Bool) (conclusion : Bool) :
    universal.Entails ⟨boolLogic, CategoryTheory.Discrete.mk ()⟩ premises conclusion ↔
      (PredicateInstitution.ofCarrier boolCarrier).Entails (CategoryTheory.Discrete.mk ())
        premises conclusion :=
  Iff.rfl

end Control

#print axioms Institution.reindex
#print axioms GrothendieckInstitution.universal
#print axioms GrothendieckInstitution.flatten
#print axioms GrothendieckInstitution.node
#print axioms GrothendieckInstitution.node_coversModels
#print axioms GrothendieckInstitution.node_entails_iff
#print axioms GrothendieckInstitution.arrow_sentence
#print axioms GrothendieckInstitution.arrow_reduct
#print axioms GrothendieckInstitution.arrow_satisfaction
#print axioms GrothendieckInstitution.node_arrow_sentence
#print axioms GrothendieckInstitution.arrow_entails
#print axioms GrothendieckInstitution.Control.collapse_not_conservative
#print axioms GrothendieckInstitution.Control.source_node_faithful

end GrothendieckInstitution

end Mettapedia.Logic
