import Mettapedia.Logic.WorldModel.Indexed.Doctrine
import Mettapedia.PLN.WorldModel.WorldModelInstitution

/-!
# The world-model institution as a doctrine over signatures

Signatures with their morphisms form a category (`sigCategory`); sentences form
the query functor (`sentences`), whose functor laws are the existing
`mapSentence_id` and `mapSentence_comp`.  With constant binary evidence the
profile functor's restriction is the existing `profilePrecomp`
(`profiles_map_apply`), so `profilePrecomp_id` and `profilePrecomp_comp` are
functoriality of the profile functor (`profilePrecomp_id_of_functor`,
`profilePrecomp_comp_of_functor`).  A typed world model at a signature is a
world model of the doctrine at that world (`sigModel`).

**The satisfaction condition is the doctrine's equation.**  Along a signature
morphism, a pair of world models satisfies the condition exactly when the
identity of the state is a morphism of the total category over the morphism,
from the source model to the target model (`satisfactionAlong_iff_doctrineHom`).
So every morphism of an institution bundle is a doctrine morphism
(`WMInstitution.doctrineHom`).  The reindexed world model is one instance
(`reindexHom`, `satisfactionCondition_of_reindexHom`); a bundle that reads one
world model through translations into a common signature is another
(`consistentInstitution`).

**Negative.** A source model answering zero and a target model answering the
state violate the condition along the identity of signatures
(`zero_identity_not_satisfactionAlong`), and the doctrine refuses the identity
state map between them (`inconsistentInstitution_not_doctrineHom`).

The bundle's `Hom` carries no category laws; only its image in `WMSignature`
under `mapHom` is a category.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.InstitutionBridge

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.WorldModelInstitution

/-- World-model signatures are worlds: signature morphisms compose as functions
on sorts and sentences. -/
instance sigCategory : Category WMSignature where
  Hom sig1 sig2 := WMSigMorphism sig1 sig2
  id sig := Mettapedia.PLN.WorldModel.WorldModelInstitution.id sig
  comp f g := Mettapedia.PLN.WorldModel.WorldModelInstitution.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Sentences translate forward along signature morphisms. -/
def sentences : WMSignature ⥤ Type where
  obj sig := Sentence sig
  map σ := ↾(mapSentence σ)
  map_id sig := by
    show (↾(mapSentence (𝟙 sig)) : Sentence sig ⟶ Sentence sig) = 𝟙 _
    rw [show mapSentence (𝟙 sig) = fun q => q from funext (mapSentence_id sig)]
    rfl
  map_comp σ τ := by
    show (↾(mapSentence (σ ≫ τ)) : _ ⟶ _) = ↾(mapSentence σ) ≫ ↾(mapSentence τ)
    rw [show mapSentence (σ ≫ τ) = fun q => mapSentence τ (mapSentence σ q) from
      funext (mapSentence_comp σ τ)]
    rfl

/-- Binary evidence at every signature. -/
noncomputable def binaryEvidence : WMSignatureᵒᵖ ⥤ AddCommMonCat :=
  (Functor.const _).obj (AddCommMonCat.of BinaryEvidence)

/-- The profile functor of the institution. -/
noncomputable abbrev profiles : WMSignatureᵒᵖ ⥤ AddCommMonCat := profileFunctor sentences binaryEvidence

/-- Restriction of profiles is the existing precomposition. -/
theorem profiles_map_apply {sig1 sig2 : WMSignature} (σ : sig1 ⟶ sig2)
    (F : Sentence sig2 → BinaryEvidence) :
    (profiles.map σ.op).hom F = profilePrecomp σ F := rfl

/-- `profilePrecomp_id` is the identity law of the profile functor. -/
theorem profilePrecomp_id_of_functor (sig : WMSignature) (F : Sentence sig → BinaryEvidence) :
    profilePrecomp (Mettapedia.PLN.WorldModel.WorldModelInstitution.id sig) F = F := by
  have := congrArg (fun k => k.hom F) (profiles.map_id (op sig))
  exact this

/-- `profilePrecomp_comp` is the composition law of the profile functor. -/
theorem profilePrecomp_comp_of_functor {sig1 sig2 sig3 : WMSignature} (σ : sig1 ⟶ sig2)
    (τ : sig2 ⟶ sig3) (F : Sentence sig3 → BinaryEvidence) :
    profilePrecomp (Mettapedia.PLN.WorldModel.WorldModelInstitution.comp σ τ) F =
      profilePrecomp σ (profilePrecomp τ F) := by
  have := congrArg (fun k => k.hom F) (profiles.map_comp τ.op σ.op)
  exact this

variable {State : Type} [EvidenceType State]

/-- The evidence profile of a typed world model, as one additive map. -/
noncomputable def evidenceProfileHom (sig : WMSignature)
    (wm : WorldModelSigma State sig.Srt sig.Query) : State →+ (Sentence sig → BinaryEvidence) :=
  letI := wm
  { toFun := evidenceProfile (State := State) sig
    map_zero' := funext fun q => WorldModelSigma.evidence_zero (State := State) q
    map_add' := fun W₁ W₂ => funext fun q => WorldModelSigma.evidence_add W₁ W₂ q }

/-- A typed world model at a signature is a world model of the doctrine at that
world. -/
noncomputable def sigModel (sig : WMSignature) (wm : WorldModelSigma State sig.Srt sig.Query) :
    Over (profiles.obj (op sig)) :=
  Over.mk (AddCommMonCat.ofHom (evidenceProfileHom sig wm) :
    AddCommMonCat.of State ⟶ profiles.obj (op sig))

/-- **The satisfaction condition is the reindexing equation**: the identity of
the state is a morphism over `σ` from the reindexed model to the original. -/
noncomputable def reindexHom {sig1 sig2 : WMSignature} (σ : sig1 ⟶ sig2)
    (wm : WorldModelSigma State sig2.Srt sig2.Query) :
    Total.mk profiles sig1 (sigModel sig1 (reindexWorldModelSigma (State := State) σ)) ⟶
      Total.mk profiles sig2 (sigModel sig2 wm) :=
  homOver profiles σ (𝟙 _) rfl

/-- The existing naturality statement, read off the morphism. -/
theorem satisfactionCondition_of_reindexHom {sig1 sig2 : WMSignature} (σ : sig1 ⟶ sig2)
    (wm : WorldModelSigma State sig2.Srt sig2.Query) (W : State) :
    letI : WorldModelSigma State sig2.Srt sig2.Query := wm
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) σ
    evidenceProfile (State := State) sig1 W =
      profilePrecomp σ (evidenceProfile (State := State) sig2 W) := by
  have w := ((totalHomEquiv profiles (reindexHom σ wm)).2.2)
  exact (congrArg (fun k : AddCommMonCat.of State ⟶ profiles.obj (op sig1) => k.hom W) w).symm

/-! ## The satisfaction condition is the doctrine's equation -/

/-- **The satisfaction condition along a morphism is the restriction equation
of the doctrine** for the identity state map from the source model to the
target model. -/
theorem satisfactionAlong_iff_doctrineHom {sig1 sig2 : WMSignature} (σ : sig1 ⟶ sig2)
    (wm1 : WorldModelSigma State sig1.Srt sig1.Query)
    (wm2 : WorldModelSigma State sig2.Srt sig2.Query) :
    SatisfactionAlong σ wm1 wm2 ↔
      𝟙 (AddCommMonCat.of State) ≫ (sigModel sig2 wm2).hom ≫ profiles.map σ.op =
        (sigModel sig1 wm1).hom := by
  constructor
  · intro h
    exact (overArrow_iff sentences binaryEvidence σ (sigModel sig1 wm1) (sigModel sig2 wm2)
      (𝟙 _)).2 fun W φ => (h W φ).symm
  · intro w W φ
    exact ((overArrow_iff sentences binaryEvidence σ (sigModel sig1 wm1) (sigModel sig2 wm2)
      (𝟙 _)).1 w W φ).symm

/-- **Every morphism of an institution bundle is a doctrine morphism**: the
identity of the state, over the signature morphism, from the source world
model to the target world model. -/
noncomputable def _root_.Mettapedia.PLN.WorldModel.WorldModelInstitution.WMInstitution.doctrineHom
    (I : WMInstitution) {sig1 sig2 : I.Sig} (h : I.Hom sig1 sig2) :
    Total.mk profiles (I.sigData sig1) (sigModel (I.sigData sig1) (I.worldModel sig1)) ⟶
      Total.mk profiles (I.sigData sig2) (sigModel (I.sigData sig2) (I.worldModel sig2)) :=
  homOver profiles (I.mapHom h) (𝟙 _)
    ((satisfactionAlong_iff_doctrineHom (I.mapHom h) _ _).1 (I.sat_condition h))

/-- The reindexed world model satisfies the condition, read through the
doctrine. -/
theorem satisfactionAlong_reindex_doctrine {sig1 sig2 : WMSignature} (σ : sig1 ⟶ sig2)
    (wm : WorldModelSigma State sig2.Srt sig2.Query) :
    𝟙 (AddCommMonCat.of State) ≫ (sigModel sig2 wm).hom ≫ profiles.map σ.op =
      (sigModel sig1 (reindexWorldModelSigma (State := State) σ)).hom :=
  (satisfactionAlong_iff_doctrineHom σ _ wm).1 (satisfactionAlong_reindex σ wm)

/-! ## Positive and negative bundles over two signatures -/

/-- One sort with one sentence. -/
def unitSignature : WMSignature := ⟨Unit, fun _ => Unit⟩

/-- The world model that answers zero. -/
@[instance_reducible] noncomputable def zeroModel : WorldModelSigma BinaryEvidence Unit (fun _ : Unit => Unit) where
  evidence _ _ := 0
  evidence_add _ _ _ := (add_zero 0).symm
  evidence_zero _ := rfl

/-- The world model that answers the state itself. -/
@[instance_reducible] noncomputable def identityModel : WorldModelSigma BinaryEvidence Unit (fun _ : Unit => Unit) where
  evidence W _ := W
  evidence_add _ _ _ := rfl
  evidence_zero _ := rfl

/-- **Negative.** A source model answering zero and a target model answering
the state violate the satisfaction condition along the identity of
signatures, so no institution bundle assigns them to the ends of a morphism
mapped to that identity. -/
theorem zero_identity_not_satisfactionAlong :
    ¬ SatisfactionAlong (Mettapedia.PLN.WorldModel.WorldModelInstitution.id unitSignature)
        zeroModel identityModel := by
  intro h
  have one : (0 : BinaryEvidence) = 1 := h 1 ⟨(), ()⟩
  exact zero_ne_one (congrArg BinaryEvidence.pos one)

/-- **The doctrine refuses the same pair.** Along the identity of signatures,
the identity of the state is not a morphism of the doctrine from the
zero-answering model to the state-answering model. -/
theorem inconsistentInstitution_not_doctrineHom :
    ¬ ((𝟙 (AddCommMonCat.of BinaryEvidence)) ≫
        (sigModel (State := BinaryEvidence) unitSignature identityModel).hom ≫
          profiles.map (𝟙 unitSignature : unitSignature ⟶ unitSignature).op =
        (sigModel (State := BinaryEvidence) unitSignature zeroModel).hom) :=
  fun w => zero_identity_not_satisfactionAlong
    ((satisfactionAlong_iff_doctrineHom (𝟙 unitSignature) zeroModel identityModel).2 w)

/-- **Positive.** Two copies of the one-sentence signature, `false` and `true`,
both translated identically into it and both reading the state-answering
model through the translation. -/
noncomputable def consistentInstitution : WMInstitution :=
  WMInstitution.overTop BinaryEvidence unitSignature identityModel (fun _ : Bool => unitSignature)
    (fun _ => Mettapedia.PLN.WorldModel.WorldModelInstitution.id unitSignature)

/-- The morphism `false → true` of the positive bundle: the identity of
signatures, which commutes with the translations. -/
def consistentInstitution_up : consistentInstitution.Hom false true :=
  ⟨Mettapedia.PLN.WorldModel.WorldModelInstitution.id unitSignature, fun phi => by
    cases phi
    rfl⟩

/-- Its doctrine morphism over `false → true`. -/
noncomputable def consistentInstitution_doctrineHom :=
  consistentInstitution.doctrineHom consistentInstitution_up

/-- Both ends of the positive bundle answer the state. -/
theorem consistentInstitution_evidence (b : Bool) (W : BinaryEvidence)
    (phi : Sentence unitSignature) :
    @satEvidence BinaryEvidence _ unitSignature (consistentInstitution.worldModel b) W phi = W :=
  rfl

end Mettapedia.Logic.WorldModel.Indexed.InstitutionBridge
