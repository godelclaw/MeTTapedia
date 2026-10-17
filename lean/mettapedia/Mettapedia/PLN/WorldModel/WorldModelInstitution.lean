import Mettapedia.PLN.WorldModel.BinaryWorldModel

/-!
# WM Institution Layer (BinaryEvidence-Valued)

This module adds a conservative institution-style layer over `WorldModelSigma`:

- signatures = sort-indexed query families,
- signature morphisms = sort/query transport maps,
- models = WM states (fixed `State` carrier),
- satisfaction value = extracted evidence (and derived scalar views).

The institution law (`SatisfactionAlong`, the field `WMInstitution.sat_condition`)
relates the two world models a bundle assigns to the ends of a signature
morphism: the evidence of a sentence under the source world model is the
evidence of its translation under the target world model, at the same state.
The world model reindexed from the target is one construction that satisfies it
(`satisfactionAlong_reindex`); signatures read through morphisms into one common
signature give a whole institution (`WMInstitution.overTop`).
-/

namespace Mettapedia.PLN.WorldModel.PLNWorldModelInstitution

open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

universe x

/-- Signature object for typed WM queries. -/
structure WMSignature where
  Srt : Type
  Query : Srt → Type

/-- Sentence object for a WM signature (`Sigma Query`). -/
abbrev Sentence (sig : WMSignature) := Sigma sig.Query

/-- Signature morphism: sort map + query transport along the mapped sort. -/
structure WMSigMorphism (sig1 sig2 : WMSignature) where
  mapSort : sig1.Srt → sig2.Srt
  mapQuery : ∀ {s : sig1.Srt}, sig1.Query s → sig2.Query (mapSort s)

/-- Sentence transport along a signature morphism. -/
def mapSentence {sig1 sig2 : WMSignature} (sigma : WMSigMorphism sig1 sig2) :
    Sentence sig1 → Sentence sig2
  | ⟨s, q⟩ => ⟨sigma.mapSort s, sigma.mapQuery q⟩

/-- Identity signature morphism. -/
def id (sig : WMSignature) : WMSigMorphism sig sig where
  mapSort := fun s => s
  mapQuery := fun q => q

/-- Composition of signature morphisms. -/
def comp {sig1 sig2 sig3 : WMSignature}
    (sigma12 : WMSigMorphism sig1 sig2) (sigma23 : WMSigMorphism sig2 sig3) :
    WMSigMorphism sig1 sig3 where
  mapSort := fun s => sigma23.mapSort (sigma12.mapSort s)
  mapQuery := fun q => sigma23.mapQuery (sigma12.mapQuery q)

@[simp] theorem mapSentence_id (sig : WMSignature) (q : Sentence sig) :
    mapSentence (id sig) q = q := by
  cases q
  rfl

@[simp] theorem mapSentence_comp
    {sig1 sig2 sig3 : WMSignature}
    (sigma12 : WMSigMorphism sig1 sig2) (sigma23 : WMSigMorphism sig2 sig3)
    (q : Sentence sig1) :
    mapSentence (comp sigma12 sigma23) q =
      mapSentence sigma23 (mapSentence sigma12 q) := by
  cases q
  rfl

variable {State : Type x} [EvidenceType State]

/-- Reindex a typed WM instance along a signature/query transport map. -/
@[instance_reducible] def reindexWorldModelSigma
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query] :
    WorldModelSigma State sig1.Srt sig1.Query where
  evidence := fun W q => WorldModelSigma.evidence W (mapSentence sigma q)
  evidence_add := by
    intro W1 W2 q
    simpa [mapSentence] using
      (WorldModelSigma.evidence_add (State := State) (Srt := sig2.Srt) (Query := sig2.Query)
        W1 W2 (mapSentence sigma q))
  evidence_zero q := by
    simpa [mapSentence] using
      (WorldModelSigma.evidence_zero (State := State) (Srt := sig2.Srt) (Query := sig2.Query)
        (mapSentence sigma q))

/-- BinaryEvidence-valued satisfaction at a state for a signature sentence. -/
def satEvidence
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (W : State) (phi : Sentence sig) : BinaryEvidence :=
  WorldModelSigma.evidence W phi

/-- Strength-valued satisfaction view. -/
noncomputable def satStrength
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (W : State) (phi : Sentence sig) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (satEvidence (State := State) sig W phi)

/-- Context-sensitive strength-valued satisfaction view. -/
noncomputable def satStrengthWith
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (ctx : BinaryContext) (W : State) (phi : Sentence sig) : ℝ≥0∞ :=
  BinaryEvidence.strengthWith ctx (satEvidence (State := State) sig W phi)

/-- Confidence-valued satisfaction view. -/
noncomputable def satConfidence
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (kappa : ℝ≥0∞) (W : State) (phi : Sentence sig) : ℝ≥0∞ :=
  BinaryEvidence.toConfidence kappa (satEvidence (State := State) sig W phi)

/-- **The satisfaction condition along one signature morphism.** The evidence
of every sentence under the source world model is the evidence of its
translation under the target world model, at every state. -/
def SatisfactionAlong {sig1 sig2 : WMSignature} (sigma : WMSigMorphism sig1 sig2)
    (wm1 : WorldModelSigma State sig1.Srt sig1.Query)
    (wm2 : WorldModelSigma State sig2.Srt sig2.Query) : Prop :=
  ∀ (W : State) (phi : Sentence sig1),
    @satEvidence State _ sig1 wm1 W phi = @satEvidence State _ sig2 wm2 W (mapSentence sigma phi)

/-- The satisfaction condition is equivalent to its strength-free profile form:
the source profile of every state is the precomposed target profile. -/
theorem satisfactionAlong_iff_profile {sig1 sig2 : WMSignature} (sigma : WMSigMorphism sig1 sig2)
    (wm1 : WorldModelSigma State sig1.Srt sig1.Query)
    (wm2 : WorldModelSigma State sig2.Srt sig2.Query) :
    SatisfactionAlong sigma wm1 wm2 ↔
      ∀ W : State, (fun phi => @satEvidence State _ sig1 wm1 W phi) =
        fun phi => @satEvidence State _ sig2 wm2 W (mapSentence sigma phi) :=
  ⟨fun h W => funext (h W), fun h W phi => congrFun (h W) phi⟩

/-- The reindexed world model evidence, at the same state: the defining
equation of `reindexWorldModelSigma`. -/
theorem satisfactionCondition_evidence
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satEvidence (State := State) sig1 W phi =
      satEvidence (State := State) sig2 W (mapSentence sigma phi) := by
  rfl

/-- Satisfaction condition (strength view) under signature/query transport. -/
theorem satisfactionCondition_strength
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satStrength (State := State) sig1 W phi =
      satStrength (State := State) sig2 W (mapSentence sigma phi) := by
  simpa [satStrength] using
    congrArg BinaryEvidence.toStrength
      (satisfactionCondition_evidence (State := State) (sigma := sigma) W phi)

/-- Satisfaction condition (context-sensitive strength view). -/
theorem satisfactionCondition_strengthWith
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (ctx : BinaryContext) (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satStrengthWith (State := State) sig1 ctx W phi =
      satStrengthWith (State := State) sig2 ctx W (mapSentence sigma phi) := by
  simpa [satStrengthWith] using
    congrArg (BinaryEvidence.strengthWith ctx)
      (satisfactionCondition_evidence (State := State) (sigma := sigma) W phi)

/-- Satisfaction condition (confidence view). -/
theorem satisfactionCondition_confidence
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (kappa : ℝ≥0∞) (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satConfidence (State := State) sig1 kappa W phi =
      satConfidence (State := State) sig2 kappa W (mapSentence sigma phi) := by
  simpa [satConfidence] using
    congrArg (BinaryEvidence.toConfidence kappa)
      (satisfactionCondition_evidence (State := State) (sigma := sigma) W phi)

/-- **Positive.** The world model reindexed from the target satisfies the
satisfaction condition along the morphism it was reindexed by. -/
theorem satisfactionAlong_reindex {sig1 sig2 : WMSignature} (sigma : WMSigMorphism sig1 sig2)
    (wm : WorldModelSigma State sig2.Srt sig2.Query) :
    SatisfactionAlong sigma (@reindexWorldModelSigma State _ sig1 sig2 sigma wm) wm :=
  fun _ _ => rfl

/-- Institution bundle over WM signatures with explicit satisfaction condition. -/
structure WMInstitution where
  /-- State carrier and evidence algebra. -/
  State : Type
  instEvidenceType : EvidenceType State
  /-- Signature objects. -/
  Sig : Type
  /-- Sort/query family assigned to each signature. -/
  sigData : Sig → WMSignature
  /-- Signature morphisms. -/
  Hom : Sig → Sig → Type
  /-- Identity morphism. -/
  id : ∀ sig, Hom sig sig
  /-- Composition. -/
  comp : ∀ {sig1 sig2 sig3}, Hom sig1 sig2 → Hom sig2 sig3 → Hom sig1 sig3
  /-- Query-transport action of signature morphisms. -/
  mapHom :
    ∀ {sig1 sig2}, Hom sig1 sig2 →
      WMSigMorphism (sigData sig1) (sigData sig2)
  /-- WM semantics at each signature. -/
  worldModel :
    ∀ sig, WorldModelSigma State (sigData sig).Srt (sigData sig).Query
  /-- The satisfaction condition: along every morphism, the evidence of a
  sentence under the source world model is the evidence of its translation
  under the target world model.  This field formerly compared the target world
  model with its own reindexing, which holds for every choice of world models;
  it now relates the two world models the bundle assigns. -/
  sat_condition :
    ∀ {sig1 sig2} (h : Hom sig1 sig2),
      SatisfactionAlong (mapHom h) (worldModel sig1) (worldModel sig2)

attribute [instance] WMInstitution.instEvidenceType

namespace WMInstitution

/-- Strength-level satisfaction transport derived from the institution's
evidence law, between the two world models the bundle assigns. -/
theorem sat_condition_strength
    (I : WMInstitution)
    {sig1 sig2 : I.Sig}
    (h : I.Hom sig1 sig2) (W : I.State)
    (phi : Sentence (I.sigData sig1)) :
    @satStrength I.State _ (I.sigData sig1) (I.worldModel sig1) W phi =
      @satStrength I.State _ (I.sigData sig2) (I.worldModel sig2) W
        (mapSentence (I.mapHom h) phi) :=
  congrArg BinaryEvidence.toStrength (I.sat_condition h W phi)

/-- Context-sensitive strength transport between the bundle's world models. -/
theorem sat_condition_strengthWith
    (I : WMInstitution)
    {sig1 sig2 : I.Sig}
    (h : I.Hom sig1 sig2) (ctx : BinaryContext) (W : I.State)
    (phi : Sentence (I.sigData sig1)) :
    @satStrengthWith I.State _ (I.sigData sig1) (I.worldModel sig1) ctx W phi =
      @satStrengthWith I.State _ (I.sigData sig2) (I.worldModel sig2) ctx W
        (mapSentence (I.mapHom h) phi) :=
  congrArg (BinaryEvidence.strengthWith ctx) (I.sat_condition h W phi)

/-- Confidence transport between the bundle's world models. -/
theorem sat_condition_confidence
    (I : WMInstitution)
    {sig1 sig2 : I.Sig}
    (h : I.Hom sig1 sig2) (kappa : ℝ≥0∞) (W : I.State)
    (phi : Sentence (I.sigData sig1)) :
    @satConfidence I.State _ (I.sigData sig1) (I.worldModel sig1) kappa W phi =
      @satConfidence I.State _ (I.sigData sig2) (I.worldModel sig2) kappa W
        (mapSentence (I.mapHom h) phi) :=
  congrArg (BinaryEvidence.toConfidence kappa) (I.sat_condition h W phi)

/-! ### A natural instance: signatures over one common signature -/

/-- Morphisms between signatures that both translate into a common signature
`top`: signature morphisms that commute with the translations into `top`. -/
def OverTopHom (top : WMSignature) {ι : Type} (sigOf : ι → WMSignature)
    (toTop : ∀ i, WMSigMorphism (sigOf i) top) (i j : ι) : Type :=
  {h : WMSigMorphism (sigOf i) (sigOf j) //
    ∀ phi, mapSentence (toTop j) (mapSentence h phi) = mapSentence (toTop i) phi}

/-- **The institution of signatures over a common signature.** Each signature
reads one world model at `top` through its translation into `top`; the
satisfaction condition holds because the morphisms commute with the
translations, not by definition. -/
def overTop (State : Type) [EvidenceType State] (top : WMSignature)
    (wm : WorldModelSigma State top.Srt top.Query) {ι : Type} (sigOf : ι → WMSignature)
    (toTop : ∀ i, WMSigMorphism (sigOf i) top) : WMInstitution where
  State := State
  instEvidenceType := inferInstance
  Sig := ι
  sigData := sigOf
  Hom := OverTopHom top sigOf toTop
  id i := ⟨PLNWorldModelInstitution.id (sigOf i), fun phi => by rw [mapSentence_id]⟩
  comp h k := ⟨PLNWorldModelInstitution.comp h.1 k.1, fun phi => by
    rw [mapSentence_comp, k.2, h.2]⟩
  mapHom h := h.1
  worldModel i := @reindexWorldModelSigma State _ (sigOf i) top (toTop i) wm
  sat_condition h W phi := (congrArg (fun q => @satEvidence State _ top wm W q) (h.2 phi)).symm

/-- The evidence of `overTop` at a signature is the common world model's
evidence for the translated sentence. -/
theorem overTop_evidence (State : Type) [EvidenceType State] (top : WMSignature)
    (wm : WorldModelSigma State top.Srt top.Query) {ι : Type} (sigOf : ι → WMSignature)
    (toTop : ∀ i, WMSigMorphism (sigOf i) top) (i : ι) (W : State) (phi : Sentence (sigOf i)) :
    @satEvidence State _ (sigOf i) ((overTop State top wm sigOf toTop).worldModel i) W phi =
      @satEvidence State _ top wm W (mapSentence (toTop i) phi) :=
  rfl

end WMInstitution

/-! ## Profile Natural Transformation View

The satisfaction condition of the reindexed world model is the naturality
square for evidence extraction viewed as a natural transformation; for an
institution bundle the same square relates its two assigned world models
(`WMInstitution.sat_condition_profile`).

For each signature `sig`, define the **evidence profile** of a state:

    Prof(sig)(W) := fun phi => satEvidence sig W phi

This is a function `Sentence sig → BinaryEvidence`, i.e., an element of
`Prof(sig) := Sentence sig → BinaryEvidence`.

A signature morphism `σ : sig₁ → sig₂` induces precomposition:

    Prof(σ) : Prof(sig₂) → Prof(sig₁),  F ↦ F ∘ mapSentence(σ)

The satisfaction condition says exactly that extraction commutes with
this precomposition:

    Prof(σ)(extract_sig₂(W)) = extract_sig₁(W)

which is the naturality square for `extract : Δ(State) ⟹ Prof`. -/

/-- BinaryEvidence profile at a signature: maps each sentence to its evidence. -/
def evidenceProfile
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (W : State) : Sentence sig → BinaryEvidence :=
  fun phi => satEvidence (State := State) sig W phi

/-- Precomposition on profiles along a signature morphism. -/
def profilePrecomp
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2) :
    (Sentence sig2 → BinaryEvidence) → (Sentence sig1 → BinaryEvidence) :=
  fun F phi => F (mapSentence sigma phi)

/-- **Naturality**: satisfaction condition = evidence extraction commutes
    with profile precomposition.

    This is the natural-transformation form of the institution law:
    `extract : Δ(State) ⟹ Prof` where `Prof` is the contravariant
    profile functor on signatures. -/
theorem satisfactionCondition_is_naturality
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (W : State) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    evidenceProfile (State := State) sig1 W =
      profilePrecomp sigma (evidenceProfile (State := State) sig2 W) := by
  funext phi
  exact satisfactionCondition_evidence (State := State) sigma W phi

/-- **The institution law in profile form**: the source world model's profile
is the target world model's profile precomposed with the translation. -/
theorem WMInstitution.sat_condition_profile (I : WMInstitution) {sig1 sig2 : I.Sig}
    (h : I.Hom sig1 sig2) (W : I.State) :
    @evidenceProfile I.State _ (I.sigData sig1) (I.worldModel sig1) W =
      profilePrecomp (I.mapHom h) (@evidenceProfile I.State _ (I.sigData sig2) (I.worldModel sig2) W) :=
  funext (I.sat_condition h W)

/-- Profile precomposition is functorial: identity. -/
theorem profilePrecomp_id (sig : WMSignature)
    (F : Sentence sig → BinaryEvidence) :
    profilePrecomp (id sig) F = F := by
  funext phi; simp [profilePrecomp]

/-- Profile precomposition is functorial: composition. -/
theorem profilePrecomp_comp
    {sig1 sig2 sig3 : WMSignature}
    (sigma12 : WMSigMorphism sig1 sig2) (sigma23 : WMSigMorphism sig2 sig3)
    (F : Sentence sig3 → BinaryEvidence) :
    profilePrecomp (comp sigma12 sigma23) F =
      profilePrecomp sigma12 (profilePrecomp sigma23 F) := by
  funext phi; simp [profilePrecomp]

end Mettapedia.PLN.WorldModel.PLNWorldModelInstitution
