import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire
import Mathlib.Data.W.Basic
import Mathlib.Data.Nat.Size

/-!
# Exact coding of ordered finite derivation certificates

The node payload codec includes every rule parameter. Ordered certificate trees
are represented by the standard finitely branching W type; its constructive
codec supplies an enumeration without a completeness oracle. The wire-size
bound is the bit length of this complete encoding, rather than a node count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates

namespace Tree

universe u

variable {P : Presentation.{u}}

def toW : Tree P → WType (fun rule : P.Rule => Fin (P.premises rule).length)
  | .node rule children => .mk rule (fun position => toW (children position))

def fromW : WType (fun rule : P.Rule => Fin (P.premises rule).length) → Tree P
  | .mk rule children => .node rule (fun position => fromW (children position))

theorem fromW_toW (tree : Tree P) : fromW (toW tree) = tree := by
  induction tree with
  | node rule children ih =>
      change Tree.node rule (fun position => fromW (toW (children position))) =
        Tree.node rule children
      congr 1
      funext position
      exact ih position

instance [Encodable P.Rule] : Encodable (Tree P) :=
  Encodable.ofLeftInverse toW fromW fromW_toW

def wireSize [Encodable P.Rule] (tree : Tree P) : Nat :=
  Nat.size (Encodable.encode tree)

def discoveryBound (wireBits : Nat) : Nat := 2 ^ wireBits

theorem code_lt_discoveryBound [Encodable P.Rule] (tree : Tree P) :
    Encodable.encode tree < discoveryBound (wireSize tree) := Nat.lt_size_self _

theorem decode_encode [Encodable P.Rule] (tree : Tree P) :
    Encodable.decode (α := Tree P) (Encodable.encode tree) = some tree := Encodable.encodek tree

theorem distinct_codes [Encodable P.Rule] {first second : Tree P}
    (different : first ≠ second) : Encodable.encode first ≠ Encodable.encode second :=
  fun same => different (Encodable.encode_injective same)

end Tree

namespace Presentation

open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

universe u
variable (P : Presentation.{u})

/-- The existing premise-list polynomial uses precisely the same rule
instances and occurrence positions as the native finite-tree checker. -/
def finiteRules : FinitePresentation.{0, u, u} Unit (fun _ => P.Judgment) where
  Shape _ judgment := {code : P.Rule // P.conclusion code = judgment}
  premises _ _ code := P.premises code.val

def toFiniteDerivation {judgment : P.Judgment} :
    P.Derivation judgment → P.finiteRules.Derivation () judgment
  | .node code children => .roll code (fun position => toFiniteDerivation (children ⟨position⟩))

def fromFiniteDerivation {judgment : P.Judgment} :
    P.finiteRules.Derivation () judgment → P.Derivation judgment
  | .roll code children => .node code (fun position => fromFiniteDerivation (children position.down))

theorem fromFinite_toFinite {judgment : P.Judgment} (derivation : P.Derivation judgment) :
    P.fromFiniteDerivation (P.toFiniteDerivation derivation) = derivation := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation =>
      P.fromFiniteDerivation (P.toFiniteDerivation derivation) = derivation)
    (t := derivation)
  intro judgment code children ih
  change JudgmentDerivation.Derivation.node code (fun position =>
    P.fromFiniteDerivation (P.toFiniteDerivation (children position))) =
    JudgmentDerivation.Derivation.node code children
  congr 1
  funext position
  exact ih position

theorem toFinite_fromFinite {judgment : P.Judgment}
    (derivation : P.finiteRules.Derivation () judgment) :
    P.toFiniteDerivation (P.fromFiniteDerivation derivation) = derivation := by
  refine IndexedPolynomial.Fix.rec
    (motive := fun judgment derivation =>
      P.toFiniteDerivation (P.fromFiniteDerivation derivation) = derivation) ?_ derivation
  intro judgment code children ih
  change IndexedPolynomial.Fix.roll code (fun position =>
    P.toFiniteDerivation (P.fromFiniteDerivation (children position))) =
    IndexedPolynomial.Fix.roll code children
  congr 1
  funext position
  exact ih position

namespace Morphism

variable {source target : Presentation.{u}} (translation : Morphism source target)

/-- The native checker map is a cartesian map of the existing rule
polynomials: it retains the rule instance and every recursive address. -/
def polynomial :
    Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms.Hom
      source.finiteRules.polynomial target.finiteRules.polynomial
      (fun _ => translation.judgment) where
  onShape _ _ code := ⟨translation.rule code.val,
    (translation.conclusion code.val).trans (congrArg translation.judgment code.property)⟩
  onPosition _ _ code :=
    { toFun := translation.sourceIndex code.val
      invFun := translation.targetIndex code.val
      left_inv := translation.target_source code.val
      right_inv := translation.source_target code.val }
  onNext _ _ code position := translation.premise code.val position

end Morphism

theorem toFinite_castDerivation {first second : P.Judgment} (same : first = second)
    (derivation : P.Derivation first) :
    P.toFiniteDerivation (Tree.castDerivation same derivation) =
      same ▸ P.toFiniteDerivation derivation := by
  subst second
  rfl

/-- Translating a native derivation and translating its polynomial
representation retain the same complete firing history. -/
theorem toFinite_mapDerivation {source target : Presentation.{u}}
    (translation : Morphism source target) {judgment : source.Judgment}
    (derivation : source.Derivation judgment) :
    target.toFiniteDerivation (translation.mapDerivation derivation) =
      translation.polynomial.mapFix () judgment (source.toFiniteDerivation derivation) := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation =>
      target.toFiniteDerivation (translation.mapDerivation derivation) =
        translation.polynomial.mapFix () judgment (source.toFiniteDerivation derivation))
    (t := derivation)
  intro judgment code children ih
  rcases code with ⟨code, rfl⟩
  change IndexedPolynomial.Fix.roll (polynomial := target.finiteRules.polynomial) (base := ())
    (⟨translation.rule code, translation.conclusion code⟩ :
      {rule : target.Rule // target.conclusion rule =
        translation.judgment (source.conclusion code)})
    (fun position =>
      target.toFiniteDerivation (Tree.castDerivation
        (translation.premise code position).symm
        (translation.mapDerivation (children ⟨translation.sourceIndex code position⟩)))) =
    IndexedPolynomial.Fix.roll (polynomial := target.finiteRules.polynomial) (base := ())
    (⟨translation.rule code, translation.conclusion code⟩ :
      {rule : target.Rule // target.conclusion rule =
        translation.judgment (source.conclusion code)})
    (fun position =>
      Eq.rec (motive := fun index _ => target.finiteRules.Derivation () index)
        (translation.polynomial.mapFix () _
          (source.toFiniteDerivation (children ⟨translation.sourceIndex code position⟩)))
        (translation.premise code position).symm)
  congr 1
  funext position
  change Fin (target.premises (translation.rule code)).length at position
  exact (target.toFinite_castDerivation (translation.premise code position).symm
      (translation.mapDerivation (children ⟨translation.sourceIndex code position⟩))).trans
    (congrArg (fun tree : target.finiteRules.Derivation ()
        (translation.judgment ((source.premises code).get (translation.sourceIndex code position))) =>
      Eq.rec (motive := fun index _ => target.finiteRules.Derivation () index)
        tree (translation.premise code position).symm)
      (ih ⟨translation.sourceIndex code position⟩))

/-- Raw rule payloads are the structured labels; conclusion and premise
indices are recomputed from each payload rather than supplied by the sender. -/
def ruleShapeCodec : Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.ShapeCodec P.finiteRules P.Rule where
  encode packet := packet.2.val
  decode code := some ⟨P.conclusion code, ⟨code, rfl⟩⟩
  roundtrip := by rintro ⟨judgment, code, same⟩; cases same; rfl
  canonical := by intro code packet accepted; cases accepted; rfl

end Presentation

namespace Tree

open Mettapedia.OSLF.Binding

universe u
variable {P : Presentation.{u}}

/-- Reuse the common untrusted list-tree wire. Missing and extra premise
occurrences are representable here, unlike in the indexed native tree. -/
abbrev Wire (P : Presentation.{u}) := FiniteRuleLabelledProofWire.Wire P.Rule

def encodeDerivation {judgment : P.Judgment} (derivation : P.Derivation judgment) : Wire P :=
  FiniteRuleLabelledProofWire.encode P.finiteRules P.ruleShapeCodec
    (P.toFiniteDerivation derivation)

def decodeDerivation [DecidableEq P.Judgment] (wire : Wire P) :
    Option (Σ judgment, P.Derivation judgment) :=
  (FiniteRuleLabelledProofWire.decode P.finiteRules P.ruleShapeCodec wire).map
    (fun packet => ⟨packet.1, P.fromFiniteDerivation packet.2⟩)

theorem decode_encodeDerivation [DecidableEq P.Judgment] {judgment : P.Judgment}
    (derivation : P.Derivation judgment) :
    decodeDerivation (encodeDerivation derivation) = some ⟨judgment, derivation⟩ := by
  simp only [decodeDerivation, encodeDerivation, FiniteRuleLabelledProofWire.decode_encode,
    Option.map_some, Presentation.fromFinite_toFinite]

theorem encode_decodeDerivation [DecidableEq P.Judgment] (wire : Wire P)
    (packet : Σ judgment, P.Derivation judgment)
    (accepted : decodeDerivation wire = some packet) : encodeDerivation packet.2 = wire := by
  cases decoded : FiniteRuleLabelledProofWire.decode P.finiteRules P.ruleShapeCodec wire with
  | none => simp only [decodeDerivation, decoded, Option.map_none] at accepted; cases accepted
  | some original =>
      have same : (⟨original.1, P.fromFiniteDerivation original.2⟩ : Σ judgment, P.Derivation judgment) =
          packet := by simpa only [decodeDerivation, decoded, Option.map_some, Option.some.injEq] using accepted
      cases same
      unfold encodeDerivation
      rw [Presentation.toFinite_fromFinite]
      exact FiniteRuleLabelledProofWire.encode_decode P.finiteRules P.ruleShapeCodec wire original decoded

def checkWire [DecidableEq P.Judgment] (wire : Wire P) (judgment : P.Judgment) : Bool :=
  FiniteRuleLabelledProofWire.check P.finiteRules P.ruleShapeCodec judgment wire

theorem checkWire_exact [DecidableEq P.Judgment] (wire : Wire P) (judgment : P.Judgment) :
    checkWire wire judgment = true ↔
      ∃ derivation : P.Derivation judgment, encodeDerivation derivation = wire := by
  rw [checkWire, FiniteRuleLabelledProofWire.check_iff]
  constructor
  · rintro ⟨derivation, encoded⟩
    refine ⟨P.fromFiniteDerivation derivation, ?_⟩
    simpa only [encodeDerivation, Presentation.toFinite_fromFinite] using encoded
  · rintro ⟨derivation, encoded⟩
    exact ⟨P.toFiniteDerivation derivation, encoded⟩

theorem checkWire_complete [DecidableEq P.Judgment] (judgment : P.Judgment) :
    Nonempty (P.Derivation judgment) ↔ ∃ wire : Wire P, checkWire wire judgment = true := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨encodeDerivation derivation, (checkWire_exact _ _).mpr ⟨derivation, rfl⟩⟩
  · rintro ⟨wire, accepted⟩
    obtain ⟨derivation, _⟩ := (checkWire_exact wire judgment).mp accepted
    exact ⟨derivation⟩

/-- The raw wire retains exactly the original proof fibre. It cannot carry
an ignored tag or extra child that is discarded by decoding. -/
def derivationWireEquiv [DecidableEq P.Judgment] (judgment : P.Judgment) :
    P.Derivation judgment ≃ {wire : Wire P // checkWire wire judgment = true} where
  toFun derivation := ⟨encodeDerivation derivation,
    (checkWire_exact _ _).mpr ⟨derivation, rfl⟩⟩
  invFun wire := P.fromFiniteDerivation
    ((FiniteRuleLabelledProofWire.decodeAt P.finiteRules P.ruleShapeCodec judgment wire.val).get
      wire.property)
  left_inv derivation := by
    change P.fromFiniteDerivation
      ((FiniteRuleLabelledProofWire.decodeAt P.finiteRules P.ruleShapeCodec judgment
        (encodeDerivation derivation)).get _) = derivation
    simp only [encodeDerivation, FiniteRuleLabelledProofWire.decodeAt_encode,
      Option.get_some, Presentation.fromFinite_toFinite]
  right_inv wire := by
    apply Subtype.ext
    change encodeDerivation (P.fromFiniteDerivation
      ((FiniteRuleLabelledProofWire.decodeAt P.finiteRules P.ruleShapeCodec judgment wire.val).get
        wire.property)) = wire.val
    unfold encodeDerivation
    rw [Presentation.toFinite_fromFinite]
    exact FiniteRuleLabelledProofWire.decodeAt_exact P.finiteRules P.ruleShapeCodec
      (Option.some_get wire.property).symm

end Tree

end Mettapedia.OSLF.NativeTypes.Certificates
