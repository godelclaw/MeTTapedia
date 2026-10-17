import Mettapedia.TypeTheory.JudgmentDerivation
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.OfFn

/-!
# Finite certificate checking for generated judgment presentations

Unchecked certificates retain a rule code and its ordered child occurrences.
The checker compares each independently computed premise judgment with the
child's conclusion. Its acceptance theorem reconstructs the original indexed
derivation and proves that erasing that derivation recovers the exact input
certificate. No semantic truth or derivability oracle is required.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates

open Mettapedia.TypeTheory

universe u v

structure Presentation where
  Judgment : Type u
  Rule : Type u
  conclusion : Rule → Judgment
  premises : Rule → List Judgment

def Presentation.signature (P : Presentation.{u}) : JudgmentDerivation.Signature.{u} where
  Judgment := P.Judgment
  Rule judgment := {rule : P.Rule // P.conclusion rule = judgment}
  Premise rule := ULift (Fin (P.premises rule.val).length)
  hypothesis rule position := (P.premises rule.val).get position.down

abbrev Presentation.Derivation (P : Presentation.{u}) (judgment : P.Judgment) :=
  JudgmentDerivation.Derivation P.signature judgment

/-- Premise positions are finite and ordered; equal premise judgments do not
identify their distinct certificate occurrences. -/
inductive Tree (P : Presentation.{u}) : Type u where
  | node (rule : P.Rule)
      (children : Fin (P.premises rule).length → Tree P) : Tree P

namespace Tree

variable {P : Presentation.{u}}

def root : Tree P → P.Rule
  | .node rule _ => rule

/-- Syntax equality is the only required decision operation. -/
def check [DecidableEq P.Judgment] : Tree P → P.Judgment → Bool
  | .node rule children, judgment =>
      decide (P.conclusion rule = judgment) &&
        decide (∀ position,
          check (children position) ((P.premises rule).get position) = true)

/-- Erasure keeps complete rule payloads and every ordered premise subtree. -/
def erase {judgment : P.Judgment} : P.Derivation judgment → Tree P
  | .node rule premises => .node rule.val (fun position => erase (premises ⟨position⟩))

/-- A successful check constructs a derivation of the independently supplied
indexed rules. The returned proof retains all original certificate choices. -/
def reconstruct [DecidableEq P.Judgment] : (tree : Tree P) →
    (judgment : P.Judgment) → check tree judgment = true → P.Derivation judgment
  | .node rule children, judgment, accepted => by
      have clauses : decide (P.conclusion rule = judgment) = true ∧
          decide (∀ position,
            check (children position) ((P.premises rule).get position) = true) = true := by
        simpa only [check, Bool.and_eq_true] using accepted
      have conclusion : P.conclusion rule = judgment := of_decide_eq_true clauses.1
      have premises : ∀ position,
          check (children position) ((P.premises rule).get position) = true :=
        of_decide_eq_true clauses.2
      exact .node ⟨rule, conclusion⟩
        (fun position => reconstruct (children position.down)
          ((P.premises rule).get position.down) (premises position.down))

theorem check_erase [DecidableEq P.Judgment] {judgment : P.Judgment}
    (derivation : P.Derivation judgment) : check (erase derivation) judgment = true := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation => check (erase derivation) judgment = true)
    (t := derivation)
  intro judgment rule premises ih
  rcases rule with ⟨rule, conclusion⟩
  cases conclusion
  simp only [erase, check, decide_true, Bool.true_and]
  apply decide_eq_true
  intro position
  exact ih ⟨position⟩

theorem erase_reconstruct [DecidableEq P.Judgment] (tree : Tree P)
    (judgment : P.Judgment) (accepted : check tree judgment = true) :
    erase (reconstruct tree judgment accepted) = tree := by
  induction tree generalizing judgment with
  | node rule children ih =>
      change Tree.node rule (fun position =>
        erase (reconstruct (children position) ((P.premises rule).get position) _)) =
        Tree.node rule children
      congr 1
      funext position
      exact ih position _ _

theorem reconstruct_erase [DecidableEq P.Judgment] {judgment : P.Judgment}
    (derivation : P.Derivation judgment) :
    reconstruct (erase derivation) judgment (check_erase derivation) = derivation := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation =>
      reconstruct (erase derivation) judgment (check_erase derivation) = derivation)
    (t := derivation)
  intro judgment rule premises ih
  rcases rule with ⟨rule, conclusion⟩
  cases conclusion
  change JudgmentDerivation.Derivation.node (S := P.signature) ⟨rule, rfl⟩
    (fun position => reconstruct (erase (premises position))
      ((P.premises rule).get position.down) _) =
    JudgmentDerivation.Derivation.node (S := P.signature) ⟨rule, rfl⟩ premises
  congr 1
  funext position
  exact ih position

theorem erase_injective [DecidableEq P.Judgment] {judgment : P.Judgment} :
    Function.Injective (@erase P judgment) := by
  intro first second same
  have checked := congrArg (fun tree =>
    if accepted : check tree judgment = true then
      some (reconstruct tree judgment accepted) else none) same
  simpa only [dif_pos (check_erase first), dif_pos (check_erase second),
    reconstruct_erase, Option.some.injEq] using checked

/-- Exact acceptance includes occurrence identity, rather than only existence
of some derivation with the same final judgment. -/
theorem check_exact [DecidableEq P.Judgment] (tree : Tree P) (judgment : P.Judgment) :
    check tree judgment = true ↔
      ∃ derivation : P.Derivation judgment, erase derivation = tree := by
  constructor
  · intro accepted
    exact ⟨reconstruct tree judgment accepted, erase_reconstruct tree judgment accepted⟩
  · rintro ⟨derivation, same⟩
    rw [← same]
    exact check_erase derivation

theorem check_sound [DecidableEq P.Judgment] (tree : Tree P) (judgment : P.Judgment)
    (accepted : check tree judgment = true) : Nonempty (P.Derivation judgment) :=
  ⟨reconstruct tree judgment accepted⟩

theorem check_complete [DecidableEq P.Judgment] (judgment : P.Judgment) :
    Nonempty (P.Derivation judgment) ↔ ∃ tree : Tree P, check tree judgment = true := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨erase derivation, check_erase derivation⟩
  · rintro ⟨tree, accepted⟩
    exact check_sound tree judgment accepted

theorem reconstructed_root [DecidableEq P.Judgment] (tree : Tree P)
    (judgment : P.Judgment) (accepted : check tree judgment = true) :
    root (erase (reconstruct tree judgment accepted)) = root tree := by
  rw [erase_reconstruct]

/-- Transport changes the derivation's index, not its supplied rule history. -/
def castDerivation {first second : P.Judgment} (same : first = second)
    (derivation : P.Derivation first) : P.Derivation second := same ▸ derivation

@[simp] theorem erase_cast {first second : P.Judgment} (same : first = second)
    (derivation : P.Derivation first) : erase (castDerivation same derivation) = erase derivation := by
  cases same
  rfl

end Tree

namespace Presentation

/-- A rule translation preserves each premise position. It need not reflect
arbitrary target derivations or identify the two presentations. -/
structure Morphism (source target : Presentation.{u}) where
  judgment : source.Judgment → target.Judgment
  rule : source.Rule → target.Rule
  conclusion : ∀ code, target.conclusion (rule code) = judgment (source.conclusion code)
  premises : ∀ code, target.premises (rule code) = (source.premises code).map judgment

namespace Morphism

variable {source target : Presentation.{u}} (translation : Morphism source target)

/-- Target and source premise positions have the same ordinal. -/
def sourceIndex (code : source.Rule)
    (position : Fin (target.premises (translation.rule code)).length) :
    Fin (source.premises code).length :=
  ⟨position.val, by simpa only [translation.premises, List.length_map] using position.isLt⟩

def targetIndex (code : source.Rule) (position : Fin (source.premises code).length) :
    Fin (target.premises (translation.rule code)).length :=
  ⟨position.val, by simpa only [translation.premises, List.length_map] using position.isLt⟩

@[simp] theorem source_target (code : source.Rule)
    (position : Fin (source.premises code).length) :
    translation.sourceIndex code (translation.targetIndex code position) = position := by
  apply Fin.ext
  rfl

@[simp] theorem target_source (code : source.Rule)
    (position : Fin (target.premises (translation.rule code)).length) :
    translation.targetIndex code (translation.sourceIndex code position) = position := by
  apply Fin.ext
  rfl

theorem premise (code : source.Rule)
    (position : Fin (target.premises (translation.rule code)).length) :
    (target.premises (translation.rule code)).get position =
      translation.judgment ((source.premises code).get (translation.sourceIndex code position)) := by
  have same := congrArg (fun judgments => judgments[position.val]?) (translation.premises code)
  have bound : position.val < (source.premises code).length :=
    (translation.sourceIndex code position).isLt
  simpa only [List.getElem?_eq_getElem position.isLt, List.getElem?_map,
    List.getElem?_eq_getElem bound,
    Option.map_some, Option.some.injEq, List.get_eq_getElem, sourceIndex] using same

theorem ofFn_sourceIndex {Value : Type v} (code : source.Rule)
    (values : Fin (source.premises code).length → Value) :
    List.ofFn (fun position => values (translation.sourceIndex code position)) = List.ofFn values := by
  have lengths : (target.premises (translation.rule code)).length =
      (source.premises code).length := by rw [translation.premises, List.length_map]
  exact (List.ofFn_congr lengths.symm values).symm

def identity (presentation : Presentation.{u}) : Morphism presentation presentation where
  judgment := id
  rule := id
  conclusion _ := rfl
  premises _ := (List.map_id _).symm

def comp {last : Presentation.{u}} (first : Morphism source target)
    (second : Morphism target last) : Morphism source last where
  judgment := second.judgment ∘ first.judgment
  rule := second.rule ∘ first.rule
  conclusion code := by rw [Function.comp_apply, second.conclusion, first.conclusion]; rfl
  premises code := by rw [Function.comp_apply, second.premises, first.premises, List.map_map]

/-- Interpret original source derivations using the mapped target rules.
This construction is independent of the Boolean certificate checker. -/
def derivationAlgebra : JudgmentDerivation.Algebra source.signature where
  Carrier judgment := target.Derivation (translation.judgment judgment)
  conclude := by
    intro judgment code children
    refine .node ⟨translation.rule code.val,
      (translation.conclusion code.val).trans (congrArg translation.judgment code.property)⟩ ?_
    intro position
    exact Tree.castDerivation (translation.premise code.val position.down).symm
      (children ⟨translation.sourceIndex code.val position.down⟩)

def mapDerivation {judgment : source.Judgment} :
    source.Derivation judgment → target.Derivation (translation.judgment judgment) :=
  JudgmentDerivation.interpret translation.derivationAlgebra

end Morphism
end Presentation

namespace Tree

variable {source target : Presentation.{u}}

/-- Compute the translated proof, retaining each child occurrence exactly once. -/
def map (translation : Presentation.Morphism source target) : Tree source → Tree target
  | .node code children => .node (translation.rule code)
      (fun position => map translation (children (translation.sourceIndex code position)))

/-- A structural count of certificate occurrences, independent of payload
bytes and the work performed by equality checks or rule calculations. -/
def nodeCount {presentation : Presentation.{u}} : Tree presentation → Nat
  | .node _ children => 1 + (List.ofFn fun position => nodeCount (children position)).sum

theorem nodeCount_map (translation : Presentation.Morphism source target) (tree : Tree source) :
    (tree.map translation).nodeCount = tree.nodeCount := by
  induction tree with
  | node code children ih =>
      simp only [map, nodeCount]
      apply congrArg (fun values : List Nat => 1 + values.sum)
      calc
        List.ofFn (fun position => nodeCount (map translation
            (children (translation.sourceIndex code position)))) =
            List.ofFn (fun position => nodeCount (children (translation.sourceIndex code position))) := by
          congr 1
          funext position
          exact ih (translation.sourceIndex code position)
        _ = List.ofFn (fun position => nodeCount (children position)) :=
          translation.ofFn_sourceIndex (Value := Nat) code (fun position => nodeCount (children position))

/-- Mapping rule instances preserves acceptance. This direction does not
require an injective judgment map. -/
theorem check_map [DecidableEq source.Judgment] [DecidableEq target.Judgment]
    (translation : Presentation.Morphism source target)
    (tree : Tree source) (judgment : source.Judgment)
    (accepted : tree.check judgment = true) :
    (tree.map translation).check (translation.judgment judgment) = true := by
  induction tree generalizing judgment with
  | node code children ih =>
      have clauses : source.conclusion code = judgment ∧
          ∀ position, (children position).check ((source.premises code).get position) = true := by
        simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using accepted
      simp only [map, check, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨(translation.conclusion code).trans (congrArg translation.judgment clauses.1), ?_⟩
      intro position
      rw [translation.premise]
      exact ih _ _ (clauses.2 _)

/-- Injectivity reflects acceptance of the translated certificate. This is
reflection on the translated proof image, not conservativity for all target proofs. -/
theorem check_map_iff [DecidableEq source.Judgment] [DecidableEq target.Judgment]
    (translation : Presentation.Morphism source target)
    (injective : Function.Injective translation.judgment)
    (tree : Tree source) (judgment : source.Judgment) :
    (tree.map translation).check (translation.judgment judgment) = true ↔
      tree.check judgment = true := by
  constructor
  · intro accepted
    induction tree generalizing judgment with
    | node code children ih =>
        have clauses : target.conclusion (translation.rule code) = translation.judgment judgment ∧
            ∀ position, ((children (translation.sourceIndex code position)).map translation).check
              ((target.premises (translation.rule code)).get position) = true := by
          simpa only [map, check, Bool.and_eq_true, decide_eq_true_eq] using accepted
        simp only [check, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨injective ((translation.conclusion code).symm.trans clauses.1), ?_⟩
        intro position
        have checked := clauses.2 (translation.targetIndex code position)
        rw [translation.premise, translation.source_target] at checked
        exact ih position _ checked
  · exact check_map translation tree judgment

@[simp] theorem map_identity (presentation : Presentation.{u}) (tree : Tree presentation) :
    tree.map (Presentation.Morphism.identity presentation) = tree := by
  induction tree with
  | node code children ih =>
      change Tree.node code (fun position =>
        map (Presentation.Morphism.identity presentation)
          (children ((Presentation.Morphism.identity presentation).sourceIndex code position))) =
        Tree.node code children
      congr 1
      funext position
      have same : (Presentation.Morphism.identity presentation).sourceIndex code position = position :=
        Fin.ext rfl
      simpa only [same] using ih position

theorem map_comp {last : Presentation.{u}}
    (first : Presentation.Morphism source target) (second : Presentation.Morphism target last)
    (tree : Tree source) :
    (tree.map first).map second = tree.map (first.comp second) := by
  induction tree with
  | node code children ih =>
      change Tree.node (second.rule (first.rule code)) (fun position =>
        map second (map first (children
          (first.sourceIndex code (second.sourceIndex (first.rule code) position))))) =
        Tree.node (second.rule (first.rule code)) (fun position =>
          map (first.comp second) (children ((first.comp second).sourceIndex code position)))
      congr 1
      funext position
      have same : first.sourceIndex code (second.sourceIndex (first.rule code) position) =
          (first.comp second).sourceIndex code position := Fin.ext rfl
      simpa only [same] using ih ((first.comp second).sourceIndex code position)

/-- Translation commutes with erasing the independently generated derivation.
The concrete rule codes and every premise occurrence are retained. -/
theorem erase_mapDerivation (translation : Presentation.Morphism source target)
    {judgment : source.Judgment} (derivation : source.Derivation judgment) :
    erase (translation.mapDerivation derivation) = (erase derivation).map translation := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun judgment derivation =>
      erase (translation.mapDerivation derivation) = (erase derivation).map translation)
    (t := derivation)
  intro judgment code children ih
  rcases code with ⟨code, conclusion⟩
  cases conclusion
  change Tree.node (translation.rule code) (fun position =>
    erase (castDerivation (translation.premise code position).symm
      (translation.mapDerivation (children ⟨translation.sourceIndex code position⟩)))) =
    Tree.node (translation.rule code) (fun position =>
      map translation (erase (children ⟨translation.sourceIndex code position⟩)))
  congr 1
  funext position
  rw [erase_cast]
  exact ih ⟨translation.sourceIndex code position⟩

end Tree

end Mettapedia.OSLF.NativeTypes.Certificates
