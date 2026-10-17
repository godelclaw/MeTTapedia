import Mettapedia.Languages.HOLLight.ImplicationExpansion

/-!
# Original MP graph templates with runtime axiom fields

The direct calculus compiler uses empty hypotheses. Its incoming theorem objects,
operand words, original source representatives, origin, input axiom field and
computed axiom union are physical fields. No incoming dependency basis is fixed
in this descriptor. Physical extraction and union production earn the two axiom
fields before this emitter is run.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.DynamicModusPonensTemplates
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Turing Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Logic.DerivationGraph
open ProofDataEncoding PrimitiveTransport EqualityExpansion EqualityExpansion.Emission
open GraphExpansion ImplicationExpansion ImplicationExpansion.Emission
open PrimitiveSentences (truthDB identityBool)
open DerivedRules (selectSecondDB)
open ExcludedMiddle (boolBinaryTy andDB)

abbrev Plan := Indexed.Template Alphabet 11
abbrev TemplateNode := Node Plan Plan Plan

/-- Runtime original axiom bytes and the original empty hypothesis codec. -/
def dependent (axioms conclusion : Plan) : Plan :=
  Templates.pair axioms (Templates.pair
    (Templates.literal ((finsetCodec canonicalCodec).put ∅)) conclusion)

/-- Original five-node symmetry expansion, with runtime axiom bytes. -/
def symmetryNodes (axioms input left right origin : Plan) : List TemplateNode :=
  let operandType := Ty.bool
  let operator := Templates.literal (putTerm (.const Const.equality (Ty.equality operandType)))
  let operatorCanonical := Templates.canonical (Ty.equality operandType) operator
  let operatorProof := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality (Ty.equality operandType) operator operator))
  let head := dependent axioms
    (Templates.canonical Ty.bool (Templates.equality (.function operandType Ty.bool)
      (Templates.application operator left) (Templates.application operator right)))
  let leftCanonical := Templates.canonical operandType left
  let leftProof := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality operandType left left))
  let full := dependent axioms
    (Templates.canonical Ty.bool (Templates.equality Ty.bool
      (Templates.equality operandType left left) (Templates.equality operandType right left)))
  let reversed := dependent axioms
    (Templates.canonical Ty.bool (Templates.equality operandType right left))
  [⟨operatorProof, unaryRequest 0 operatorCanonical, [], origin⟩,
   ⟨head, binaryRequest 2 operatorProof input, [1, 0], origin⟩,
   ⟨leftProof, unaryRequest 0 leftCanonical, [], origin⟩,
   ⟨full, binaryRequest 2 head leftProof, [2, 3], origin⟩,
   ⟨reversed, binaryRequest 6 full leftProof, [4, 3], origin⟩]

def requests? :
    Option (List (Node (Indexed.Template Alphabet 11)
      (List (Node (Indexed.Template Alphabet 11)
        (Indexed.Template Alphabet 11) (Indexed.Template Alphabet 11)) × Nat)
      (Indexed.Template Alphabet 11))) := do
  let input : Indexed.Template Alphabet 11 := [.inr 0]
  let premise : Indexed.Template Alphabet 11 := [.inr 1]
  let left : Indexed.Template Alphabet 11 := [.inr 2]
  let right : Indexed.Template Alphabet 11 := [.inr 3]
  let leftSource : Indexed.Template Alphabet 11 := [.inr 4]
  let rightSource : Indexed.Template Alphabet 11 := [.inr 5]
  let origin : Indexed.Template Alphabet 11 := [.inr 6]
  let pairLeftSource : Indexed.Template Alphabet 11 := [.inr 7]
  let pairRightSource : Indexed.Template Alphabet 11 := [.inr 8]
  let inputAxioms : Plan := [.inr 9]
  let combinedAxioms : Plan := [.inr 10]
  let boolTerm := Templates.canonical Ty.bool
  let emptyTheorem := Templates.theoremTemplate ∅ ∅
  let inputTheorem := dependent inputAxioms
  let combinedTheorem := dependent combinedAxioms
  let equality := Templates.equality Ty.bool
  let truth := Templates.literal (putTerm truthDB)
  let selector := Templates.literal (putTerm selectSecondDB)
  let andTerm := Templates.application (Templates.application (Templates.literal (putTerm andDB)) left) right
  let pairLeft := Templates.pair (Templates.literal (.atom 4))
    (Templates.pair (Templates.literal (putTy boolBinaryTy))
      (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) left) right))
  let pairTruth := Templates.literal (putTerm (pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl).term)
  let selectedLeft := Templates.application pairLeft selector
  let selectedTruth := Templates.application pairTruth selector
  let andEquation := equality andTerm left
  let pairEquation := Templates.equality (.function boolBinaryTy Ty.bool) pairLeft pairTruth
  let doubleSlots : Fin 5 → Indexed.Template Alphabet 11 := ![left, right, leftSource, rightSource, origin]
  let primitive (count : Nat) (claim request : Indexed.Template Alphabet 11) :=
    EqualityExpansion.Emission.primitiveNodes count claim request origin
  let sym (axioms theoremField left right : Plan) := symmetryNodes axioms theoremField left right origin
  let fixed (block : ProofSystem.Certificate) :=
    EqualityExpansion.Emission.substituteNodes ![origin] (EqualityExpansion.Emission.blockNodes block)
  let implicationNodes := EqualityExpansion.Emission.substituteNodes doubleSlots
    (EqualityExpansion.Emission.doubleBetaNodes Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked)
  let conjunctionNodes := EqualityExpansion.Emission.substituteNodes doubleSlots
    (EqualityExpansion.Emission.doubleBetaNodes Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked)
  let implicationConclusion := (implicationNodes.getLast?).map (·.conclusion)
  let conjunctionConclusion := (conjunctionNodes.getLast?).map (·.conclusion)
  let implicationConclusion ← implicationConclusion
  let conjunctionConclusion ← conjunctionConclusion
  let converted := inputTheorem (boolTerm andEquation)
  let reversedImp := inputTheorem (boolTerm (equality left andTerm))
  let andProof := combinedTheorem (boolTerm andTerm)
  let bodyProof := combinedTheorem (boolTerm pairEquation)
  let selectorCanonical := Templates.canonical boolBinaryTy selector
  let selectorProof := emptyTheorem (boolTerm (Templates.equality boolBinaryTy selector selector))
  let bodyApplication := combinedTheorem (boolTerm (equality selectedLeft selectedTruth))
  let pairNodes := EqualityExpansion.Emission.substituteNodes
    ![left, right, pairLeftSource, pairRightSource, origin] pairNodes
  let selectorNodes := EqualityExpansion.Emission.substituteNodes doubleSlots
    (EqualityExpansion.Emission.doubleBetaNodes Ty.bool Ty.bool Ty.bool (.bound 0) (by simp))
  let leftPairConclusion ← (pairNodes.getLast?).map (·.conclusion)
  let leftSelectorConclusion ← (selectorNodes.getLast?).map (·.conclusion)
  let leftReduction := emptyTheorem (boolTerm (equality selectedLeft right))
  let reversedLeft := emptyTheorem (boolTerm (equality right selectedLeft))
  let truthPair := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthSelector := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthPairNodes := fixed (betaBlock truthPair ("", 0))
  let truthSelectorNodes := fixed (doubleBetaBlock truthSelector ("", 0))
  let truthPairConclusion := Templates.literal (theoremCodec.put truthPair.conclusion)
  let truthSelectorConclusion := Templates.literal (theoremCodec.put truthSelector.conclusion)
  let truthReduction := emptyTheorem (boolTerm (equality selectedTruth truth))
  let joinedLeft := combinedTheorem (boolTerm (equality right selectedTruth))
  let joinedTruth := combinedTheorem (boolTerm (equality right truth))
  let reversedTruth := combinedTheorem (boolTerm (equality truth right))
  let identityCanonical := Templates.literal (canonicalCodec.put
    (⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩ : CanonicalTerm))
  let truthProof := Templates.literal (theoremCodec.put (reflexivity
    (⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩ : CanonicalTerm)))
  let result := combinedTheorem (boolTerm right)
  let request0 ← macroRequest? implicationNodes 6 [] origin
  let request1 ← macroRequest? (primitive 2 converted
    (EqualityExpansion.Emission.binaryRequest 6 implicationConclusion input)) 2 [2, 0] origin
  let request2 ← macroRequest? (sym inputAxioms converted andTerm left) 5 [3] origin
  let request3 ← macroRequest? (primitive 2 andProof
    (EqualityExpansion.Emission.binaryRequest 6 reversedImp premise)) 2 [4, 1] origin
  let request4 ← macroRequest? conjunctionNodes 6 [] origin
  let request5 ← macroRequest? (primitive 2 bodyProof
    (EqualityExpansion.Emission.binaryRequest 6 conjunctionConclusion andProof)) 2 [6, 5] origin
  let request6 ← macroRequest? (primitive 0 selectorProof
    (EqualityExpansion.Emission.unaryRequest 0 selectorCanonical)) 0 [] origin
  let request7 ← macroRequest? (primitive 2 bodyApplication
    (EqualityExpansion.Emission.binaryRequest 2 bodyProof selectorProof)) 2 [7, 8] origin
  let request8 ← macroRequest? pairNodes 1 [] origin
  let request9 ← macroRequest? selectorNodes 6 [] origin
  let request10 ← macroRequest? (primitive 2 leftReduction
    (EqualityExpansion.Emission.binaryRequest 1 leftPairConclusion leftSelectorConclusion)) 2 [10, 11] origin
  let request11 ← macroRequest? (sym (Templates.literal ((finsetCodec sequentCodec).put ∅)) leftReduction selectedLeft right) 5 [12] origin
  let request12 ← macroRequest? truthPairNodes 1 [] origin
  let request13 ← macroRequest? truthSelectorNodes 6 [] origin
  let request14 ← macroRequest? (primitive 2 truthReduction
    (EqualityExpansion.Emission.binaryRequest 1 truthPairConclusion truthSelectorConclusion)) 2 [14, 15] origin
  let request15 ← macroRequest? (primitive 2 joinedLeft
    (EqualityExpansion.Emission.binaryRequest 1 reversedLeft bodyApplication)) 2 [13, 9] origin
  let request16 ← macroRequest? (primitive 2 joinedTruth
    (EqualityExpansion.Emission.binaryRequest 1 joinedLeft truthReduction)) 2 [17, 16] origin
  let request17 ← macroRequest? (sym combinedAxioms joinedTruth right truth) 5 [18] origin
  let request18 ← macroRequest? (primitive 0 truthProof
    (EqualityExpansion.Emission.unaryRequest 0 identityCanonical)) 0 [] origin
  let request19 ← macroRequest? (primitive 2 result
    (EqualityExpansion.Emission.binaryRequest 6 reversedTruth truthProof)) 2 [19, 20] origin
  return [request0, request1, request2, request3, request4, request5, request6, request7, request8, request9,
    request10, request11, request12, request13, request14, request15, request16, request17, request18, request19]



/-- Substitution of the two earned support fields retains the original nine slots. -/
def supportSlots (inputAxioms premiseAxioms : Finset Sequent) : Fin 11 → Indexed.Template Alphabet 9 :=
  fun index => if before : index.val < 9 then [.inr ⟨index.val,before⟩]
    else if index.val = 9 then Templates.literal ((finsetCodec sequentCodec).put inputAxioms)
    else Templates.literal ((finsetCodec sequentCodec).put (inputAxioms ∪ premiseAxioms))

@[simp] theorem substitute_append {m n : Nat} (first second : Indexed.Template Alphabet m)
    (slots : Fin m → Indexed.Template Alphabet n) :
    Templates.substitute (first ++ second) slots =
      Templates.substitute first slots ++ Templates.substitute second slots := by
  simp only [Templates.substitute,List.flatMap_append]

@[simp] theorem substitute_literal {m n : Nat} (data : Data)
    (slots : Fin m → Indexed.Template Alphabet n) :
    Templates.substitute (Templates.literal data) slots = Templates.literal data := by
  simp only [Templates.substitute,Templates.literal,List.flatMap_map]
  generalize encodeData data = word
  induction word with
  | nil => rfl
  | cons symbol rest ih => simpa only [List.flatMap_cons,List.map_cons,List.singleton_append] using congrArg (List.cons (.inl symbol)) ih

@[simp] theorem substitute_hole {m n : Nat} (index : Fin m)
    (slots : Fin m → Indexed.Template Alphabet n) :
    Templates.substitute [.inr index] slots = slots index := by
  simp [Templates.substitute]

@[simp] theorem substitute_pair {m n : Nat} (first second : Indexed.Template Alphabet m)
    (slots : Fin m → Indexed.Template Alphabet n) :
    Templates.substitute (Templates.pair first second) slots =
      Templates.pair (Templates.substitute first slots) (Templates.substitute second slots) := by
  simp [Templates.pair,Templates.substitute]

@[simp] theorem substitute_nested {l m n : Nat} (plan : Indexed.Template Alphabet l)
    (first : Fin l → Indexed.Template Alphabet m) (second : Fin m → Indexed.Template Alphabet n) :
    Templates.substitute (Templates.substitute plan first) second =
      Templates.substitute plan (fun index => Templates.substitute (first index) second) := by
  induction plan with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp only [Templates.substitute,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.flatMap_append] at * <;> simp_all

@[simp] theorem substituteNodes_nested {l m n : Nat}
    (first : Fin l → Indexed.Template Alphabet m) (second : Fin m → Indexed.Template Alphabet n)
    (nodes : List (Node (Indexed.Template Alphabet l) (Indexed.Template Alphabet l)
      (Indexed.Template Alphabet l))) :
    (substituteNodes first nodes).map
      (Node.map (fun plan => Templates.substitute plan second)
        (fun plan => Templates.substitute plan second) (fun plan => Templates.substitute plan second)) =
    substituteNodes (fun index => Templates.substitute (first index) second) nodes := by
  simp [substituteNodes,List.map_map,Node.map]

@[simp] theorem symmetry_specialize (inputAxioms premiseAxioms : Finset Sequent)
    (axioms : Finset Sequent) (support input left right origin : Plan)
    (exactSupport : Templates.substitute support (supportSlots inputAxioms premiseAxioms) =
      Templates.literal ((finsetCodec sequentCodec).put axioms)) :
    (symmetryNodes support input left right origin).map
      (Node.map (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))
        (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))
        (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))) =
    substituteNodes
      ![Templates.substitute input (supportSlots inputAxioms premiseAxioms),
        Templates.substitute left (supportSlots inputAxioms premiseAxioms),
        Templates.substitute right (supportSlots inputAxioms premiseAxioms),
        Templates.substitute origin (supportSlots inputAxioms premiseAxioms)]
      (EqualityExpansion.Emission.symmetryNodes axioms ∅ Ty.bool) := by
  simp [symmetryNodes,EqualityExpansion.Emission.symmetryNodes,dependent,
    Templates.theoremTemplate,Templates.canonical,Templates.equality,Templates.application,
    unaryRequest,binaryRequest,substituteNodes,Node.map,exactSupport]


def specializeNode (inputAxioms premiseAxioms : Finset Sequent) : TemplateNode →
    Node (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9) :=
  Node.map (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))
    (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))
    (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))

def specializeRequest (inputAxioms premiseAxioms : Finset Sequent) :=
  Node.map (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))
    (fun block : List TemplateNode × Nat =>
      (block.1.map (specializeNode inputAxioms premiseAxioms),block.2))
    (fun plan => Templates.substitute plan (supportSlots inputAxioms premiseAxioms))

@[simp] theorem support_small (a b : Finset Sequent) (index : Fin 11) (small : index.val < 9) :
    supportSlots a b index = [.inr ⟨index.val,small⟩] := by simp [supportSlots,small]
@[simp] theorem support_input (a b : Finset Sequent) :
    supportSlots a b 9 = Templates.literal ((finsetCodec sequentCodec).put a) := by simp [supportSlots]
@[simp] theorem support_union (a b : Finset Sequent) :
    supportSlots a b 10 = Templates.literal ((finsetCodec sequentCodec).put (a ∪ b)) := by simp [supportSlots]

theorem support_double (a b : Finset Sequent) :
    (fun index : Fin 5 => Templates.substitute
      (![[.inr 2],[.inr 3],[.inr 4],[.inr 5],[.inr 6]] index : Plan) (supportSlots a b)) =
    (![[.inr 2],[.inr 3],[.inr 4],[.inr 5],[.inr 6]] : Fin 5 → Indexed.Template Alphabet 9) := by
  funext index; fin_cases index <;> simp
theorem support_pair (a b : Finset Sequent) :
    (fun index : Fin 5 => Templates.substitute
      (![[.inr 2],[.inr 3],[.inr 7],[.inr 8],[.inr 6]] index : Plan) (supportSlots a b)) =
    (![[.inr 2],[.inr 3],[.inr 7],[.inr 8],[.inr 6]] : Fin 5 → Indexed.Template Alphabet 9) := by
  funext index; fin_cases index <;> simp
theorem support_origin (a b : Finset Sequent) :
    (fun index : Fin 1 => Templates.substitute (![ [.inr 6] ] index : Plan) (supportSlots a b)) =
    (![ [.inr 6] ] : Fin 1 → Indexed.Template Alphabet 9) := by
  funext index; fin_cases index; simp

/-- The dynamic descriptor specializes to the existing original twenty-macro plan. -/
theorem requests_specialize (inputAxioms premiseAxioms : Finset Sequent) :
    requests?.map (List.map (specializeRequest inputAxioms premiseAxioms)) =
      mpRequests? inputAxioms premiseAxioms ∅ ∅ := by
  simp [requests?,mpRequests?,specializeRequest,specializeNode,
    symmetryNodes,EqualityExpansion.Emission.symmetryNodes,dependent,
    support_double,macroRequest?,substituteNodes,primitiveNodes,doubleBetaNodes,pairNodes,blockNodes,
    betaBlock,doubleBetaBlock,
    Node.map,Templates.theoremTemplate,
    Templates.canonical,Templates.application,Templates.equality,Templates.sourceApplication,
    Templates.sourceAbstraction,
    unaryRequest,binaryRequest]


/-- The original chronological assembler retains the two external theorem roots. -/
def assembled? : Option (List TemplateNode × Nat) := do
  let requests ← requests?
  let (nodes,roots) ← expandFrom [] #[0,1] requests 2
  let root ← roots[21]?
  pure (nodes,root)

def originalAssembly? (a b : Finset Sequent) : Option
    (List (Node (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9)
      (Indexed.Template Alphabet 9)) × Nat) := do
  let requests ← mpRequests? a b ∅ ∅
  let (nodes,roots) ← expandFrom [] #[0,1] requests 2
  let root ← roots[21]?
  pure (nodes,root)

/-- Every claim, primitive request, origin, parent occurrence and root transports. -/
theorem assembled_specialize (a b : Finset Sequent) :
    assembled?.map (fun block => (block.1.map (specializeNode a b),block.2)) = originalAssembly? a b := by
  have source := requests_specialize a b
  cases formed : requests? with
  | none =>
      simp only [formed,Option.map_none] at source
      simp [assembled?,originalAssembly?,formed,← source]
  | some requests =>
      simp only [formed,Option.map_some] at source
      unfold assembled? originalAssembly?
      rw [formed,← source]
      simp only [Bind.bind,Option.bind_some]
      exact (expandFrom_selected_bind_map
        (fun plan => Templates.substitute plan (supportSlots a b))
        (fun plan => Templates.substitute plan (supportSlots a b))
        (fun plan => Templates.substitute plan (supportSlots a b))
        #[0,1] requests 21 2).symm

theorem originalAssembly_isSome (a b : Finset Sequent) : (originalAssembly? a b).isSome = true := by
  have total := mpTemplate_isSome a b ∅ ∅
  have fact : mpTemplate? a b ∅ ∅ = (originalAssembly? a b).map certificateTemplate := by
    unfold mpTemplate? originalAssembly?
    cases mpRequests? a b ∅ ∅ with
    | none => rfl
    | some requests =>
      simp only [Bind.bind,Option.bind_some]
      cases expandFrom [] #[0,1] requests 2 with
      | none => rfl
      | some result => cases selected : result.2[21]? <;> simp [selected]
  rw [fact,Option.isSome_map] at total
  exact total

theorem assembled_isSome : assembled?.isSome = true := by
  have source := congrArg Option.isSome (assembled_specialize ∅ ∅)
  rw [Option.isSome_map,originalAssembly_isSome] at source
  exact source

def assembled : List TemplateNode × Nat := assembled?.get (by rw [assembled_isSome])
theorem assembled_computed : assembled? = some assembled := (Option.some_get _).symm

def template : Plan := certificateTemplate assembled

theorem assembled_fields (a b : Finset Sequent) :
    originalAssembly? a b = some (assembled.1.map (specializeNode a b),assembled.2) := by
  rw [← assembled_specialize,assembled_computed,Option.map_some]

theorem certificateTemplate_substitute {m n : Nat}
    (nodes : List (Node (Indexed.Template Alphabet m) (Indexed.Template Alphabet m)
      (Indexed.Template Alphabet m))) (root : Nat) (slots : Fin m → Indexed.Template Alphabet n) :
    Templates.substitute (certificateTemplate (nodes,root)) slots = certificateTemplate
      (nodes.map (Node.map (fun plan => Templates.substitute plan slots)
        (fun plan => Templates.substitute plan slots) (fun plan => Templates.substitute plan slots)),root) := by
  have listSame (plans : List (Indexed.Template Alphabet m)) :
      Templates.substitute (listTemplate plans) slots =
        listTemplate (plans.map (fun plan => Templates.substitute plan slots)) := by
    induction plans with
    | nil => simp [listTemplate]
    | cons plan rest ih => simp only [listTemplate,substitute_pair,ih,List.map_cons]
  simp only [certificateTemplate,substitute_pair,listSame,substitute_literal,List.map_map]
  congr 2
  apply List.map_congr_left
  intro node _
  simp [nodeTemplate,receiptTemplate,Node.map]


/-- The emitted graph descriptor is the existing original MP descriptor after support specialization. -/
theorem template_specialize (a b : Finset Sequent) :
    Templates.substitute template (supportSlots a b) = mpTemplate a b ∅ ∅ := by
  have original : mpTemplate? a b ∅ ∅ = some (certificateTemplate
      (assembled.1.map (specializeNode a b),assembled.2)) := by
    have compiled := assembled_fields a b
    unfold originalAssembly? at compiled
    unfold mpTemplate?
    cases formed : mpRequests? a b ∅ ∅ with
    | none => simp [formed] at compiled
    | some requests =>
      simp only [formed,Bind.bind,Option.bind_some] at compiled ⊢
      cases expanded : expandFrom [] #[0,1] requests 2 with
      | none => simp [expanded] at compiled
      | some result =>
        cases selected : result.2[21]? with
        | none => simp [expanded,selected] at compiled
        | some root =>
          simp only [expanded,selected,Option.bind_some] at compiled ⊢
          change some (result.1,root) = some _ at compiled
          exact congrArg (fun block => some (certificateTemplate block)) (Option.some.inj compiled)
  have same := Option.some.inj ((mpTemplate_computed a b ∅ ∅).symm.trans original)
  rw [same]
  exact certificateTemplate_substitute assembled.1 assembled.2 (supportSlots a b)


/-- Coherent readout after physical extraction and original axiom union production. -/
def fields (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) : Fin 11 → List Alphabet :=
  ![encodeWith theoremCodec input,encodeWith theoremCodec premise,
    encodeWith dbTermCodec left.term,encodeWith dbTermCodec right.term,
    encodeWith sourceTermCodec (checkedSource left).source,encodeWith sourceTermCodec (checkedSource right).source,
    encodeWith originCodec origin,encodeWith sourceTermCodec pairLeftSource,encodeWith sourceTermCodec pairRightSource,
    encodeWith (finsetCodec sequentCodec) input.axioms,
    encodeWith (finsetCodec sequentCodec) (input.axioms ∪ premise.axioms)]

def inputWire (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (fields input premise left right pairLeftSource pairRightSource origin)

theorem fields_aligned (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) :
    (fun index => Indexed.instantiate (supportSlots input.axioms premise.axioms index)
      (mpFields input premise left right pairLeftSource pairRightSource origin)) =
    fields input premise left right pairLeftSource pairRightSource origin := by
  funext index; fin_cases index <;> simp [supportSlots,fields,mpFields,encodeWith]

/-- Complete byte equality to the existing original MP graph on empty-hypothesis theorem objects. -/
theorem template_exact (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (inputHyp : input.sequent.hyp = ∅) (premiseHyp : premise.sequent.hyp = ∅)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (block : ProofSystem.Certificate)
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    Indexed.instantiate template (fields input premise left right pairLeftSource pairRightSource origin) =
      encodeCertificate block := by
  rw [← fields_aligned,← Templates.substitute_exact,template_specialize]
  have original := mpTemplate_exact input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin policy shape matching block computed
  simpa only [inputHyp,premiseHyp] using original

/-- No output block or semantic callback is supplied: the original MP checker constructs the reference. -/
theorem emitted_original (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (inputHyp : input.sequent.hyp = ∅) (premiseHyp : premise.sequent.hyp = ∅)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) :
    ∃ block, mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block ∧
      BlockChecked policy [input,premise] (mpResult input premise right) block ∧
      block.1.length = 58 ∧
      block.1.map (·.origin) = List.replicate 58 origin ∧
      Indexed.instantiate template (fields input premise left right pairLeftSource pairRightSource origin) =
        encodeCertificate block ∧
      decodeCertificate (Indexed.instantiate template
        (fields input premise left right pairLeftSource pairRightSource origin)) = some block := by
  obtain ⟨block,computed,checked⟩ := mpTypedBlock?_checked policy input premise left right leftBool rightBool shape matching origin
  have emitted := template_exact input premise left right leftBool rightBool inputHyp premiseHyp leftEmpty rightEmpty
    leftNamed pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin policy shape matching block computed
  exact ⟨block,computed,checked,mpTypedBlock?_size policy input premise left right leftBool rightBool shape matching origin computed,
    mpTypedBlock?_origins policy input premise left right leftBool rightBool shape matching origin computed,emitted,
    by rw [emitted,decodeCertificate_encodeCertificate]⟩

/-- Unconditional physical execution on framed bytes; support production is a separate preceding stage. -/
def outputsWire (word : List (Option Alphabet)) :
    TM2OutputsInTime (Indexed.machine template) word (some (Indexed.instantiateWire template word))
      (4*(template.length+1)*(word.length+1)) := Indexed.outputsWire template word

end Mettapedia.Languages.HOLLight.DynamicModusPonensTemplates
