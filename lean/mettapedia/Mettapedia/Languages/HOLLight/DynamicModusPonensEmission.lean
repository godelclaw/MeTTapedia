import Mettapedia.Languages.HOLLight.DynamicModusPonensTemplates
import Mettapedia.Languages.HOLLight.AuthoredAxiomUnion
import Mettapedia.Computability.FramedFieldSelection
import Mettapedia.Computability.RetainedWordExecution

/-!
# Original MP primitive fields from changing theorem objects

The runtime packet contains the two original incoming theorem objects, raw and
named operands and original origin. Physical product projection earns each
incoming axiom field. The authored-basis union machine earns the combined
provenance. These fields are retained and routed into the complete original
58-node descriptor. No output theorem, block or correctness callback is supplied.
The direct calculus compiler's empty-hypothesis invariant is retained; source
claim admission and chronological external-root authorization remain upstream.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.DynamicModusPonensEmission
open Turing StateTransition Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open ProofDataEncoding GraphExpansion PrimitiveTransport ImplicationExpansion ImplicationExpansion.Emission

abbrev projection := CertificateDataTraversal.ProductField.machine false
local instance : Fintype (projection.Γ projection.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (projection.Γ projection.k₁) := inferInstanceAs (Inhabited Alphabet)
def axiomMachine := StackMachineComposition.machine projection SourceQuantifierEmission.stripStatus (Equiv.refl Alphabet)
local instance : Fintype (axiomMachine.Γ axiomMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (axiomMachine.Γ axiomMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

def theoremWord (input : Theorem) : List Alphabet := encodeWith theoremCodec input

theorem axiom_length (input : Theorem) : (AuthoredAxiomUnion.source input.axioms).length ≤ (theoremWord input).length :=
  CertificateDataTraversal.ProductField.selected_length_le false
    ((finsetCodec sequentCodec).put input.axioms) (sequentCodec.put input.sequent)

/-- The complete original theorem is read; its actual axiom field is returned. -/
noncomputable def axiomOutputs (input : Theorem) :
    TM2OutputsInTime axiomMachine (theoremWord input) (some (AuthoredAxiomUnion.source input.axioms))
      (12*((theoremWord input).length+1)) := by
  have selected := (CertificateDataTraversal.ProductField.selectFirstCodec (finsetCodec sequentCodec) sequentCodec).outputsFun
    (input.axioms,input.sequent)
  dsimp only [CertificateDataTraversal.ProductField.selectFirstCodec,CertificateDataTraversal.ProductField.computable,
    CertificateDataTraversal.ProductField.successEncoding] at selected
  simp only [eval_add,eval_mul,eval_C,eval_X] at selected
  change TM2OutputsInTime projection ((theoremWord input).map id)
    (some (((1 : Alphabet)::AuthoredAxiomUnion.source input.axioms).map id)) (4*(theoremWord input).length+3) at selected
  simp only [List.map_id] at selected
  have identity := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) (AuthoredAxiomUnion.source input.axioms)
  simp only [List.flatMap_singleton'] at identity
  have stripped := StackMachineComposition.Dispatch.outputs_success SourceQuantifierEmission.rawIdentity
    AdmittedArgumentRendering.accept [] (1 : Alphabet) (AuthoredAxiomUnion.source input.axioms)
    (AuthoredAxiomUnion.source input.axioms) _ (by decide) identity
  have joined := StackMachineComposition.outputs projection SourceQuantifierEmission.stripStatus (Equiv.refl Alphabet)
    (theoremWord input) ((1 : Alphabet)::AuthoredAxiomUnion.source input.axioms)
    (AuthoredAxiomUnion.source input.axioms) _ _ selected (by
      change TM2OutputsInTime SourceQuantifierEmission.stripStatus
        (((1 : Alphabet)::AuthoredAxiomUnion.source input.axioms).map id) _ _
      simpa only [List.map_id,SourceQuantifierEmission.stripStatus] using stripped)
  apply WordEqualityMachine.within joined
  have bounded := axiom_length input
  simp only [List.length_cons]
  omega

variable {arity : Nat}
def extendFields (fields : Fin arity → List Alphabet) (last : List Alphabet) : Fin (arity+1) → List Alphabet :=
  fun index => if inside : index.val < arity then fields ⟨index.val,inside⟩ else last

theorem extend_frame (fields : Fin arity → List Alphabet) (last : List Alphabet) :
    Indexed.argumentWire (extendFields fields last) = Indexed.argumentWire fields ++ last.map some ++ [none] := by
  simp [Indexed.argumentWire,extendFields,List.finRange_succ_last,Indexed.frame,List.append_assoc,Function.comp_def]

def selector (index : Fin arity) : Indexed.Template Alphabet arity := [.inr index]
local instance (index : Fin arity) : Fintype ((Indexed.machine (selector index)).Γ (Indexed.machine (selector index)).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance (index : Fin arity) : Inhabited ((Indexed.machine (selector index)).Γ (Indexed.machine (selector index)).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def selectedAxiomMachine (index : Fin arity) := StackMachineComposition.machine (Indexed.machine (selector index))
  axiomMachine (Equiv.refl Alphabet)
local instance (index : Fin arity) : Fintype ((selectedAxiomMachine index).Γ (selectedAxiomMachine index).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance (index : Fin arity) : Inhabited ((selectedAxiomMachine index).Γ (selectedAxiomMachine index).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
local instance (index : Fin arity) : Inhabited ((selectedAxiomMachine index).Γ (selectedAxiomMachine index).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def retainedAxiomMachine (index : Fin arity) := RetainedWordExecution.WithOutput.Framed.machine (selectedAxiomMachine index)
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

def selectedAxiomClock (fields : Fin arity → List Alphabet) (index : Fin arity) : Nat :=
  8*(Indexed.argumentWire fields).length+14*(fields index).length+22

noncomputable def selectedAxiomOutputs (fields : Fin arity → List Alphabet) (index : Fin arity) (input : Theorem)
    (same : fields index = theoremWord input) :
    TM2OutputsInTime (selectedAxiomMachine index) (Indexed.argumentWire fields)
      (some (AuthoredAxiomUnion.source input.axioms)) (selectedAxiomClock fields index) := by
  have selected := Indexed.outputs (selector index) fields
  simp only [selector,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,same] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine (selector index)) axiomMachine (Equiv.refl Alphabet)
    (Indexed.argumentWire fields) (theoremWord input) (AuthoredAxiomUnion.source input.axioms) _ _ selected (by
      change TM2OutputsInTime axiomMachine ((theoremWord input).map id) _ _
      simpa only [List.map_id] using axiomOutputs input)
  apply WordEqualityMachine.within joined
  simp only [selector,List.length_cons,List.length_nil,selectedAxiomClock,same]
  omega

def retainedAxiomClock (fields : Fin arity → List Alphabet) (index : Fin arity) (input : Theorem) : Nat :=
  selectedAxiomClock fields index + 23*(Indexed.argumentWire fields).length +
    22*(AuthoredAxiomUnion.source input.axioms).length+23

noncomputable def retainedAxiomOutputs (fields : Fin arity → List Alphabet) (index : Fin arity) (input : Theorem)
    (same : fields index = theoremWord input) :
    TM2OutputsInTime (retainedAxiomMachine index) (Indexed.argumentWire fields)
      (some (Indexed.argumentWire (extendFields fields (AuthoredAxiomUnion.source input.axioms))))
      (retainedAxiomClock fields index input) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs (selectedAxiomMachine index)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire fields)
    (AuthoredAxiomUnion.source input.axioms) _ (selectedAxiomOutputs fields index input same)
  have outputSame : RetainedWordExecution.WithOutput.Framed.outputWord (selectedAxiomMachine index)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire fields)
      (AuthoredAxiomUnion.source input.axioms) = Indexed.argumentWire (extendFields fields (AuthoredAxiomUnion.source input.axioms)) := by
    change (Indexed.argumentWire fields).map id ++ (AuthoredAxiomUnion.source input.axioms).map some ++ [none] = _
    rw [List.map_id,extend_frame]
  rw [outputSame] at retained
  exact retained


local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((AuthoredAxiomUnion.machine basis).Γ
    (AuthoredAxiomUnion.machine basis).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((AuthoredAxiomUnion.machine basis).Γ
    (AuthoredAxiomUnion.machine basis).k₁) := inferInstanceAs (Inhabited Alphabet)

def unionStrip := StackMachineComposition.Dispatch.machine SourceQuantifierEmission.rawIdentity
  AdmittedArgumentRendering.accept [(0 : Alphabet)]
local instance : Fintype (unionStrip.Γ unionStrip.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (unionStrip.Γ unionStrip.k₁) := inferInstanceAs (Inhabited Alphabet)
def unionBody (basis : AuthoredAxiomUnion.Basis) := StackMachineComposition.machine (AuthoredAxiomUnion.machine basis)
  unionStrip (Equiv.refl Alphabet)
local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((unionBody basis).Γ (unionBody basis).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((unionBody basis).Γ (unionBody basis).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def selectedUnionMachine (basis : AuthoredAxiomUnion.Basis) := StackMachineComposition.machine
  (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))) (unionBody basis) (Equiv.refl (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((selectedUnionMachine basis).Γ (selectedUnionMachine basis).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((selectedUnionMachine basis).Γ (selectedUnionMachine basis).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((selectedUnionMachine basis).Γ (selectedUnionMachine basis).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def retainedUnionMachine (basis : AuthoredAxiomUnion.Basis) :=
  RetainedWordExecution.WithOutput.Framed.machine (selectedUnionMachine basis)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

def unionBodyClock (basis left right : AuthoredAxiomUnion.Basis)
    (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) : Nat :=
  AuthoredAxiomUnion.clock basis left right leftWithin rightWithin +
    6*(AuthoredAxiomUnion.source (left∪right)).length+7

noncomputable def unionBodyOutputs (basis left right : AuthoredAxiomUnion.Basis)
    (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) :
    TM2OutputsInTime (unionBody basis) (Indexed.frame [AuthoredAxiomUnion.source left,AuthoredAxiomUnion.source right])
      (some (AuthoredAxiomUnion.source (left∪right))) (unionBodyClock basis left right leftWithin rightWithin) := by
  have produced := AuthoredAxiomUnion.outputs basis left right leftWithin rightWithin
  have identity := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) (AuthoredAxiomUnion.source (left∪right))
  simp only [List.flatMap_singleton'] at identity
  have stripped := StackMachineComposition.Dispatch.outputs_success SourceQuantifierEmission.rawIdentity
    AdmittedArgumentRendering.accept [(0 : Alphabet)] (1 : Alphabet)
    (AuthoredAxiomUnion.source (left∪right)) (AuthoredAxiomUnion.source (left∪right)) _ (by decide) identity
  have joined := StackMachineComposition.outputs (AuthoredAxiomUnion.machine basis) unionStrip (Equiv.refl Alphabet)
    (Indexed.frame [AuthoredAxiomUnion.source left,AuthoredAxiomUnion.source right])
    ((1 : Alphabet)::AuthoredAxiomUnion.source (left∪right)) (AuthoredAxiomUnion.source (left∪right)) _ _ produced (by
      change TM2OutputsInTime unionStrip (((1 : Alphabet)::AuthoredAxiomUnion.source (left∪right)).map id) _ _
      simpa only [List.map_id,unionStrip] using stripped)
  apply WordEqualityMachine.within joined
  simp only [unionBodyClock,List.length_cons]
  omega

def selectedUnionClock (fields : Fin 11 → List Alphabet) (basis left right : AuthoredAxiomUnion.Basis)
    (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) : Nat :=
  28*(Indexed.argumentWire fields).length+28 +
    2*(Indexed.frame [AuthoredAxiomUnion.source left,AuthoredAxiomUnion.source right]).length+2 +
    unionBodyClock basis left right leftWithin rightWithin

noncomputable def selectedUnionOutputs (fields : Fin 11 → List Alphabet) (basis left right : AuthoredAxiomUnion.Basis)
    (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis)
    (leftSame : fields 9 = AuthoredAxiomUnion.source left) (rightSame : fields 10 = AuthoredAxiomUnion.source right) :
    TM2OutputsInTime (selectedUnionMachine basis) (Indexed.argumentWire fields)
      (some (AuthoredAxiomUnion.source (left∪right))) (selectedUnionClock fields basis left right leftWithin rightWithin) := by
  have selected := FramedFieldSelection.outputs (Γ := Alphabet) ([9,10] : List (Fin 11)) fields
  simp only [List.map_cons,List.map_nil,leftSame,rightSame,List.length_cons,List.length_nil] at selected
  have joined := StackMachineComposition.outputs (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))) (unionBody basis)
    (Equiv.refl (Option Alphabet)) (Indexed.argumentWire fields)
    (Indexed.frame [AuthoredAxiomUnion.source left,AuthoredAxiomUnion.source right])
    (AuthoredAxiomUnion.source (left∪right)) _ _ selected (by
      change TM2OutputsInTime (unionBody basis)
        ((Indexed.frame [AuthoredAxiomUnion.source left,AuthoredAxiomUnion.source right]).map id) _ _
      simpa only [List.map_id] using unionBodyOutputs basis left right leftWithin rightWithin)
  apply WordEqualityMachine.within joined
  simp only [selectedUnionClock]
  omega

def retainedUnionClock (fields : Fin 11 → List Alphabet) (basis left right : AuthoredAxiomUnion.Basis)
    (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) : Nat :=
  selectedUnionClock fields basis left right leftWithin rightWithin + 23*(Indexed.argumentWire fields).length +
    22*(AuthoredAxiomUnion.source (left∪right)).length+23

noncomputable def retainedUnionOutputs (fields : Fin 11 → List Alphabet) (basis left right : AuthoredAxiomUnion.Basis)
    (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis)
    (leftSame : fields 9 = AuthoredAxiomUnion.source left) (rightSame : fields 10 = AuthoredAxiomUnion.source right) :
    TM2OutputsInTime (retainedUnionMachine basis) (Indexed.argumentWire fields)
      (some (Indexed.argumentWire (extendFields fields (AuthoredAxiomUnion.source (left∪right)))))
      (retainedUnionClock fields basis left right leftWithin rightWithin) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs (selectedUnionMachine basis)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire fields)
    (AuthoredAxiomUnion.source (left∪right)) _ (selectedUnionOutputs fields basis left right leftWithin rightWithin leftSame rightSame)
  have outputSame : RetainedWordExecution.WithOutput.Framed.outputWord (selectedUnionMachine basis)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire fields)
      (AuthoredAxiomUnion.source (left∪right)) = Indexed.argumentWire (extendFields fields (AuthoredAxiomUnion.source (left∪right))) := by
    change (Indexed.argumentWire fields).map id ++ (AuthoredAxiomUnion.source (left∪right)).map some ++ [none] = _
    rw [List.map_id,extend_frame]
  rw [outputSame] at retained
  exact retained


def firstFields (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) : Fin 10 → List Alphabet :=
  extendFields (mpFields input premise left right pairLeftSource pairRightSource origin) (AuthoredAxiomUnion.source input.axioms)
def secondFields (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) : Fin 11 → List Alphabet :=
  extendFields (firstFields input premise left right pairLeftSource pairRightSource origin) (AuthoredAxiomUnion.source premise.axioms)
def thirdFields (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) : Fin 12 → List Alphabet :=
  extendFields (secondFields input premise left right pairLeftSource pairRightSource origin) (AuthoredAxiomUnion.source (input.axioms∪premise.axioms))

def routing : List (Fin 12) := [0,1,2,3,4,5,6,7,8,9,11]

theorem routing_exact (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) :
    Indexed.frame (routing.map (thirdFields input premise left right pairLeftSource pairRightSource origin)) =
      DynamicModusPonensTemplates.inputWire input premise left right pairLeftSource pairRightSource origin := by
  simp [routing,thirdFields,secondFields,firstFields,extendFields,
    mpFields,DynamicModusPonensTemplates.inputWire,DynamicModusPonensTemplates.fields,
    Indexed.argumentWire,List.finRange_succ,Indexed.frame,AuthoredAxiomUnion.source]

local instance (index : Fin arity) : Fintype ((retainedAxiomMachine index).Γ (retainedAxiomMachine index).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (index : Fin arity) : Inhabited ((retainedAxiomMachine index).Γ (retainedAxiomMachine index).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((retainedUnionMachine basis).Γ (retainedUnionMachine basis).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((retainedUnionMachine basis).Γ (retainedUnionMachine basis).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def theoremFieldsMachine := StackMachineComposition.machine (retainedAxiomMachine (0 : Fin 9))
  (retainedAxiomMachine (1 : Fin 10)) (Equiv.refl (Option Alphabet))
local instance : Fintype (theoremFieldsMachine.Γ theoremFieldsMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (theoremFieldsMachine.Γ theoremFieldsMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def supportsMachine (basis : AuthoredAxiomUnion.Basis) := StackMachineComposition.machine theoremFieldsMachine
  (retainedUnionMachine basis) (Equiv.refl (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((supportsMachine basis).Γ (supportsMachine basis).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((supportsMachine basis).Γ (supportsMachine basis).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def routedMachine (basis : AuthoredAxiomUnion.Basis) := StackMachineComposition.machine (supportsMachine basis)
  (FramedFieldSelection.machine (Γ := Alphabet) routing) (Equiv.refl (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((routedMachine basis).Γ (routedMachine basis).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((routedMachine basis).Γ (routedMachine basis).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def machine (basis : AuthoredAxiomUnion.Basis) := StackMachineComposition.machine (routedMachine basis)
  (Indexed.machine DynamicModusPonensTemplates.template) (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] theoremFieldsMachine supportsMachine routedMachine machine

def theoremFieldsClock (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) : Nat :=
  let original := mpFields input premise left right pairLeftSource pairRightSource origin
  let first := firstFields input premise left right pairLeftSource pairRightSource origin
  retainedAxiomClock original 0 input + 2*(Indexed.argumentWire first).length+2 + retainedAxiomClock first 1 premise

def supportsClock (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis) : Nat :=
  let second := secondFields input premise left right pairLeftSource pairRightSource origin
  theoremFieldsClock input premise left right pairLeftSource pairRightSource origin + 2*(Indexed.argumentWire second).length+2 +
    retainedUnionClock second basis input.axioms premise.axioms inputWithin premiseWithin

def routedClock (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis) : Nat :=
  let third := thirdFields input premise left right pairLeftSource pairRightSource origin
  supportsClock basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin +
    102*(Indexed.argumentWire third).length+102

def clock (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis) : Nat :=
  let final := DynamicModusPonensTemplates.inputWire input premise left right pairLeftSource pairRightSource origin
  routedClock basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin + 2*final.length+2 +
    4*(DynamicModusPonensTemplates.template.length+1)*(final.length+1)

noncomputable def theoremFieldsOutputs (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) :
    TM2OutputsInTime theoremFieldsMachine (mpInput input premise left right pairLeftSource pairRightSource origin)
      (some (Indexed.argumentWire (secondFields input premise left right pairLeftSource pairRightSource origin)))
      (theoremFieldsClock input premise left right pairLeftSource pairRightSource origin) := by
  have first := retainedAxiomOutputs (mpFields input premise left right pairLeftSource pairRightSource origin) 0 input rfl
  have second := retainedAxiomOutputs (firstFields input premise left right pairLeftSource pairRightSource origin) 1 premise
    (by simp [firstFields,extendFields,mpFields,theoremWord])
  have joined := StackMachineComposition.outputs (retainedAxiomMachine (0 : Fin 9)) (retainedAxiomMachine (1 : Fin 10))
    (Equiv.refl (Option Alphabet)) (mpInput input premise left right pairLeftSource pairRightSource origin)
    (Indexed.argumentWire (firstFields input premise left right pairLeftSource pairRightSource origin))
    (Indexed.argumentWire (secondFields input premise left right pairLeftSource pairRightSource origin)) _ _ first (by
      change TM2OutputsInTime (retainedAxiomMachine (1 : Fin 10))
        ((Indexed.argumentWire (firstFields input premise left right pairLeftSource pairRightSource origin)).map id) _ _
      simpa only [List.map_id,secondFields] using second)
  exact joined

noncomputable def supportsOutputs (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis) :
    TM2OutputsInTime (supportsMachine basis) (mpInput input premise left right pairLeftSource pairRightSource origin)
      (some (Indexed.argumentWire (thirdFields input premise left right pairLeftSource pairRightSource origin)))
      (supportsClock basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin) := by
  have union := retainedUnionOutputs (secondFields input premise left right pairLeftSource pairRightSource origin)
    basis input.axioms premise.axioms inputWithin premiseWithin
    (by simp [secondFields,firstFields,extendFields])
    (by simp [secondFields,extendFields])
  have joined := StackMachineComposition.outputs theoremFieldsMachine (retainedUnionMachine basis) (Equiv.refl (Option Alphabet))
    (mpInput input premise left right pairLeftSource pairRightSource origin)
    (Indexed.argumentWire (secondFields input premise left right pairLeftSource pairRightSource origin))
    (Indexed.argumentWire (thirdFields input premise left right pairLeftSource pairRightSource origin)) _ _
    (theoremFieldsOutputs input premise left right pairLeftSource pairRightSource origin) (by
      change TM2OutputsInTime (retainedUnionMachine basis)
        ((Indexed.argumentWire (secondFields input premise left right pairLeftSource pairRightSource origin)).map id) _ _
      simpa only [List.map_id,thirdFields] using union)
  exact joined

noncomputable def routedOutputs (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis) :
    TM2OutputsInTime (routedMachine basis) (mpInput input premise left right pairLeftSource pairRightSource origin)
      (some (DynamicModusPonensTemplates.inputWire input premise left right pairLeftSource pairRightSource origin))
      (routedClock basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin) := by
  have selected := FramedFieldSelection.outputs (Γ := Alphabet) routing
    (thirdFields input premise left right pairLeftSource pairRightSource origin)
  rw [routing_exact] at selected
  have joined := StackMachineComposition.outputs (supportsMachine basis) (FramedFieldSelection.machine (Γ := Alphabet) routing)
    (Equiv.refl (Option Alphabet)) (mpInput input premise left right pairLeftSource pairRightSource origin)
    (Indexed.argumentWire (thirdFields input premise left right pairLeftSource pairRightSource origin))
    (DynamicModusPonensTemplates.inputWire input premise left right pairLeftSource pairRightSource origin) _ _
    (supportsOutputs basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin) (by
      change TM2OutputsInTime (FramedFieldSelection.machine (Γ := Alphabet) routing)
        ((Indexed.argumentWire (thirdFields input premise left right pairLeftSource pairRightSource origin)).map id) _ _
      simpa only [List.map_id] using selected)
  apply WordEqualityMachine.within joined
  simp only [routedClock,routing,List.length_cons,List.length_nil]
  omega

/-- One physical run starts from original theorem objects and emits every original MP graph byte. -/
noncomputable def outputs (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis) :
    TM2OutputsInTime (machine basis) (mpInput input premise left right pairLeftSource pairRightSource origin)
      (some (Indexed.instantiate DynamicModusPonensTemplates.template
        (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)))
      (clock basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin) := by
  have emitted := Indexed.outputs DynamicModusPonensTemplates.template
    (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)
  have joined := StackMachineComposition.outputs (routedMachine basis) (Indexed.machine DynamicModusPonensTemplates.template)
    (Equiv.refl (Option Alphabet)) (mpInput input premise left right pairLeftSource pairRightSource origin)
    (DynamicModusPonensTemplates.inputWire input premise left right pairLeftSource pairRightSource origin)
    (Indexed.instantiate DynamicModusPonensTemplates.template
      (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)) _ _
    (routedOutputs basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin) (by
      change TM2OutputsInTime (Indexed.machine DynamicModusPonensTemplates.template)
        ((DynamicModusPonensTemplates.inputWire input premise left right pairLeftSource pairRightSource origin).map id) _ _
      simpa only [List.map_id,DynamicModusPonensTemplates.inputWire] using emitted)
  exact joined


/-- Physical field production and the unchanged original checker agree on the full original block. -/
theorem original_checked_outputs (basis : AuthoredAxiomUnion.Basis) (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (inputWithin : input.axioms ⊆ basis) (premiseWithin : premise.axioms ⊆ basis)
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
      block.1.length = 58 ∧ block.1.map (·.origin) = List.replicate 58 origin ∧
      Nonempty (TM2OutputsInTime (machine basis) (mpInput input premise left right pairLeftSource pairRightSource origin)
        (some (encodeCertificate block))
        (clock basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin)) ∧
      decodeCertificate (Indexed.instantiate DynamicModusPonensTemplates.template
        (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)) = some block := by
  obtain ⟨block,computed,checked,count,origins,same,decoded⟩ := DynamicModusPonensTemplates.emitted_original
    input premise left right leftBool rightBool inputHyp premiseHyp leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin policy shape matching
  have ran := outputs basis input premise left right pairLeftSource pairRightSource origin inputWithin premiseWithin
  rw [same] at ran
  exact ⟨block,computed,checked,count,origins,⟨ran⟩,decoded⟩

/-- Final theorem support is the original union; the direct compiler hypotheses remain empty. -/
theorem result_parts (input premise : Theorem) (right : CanonicalTerm)
    (inputHyp : input.sequent.hyp = ∅) (premiseHyp : premise.sequent.hyp = ∅) :
    (mpResult input premise right).axioms = input.axioms∪premise.axioms ∧
      (mpResult input premise right).sequent.hyp = ∅ ∧
      (mpResult input premise right).sequent.concl = right := by
  simp [mpResult,Theorem.unionResult,inputHyp,premiseHyp]

end Mettapedia.Languages.HOLLight.DynamicModusPonensEmission
