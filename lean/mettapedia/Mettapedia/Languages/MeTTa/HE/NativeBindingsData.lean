import Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# LeaTTa binding-codec study

This downstream implementation study uses LeaTTa's executable binding
carrier. It is not part of the independent HE specification or its abstract
machine, and it supplies no reference-implementation claim for HE.

The encoded records retain their original order, duplicate relations, equality
endpoints and recursively stored values. The executable image guard admits
exactly the declared HE atom representation. Values outside that image are
rejected before encoding rather than projected to placeholder payloads.
The carrier here is LeaTTa's executable binding representation, not a claim
about the layout or identities of CeTTa's C binding records.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeBindingsData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance

def groundInImage : Metta.Ground → Bool
  | .int _ | .str _ | .bool _ | .external _ _ => true
  | .float _ | .unit | .error _ | .bindings _ => false

mutual

def atomInImage : Metta.Atom → Bool
  | .sym _ | .var _ => true
  | .gnd value => groundInImage value
  | .expr atoms => atomsInImage atoms
termination_by atom => 2 * sizeOf atom

def atomsInImage : List Metta.Atom → Bool
  | [] => true
  | atom :: rest => atomInImage atom && atomsInImage rest
termination_by atoms => 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

theorem atomsInImage_eq_all (atoms : List Metta.Atom) :
    atomsInImage atoms = atoms.all atomInImage := by
  induction atoms with
  | nil => simp [atomsInImage]
  | cons atom rest ih => simp [atomsInImage, ih]

theorem atomInImage_readback (atom : Metta.Atom) (accepted : atomInImage atom = true) :
    encodeModelAtom (decodeModelAtom atom) = atom := by
  cases atom with
  | sym name => rfl
  | var name => rfl
  | gnd value =>
      cases value <;> simp_all [atomInImage, groundInImage, decodeModelAtom,
        decodeModelGround, encodeModelAtom, encodeModelGround]
  | expr atoms =>
      have children : ∀ child ∈ atoms, atomInImage child = true := by
        simpa only [atomInImage, atomsInImage_eq_all, List.all_eq_true] using accepted
      simp only [decodeModelAtom, encodeModelAtom, encodeModelAtoms_eq_map,
        decodeModelAtoms_eq_map, List.map_map]
      congr 1
      calc
        atoms.map (encodeModelAtom ∘ decodeModelAtom) = atoms.map id := by
          apply List.map_congr_left
          intro child member
          exact atomInImage_readback child (children child member)
        _ = atoms := List.map_id atoms
termination_by atom.size
decreasing_by
  subst_vars
  have bound : child.size ≤ (atoms.map Metta.Atom.size).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨child, member, rfl⟩)
  simp only [Metta.Atom.size] at *
  omega

theorem atomInImage_translation (atom : Atom) : atomInImage (encodeModelAtom atom) = true := by
  cases atom with
  | symbol name => simp [encodeModelAtom, atomInImage]
  | var name => simp [encodeModelAtom, atomInImage]
  | grounded value =>
      cases value <;> simp [encodeModelAtom, encodeModelGround, atomInImage, groundInImage]
  | expression atoms =>
      simp only [encodeModelAtom, atomInImage, atomsInImage_eq_all, encodeModelAtoms_eq_map,
        List.all_map, Function.comp_def, List.all_eq_true]
      intro child member
      exact atomInImage_translation child
termination_by sizeOf atom

theorem atomInImage_iff (atom : Metta.Atom) : atomInImage atom = true ↔ LeaAtomHEImage atom := by
  constructor
  · intro accepted
    exact ⟨decodeModelAtom atom, atomInImage_readback atom accepted⟩
  · rintro ⟨original, rfl⟩
    exact atomInImage_translation original

def bindingsInImage (bindings : Metta.Bindings) : Bool :=
  bindings.all fun relation => match relation with
    | .val _ value => atomInImage value
    | .eq _ _ => true

theorem bindingsInImage_iff (bindings : Metta.Bindings) :
    bindingsInImage bindings = true ↔ LeaBindingsHEImage bindings := by
  simp only [bindingsInImage, List.all_eq_true]
  constructor
  · intro accepted key value member
    exact (atomInImage_iff value).mp (accepted _ member)
  · intro image relation member
    cases relation with
    | val key value => exact (atomInImage_iff value).mpr (image key value member)
    | eq left right => rfl

def relationData : Metta.BindingRel → Atom
  | .val name value =>
      .expression [.symbol "he-query-value-v1", .var name, decodeModelAtom value]
  | .eq left right =>
      .expression [.symbol "he-query-equality-v1", .var left, .var right]

def readRelation : Atom → Option Metta.BindingRel
  | .expression [.symbol "he-query-value-v1", .var name, value] =>
      some (.val name (encodeModelAtom value))
  | .expression [.symbol "he-query-equality-v1", .var left, .var right] =>
      some (.eq left right)
  | _ => none

theorem readRelation_relationData (relation : Metta.BindingRel)
    (image : ∀ key value, relation = .val key value → LeaAtomHEImage value) :
    readRelation (relationData relation) = some relation := by
  cases relation with
  | val key value =>
      simp only [relationData, readRelation]
      rw [encodeModelAtom_decodeModelAtom_of_heImage (image key value rfl)]
  | eq left right => rfl

theorem readRelation_image {data : Atom} {relation : Metta.BindingRel}
    (decoded : readRelation data = some relation) :
    ∀ key value, relation = .val key value → LeaAtomHEImage value := by
  unfold readRelation at decoded
  split at decoded
  · cases decoded
    intro key value equality
    cases equality
    exact leaAtomHEImage_encodeModelAtom _
  · cases decoded
    intro key value impossible
    cases impossible
  · simp at decoded

def bindingsData (bindings : Metta.Bindings) : Option Atom :=
  if bindingsInImage bindings then
    some (.expression [.symbol "he-query-bindings-v1", .expression (bindings.map relationData)])
  else none

def readBindings : Atom → Option Metta.Bindings
  | .expression [.symbol "he-query-bindings-v1", .expression relations] =>
      relations.mapM readRelation
  | _ => none

private theorem readRelations_image : ∀ (data : List Atom) (bindings : Metta.Bindings),
    data.mapM readRelation = some bindings → LeaBindingsHEImage bindings
  | [], bindings, decoded => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at decoded
      subst bindings
      exact leaBindingsHEImage_empty
  | head :: tail, bindings, decoded => by
      cases headRead : readRelation head with
      | none => simp [List.mapM_cons, headRead] at decoded
      | some relation =>
          cases tailRead : tail.mapM readRelation with
          | none => simp [List.mapM_cons, headRead, tailRead] at decoded
          | some rest =>
              have result : relation :: rest = bindings := by
                simpa [List.mapM_cons, headRead, tailRead] using decoded
              subst bindings
              intro key value member
              rcases List.mem_cons.mp member with first | later
              · exact readRelation_image headRead key value first.symm
              · exact readRelations_image tail rest tailRead key value later

/-- Decoding itself establishes the exact-image invariant. -/
theorem readBindings_image {data : Atom} {bindings : Metta.Bindings}
    (decoded : readBindings data = some bindings) : LeaBindingsHEImage bindings := by
  unfold readBindings at decoded
  split at decoded
  · exact readRelations_image _ _ decoded
  · simp at decoded

theorem bindingsData_defined_iff (bindings : Metta.Bindings) :
    (bindingsData bindings).isSome = true ↔ LeaBindingsHEImage bindings := by
  simp [bindingsData, ← bindingsInImage_iff]

theorem readBindings_bindingsData (bindings : Metta.Bindings) (image : LeaBindingsHEImage bindings) :
    (bindingsData bindings).bind readBindings = some bindings := by
  rw [bindingsData, if_pos ((bindingsInImage_iff bindings).mpr image)]
  simp only [Option.bind_some, readBindings, List.mapM_map, Function.comp_def]
  have entries : ∀ relation ∈ bindings, readRelation (relationData relation) = some relation := by
    intro relation member
    apply readRelation_relationData relation
    intro key value equality
    subst relation
    exact image key value member
  induction bindings with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mapM_cons, entries head (by simp)]
      have next := ih (fun key value member => image key value (List.mem_cons_of_mem _ member))
        (fun relation member => entries relation (List.mem_cons_of_mem _ member))
      simp [next]

theorem bindingsData_injective {left right : Metta.Bindings} {data : Atom}
    (leftEncoded : bindingsData left = some data) (rightEncoded : bindingsData right = some data) :
    left = right := by
  have leftImage : LeaBindingsHEImage left :=
    (bindingsData_defined_iff left).mp (by simp [leftEncoded])
  have rightImage : LeaBindingsHEImage right :=
    (bindingsData_defined_iff right).mp (by simp [rightEncoded])
  have leftRead := readBindings_bindingsData left leftImage
  have rightRead := readBindings_bindingsData right rightImage
  rw [leftEncoded] at leftRead
  rw [rightEncoded] at rightRead
  exact Option.some.inj (leftRead.symm.trans rightRead)

end Mettapedia.Languages.MeTTa.HE.NativeBindingsData
