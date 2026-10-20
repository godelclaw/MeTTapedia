import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackage

/-!
# Complete instantiation of parameterized indexed computation schemas

A schema assignment includes the explicit parameter context as well as the
motive, every method and every constructor field. Instantiation is proved
against the source-defined endpoints, without replacing the caller's chosen
parameter representation. Raw instantiation does not certify argument typing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Instantiation

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u
variable {I : Interface.{u}} {Head : Type} {n m : Nat}
variable (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)

/-- New schema binders precede the original parameter context in de Bruijn
order. Every original parameter receives the caller's actual assignment. -/
def assignment (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m) :
    Sub Head (arity admitted occurrence + n) m :=
  Fin.addCases (Guest.assignment admitted occurrence motive methods fields) parameters

@[simp] theorem assignment_parameter (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m)
    (index : Fin n) :
    assignment admitted occurrence parameters motive methods fields
      (Types.parameterShift (arity admitted occurrence) index) = parameters index := by
  change Fin.addCases (Guest.assignment admitted occurrence motive methods fields) parameters
    (Fin.natAdd (arity admitted occurrence) index) = parameters index
  simp

@[simp] theorem assignment_motive (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m) :
    assignment admitted occurrence parameters motive methods fields
      (Fin.castAdd n (motiveSlot admitted occurrence)) = motive := by
  simp only [assignment, Fin.addCases_left]
  simp [Guest.assignment, motiveSlot]

@[simp] theorem assignment_method (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m)
    (index : Fin admitted.constructors.length) :
    assignment admitted occurrence parameters motive methods fields
      (Fin.castAdd n (methodSlot admitted occurrence index)) = methods index := by
  simp only [assignment, Fin.addCases_left]
  simp only [Guest.assignment, methodSlot]
  have bound := index.rev.isLt
  erw [dif_neg (by omega), dif_neg (by omega)]
  have same : (⟨fieldCount (admitted.constructors.get occurrence).body + index.rev.val -
      fieldCount (admitted.constructors.get occurrence).body, by omega⟩ :
      Fin admitted.constructors.length) = index.rev := by
    apply Fin.ext
    simp
  rw [same, Fin.rev_rev]

@[simp] theorem assignment_field (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m)
    (index : Fin (fieldCount (admitted.constructors.get occurrence).body)) :
    assignment admitted occurrence parameters motive methods fields
      (Fin.castAdd n (fieldSlot admitted occurrence index)) = fields index := by
  simp only [assignment, Fin.addCases_left, Guest.assignment, fieldSlot]
  erw [dif_pos index.rev.isLt]
  exact congrArg fields (Fin.rev_rev index)

theorem instantiate_parameter_term (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m)
    (term : Tm Head n) :
    subst (assignment admitted occurrence parameters motive methods fields)
      (rename (Types.parameterShift (arity admitted occurrence)) term) = subst parameters term := by
  rw [subst_rename]
  congr 1
  funext index
  exact assignment_parameter admitted occurrence parameters motive methods fields index

/-- Both endpoints, including all recursive calls, instantiate according to
the independent source constructor equation and the supplied parameters. -/
theorem schema_instance (indices : IndexSyntax I Head) (types : Types.TypeSyntax I Head n)
    (recursor : Tm Head n) (parameters : Sub Head n m) (motive : Tm Head m)
    (methods : Fin admitted.constructors.length → Tm Head m)
    (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m) :
    let row := Types.iotaSchema indices admitted occurrence types recursor
    let sigma := assignment admitted occurrence parameters motive methods fields
    (subst sigma row.1, subst sigma row.2) =
      Types.endpoints indices admitted occurrence (types.map (subst parameters))
        (subst parameters recursor) motive methods fields := by
  dsimp only
  unfold Types.iotaSchema
  rw [Types.endpoints_substitute]
  congr 1
  · cases types
    simp only [Types.TypeSyntax.map]
    congr 1 <;> first
      | exact instantiate_parameter_term admitted occurrence parameters motive methods fields _
      | (funext argument; exact instantiate_parameter_term admitted occurrence parameters motive methods fields _)
  · exact instantiate_parameter_term admitted occurrence parameters motive methods fields _
  · exact assignment_motive admitted occurrence parameters motive methods fields
  · funext index; exact assignment_method admitted occurrence parameters motive methods fields index
  · funext index; exact assignment_field admitted occurrence parameters motive methods fields index

variable (indices : IndexSyntax I Head) (parameters : Declarations.Parameters I Head n)
    (names : Declarations.Names)

/-- Source unfolding with explicit actual parameters. This relation is stated
using constructor endpoints, independently of the generated schema table. -/
inductive Unfold (admitted : Admitted I []) (indices : IndexSyntax I Head)
    (parameters : Declarations.Parameters I Head n) (names : Declarations.Names)
    {m : Nat} : Tm Head m → Tm Head m → Prop where
  | constructor (occurrence : Fin admitted.constructors.length)
      (parameterValues : Sub Head n m) (motive : Tm Head m)
      (methods : Fin admitted.constructors.length → Tm Head m)
      (fields : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head m) :
      Unfold admitted indices parameters names
        (Types.endpoints indices admitted occurrence ((parameters.types names).map (subst parameterValues))
          (subst parameterValues (Package.recursor parameters names)) motive methods fields).1
        (Types.endpoints indices admitted occurrence ((parameters.types names).map (subst parameterValues))
          (subst parameterValues (Package.recursor parameters names)) motive methods fields).2

/-- Every assignment to a complete generated row recovers an actual source
unfolding, with parameter values read from their original slots. -/
theorem schema_unfold (sigma : Sub Head (arity admitted occurrence + n) m) :
    Unfold admitted indices parameters names
      (subst sigma (Types.iotaSchema indices admitted occurrence (parameters.types names)
        (Package.recursor parameters names)).1)
      (subst sigma (Types.iotaSchema indices admitted occurrence (parameters.types names)
        (Package.recursor parameters names)).2) := by
  let parameterValues : Sub Head n m := fun i => sigma (Types.parameterShift (arity admitted occurrence) i)
  let motive := sigma (Fin.castAdd n (motiveSlot admitted occurrence))
  let methods := fun i => sigma (Fin.castAdd n (methodSlot admitted occurrence i))
  let fields := fun i => sigma (Fin.castAdd n (fieldSlot admitted occurrence i))
  have pair := Types.endpoints_substitute indices admitted occurrence
    ((parameters.types names).map (rename (Types.parameterShift (arity admitted occurrence))))
    (rename (Types.parameterShift (arity admitted occurrence)) (Package.recursor parameters names))
    (.var (Fin.castAdd n (motiveSlot admitted occurrence)))
    (fun i => .var (Fin.castAdd n (methodSlot admitted occurrence i)))
    (fun i => .var (Fin.castAdd n (fieldSlot admitted occurrence i))) sigma
  have source := Unfold.constructor (admitted := admitted) (indices := indices)
    (parameters := parameters) (names := names) occurrence parameterValues motive methods fields
  have left := congrArg Prod.fst pair
  have right := congrArg Prod.snd pair
  dsimp only at left right
  erw [left, right]
  simpa only [Types.TypeSyntax.map, subst_rename, subst, parameterValues, motive, methods, fields] using source

/-- Generated raw roots are exactly the source's parameterized constructor
unfoldings. The backward direction does not infer well-typed arguments. -/
theorem computation_iff_unfold (left right : Tm Head m) :
    (Package.computation indices parameters names admitted).support.step left right ↔
      Unfold admitted indices parameters names left right := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | instantiate index _ sigma =>
        let sourceOccurrence : Fin admitted.constructors.length := ⟨index.val, by
          simpa only [Package.table_length] using index.isLt⟩
        have selected : (Package.table indices parameters names admitted).get index =
            ⟨arity admitted sourceOccurrence + n,
              Types.iotaSchema indices admitted sourceOccurrence (parameters.types names)
                (Package.recursor parameters names)⟩ := by
          simpa only [Package.position, sourceOccurrence] using
            Package.table_get indices parameters names admitted sourceOccurrence
        generalize found : (Package.table indices parameters names admitted).get index = row at sigma ⊢
        have same := found.symm.trans selected
        cases same
        exact schema_unfold admitted sourceOccurrence indices parameters names sigma
  · intro source
    cases source with
    | constructor sourceOccurrence parameterValues motive methods fields =>
        have evidence := Package.evidenceAt indices parameters names admitted sourceOccurrence
          (assignment admitted sourceOccurrence parameterValues motive methods fields)
        have paired := schema_instance admitted sourceOccurrence indices (parameters.types names)
          (Package.recursor parameters names) parameterValues motive methods fields
        have left := congrArg Prod.fst paired
        have right := congrArg Prod.snd paired
        dsimp only at left right
        rw [left, right] at evidence
        exact ⟨evidence⟩

/-- The shared finite decoder neither loses nor invents a source unfolding.
Its receipt includes the chosen row and the complete parameter assignment. -/
theorem decoded_iff_unfold (left right : Tm Head m) :
    (∃ receipt : SchemaTableConversionCode.Code Head m,
      SchemaTableConversionCode.decode (Package.table indices parameters names admitted) (fun _ => true)
        receipt = some (left, right)) ↔ Unfold admitted indices parameters names left right := by
  rw [← computation_iff_unfold]
  constructor
  · rintro ⟨receipt, accepted⟩
    exact SchemaTableConversionCode.decode_sound _ _ receipt accepted
  · exact SchemaTableConversionCode.decode_complete _ _

#print axioms schema_instance
#print axioms computation_iff_unfold
#print axioms decoded_iff_unfold

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Instantiation
