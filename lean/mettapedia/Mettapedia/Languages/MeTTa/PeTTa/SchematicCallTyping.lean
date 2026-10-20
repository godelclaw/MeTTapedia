import Mettapedia.Languages.MeTTa.PeTTa.JointSchemeContracts

/-!
# Generating joint constraints for schematic call typing

A domain is either a literal universal contract or a type pattern. An
inference variable remains a type pattern after substitution; acquiring the
name `Any` never turns it into a universal domain. Every input and result
uses one substitution. Candidate types retain their lexical coordinates.

The independent typing rules quantify over finite candidates carrying both
a type and its source conditions. The compiler retains those conditions in
the joint equation problem and uses the total first-order unifier. Soundness
and completeness connect these two presentations. Source conditions cannot
be discarded merely because the candidate's visible type is ground. This
does not assert a correspondence for SWI's full candidate enumerator,
classifier interpreter or gradual-hole coordinate allocation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SchematicCallTyping

open Mettapedia.Logic.LP
open JointSchemeContracts

variable {σ : LPSignature}

inductive Domain (σ : LPSignature) where
  | universal
  | typed (pattern : Term σ)

structure Candidate (σ : LPSignature) where
  type : Term σ
  conditions : Equations σ

/-- An intrinsic or already unconditional type candidate. -/
def Candidate.plain (type : Term σ) : Candidate σ := ⟨type, []⟩

abbrev Candidates (σ : LPSignature) := List (Candidate σ)

inductive Checks (witness : Subst σ) : Domain σ → Candidates σ → Prop where
  | universal (candidates : Candidates σ) : Checks witness .universal candidates
  | typed {pattern : Term σ} {actual : Candidate σ} {candidates : Candidates σ} :
      actual ∈ candidates → Unifies witness actual.conditions →
      witness.applyTerm actual.type = witness.applyTerm pattern →
      Checks witness (.typed pattern) candidates

inductive ChecksVector (witness : Subst σ) :
    List (Domain σ) → List (Candidates σ) → Prop where
  | nil : ChecksVector witness [] []
  | cons {domain : Domain σ} {candidates : Candidates σ}
      {domains : List (Domain σ)} {values : List (Candidates σ)} :
      Checks witness domain candidates → ChecksVector witness domains values →
      ChecksVector witness (domain :: domains) (candidates :: values)

/-- A checked position remains available as evidence for the same obligation.
The witness is shared with the whole vector, rather than freshly selected. -/
theorem ChecksVector.checked_member {witness : Subst σ}
    {domains : List (Domain σ)} {values : List (Candidates σ)}
    (checked : ChecksVector witness domains values)
    {domain : Domain σ} {candidates : Candidates σ}
    (member : (domain,candidates) ∈ domains.zip values) :
    Checks witness domain candidates := by
  induction checked with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with same | later
      · cases same
        exact head
      · exact ih later

def position : Domain σ → Candidates σ → List (Equations σ)
  | .universal, _ => [[]]
  | .typed pattern, candidates =>
      candidates.map fun actual => actual.conditions ++ [(actual.type, pattern)]

def vector : List (Domain σ) → List (Candidates σ) → List (Equations σ)
  | [], [] => [[]]
  | domain :: domains, value :: values =>
      (position domain value).flatMap fun first =>
        (vector domains values).map fun rest => first ++ rest
  | _, _ => []

theorem unifies_append (witness : Subst σ) (first rest : Equations σ) :
    Unifies witness (first ++ rest) ↔ Unifies witness first ∧ Unifies witness rest := by
  constructor
  · intro solved
    exact ⟨fun pair member => solved pair (List.mem_append_left _ member),
      fun pair member => solved pair (List.mem_append_right _ member)⟩
  · rintro ⟨left,right⟩ pair member
    rcases List.mem_append.mp member with member | member
    · exact left pair member
    · exact right pair member

theorem position_iff (witness : Subst σ) (domain : Domain σ) (value : Candidates σ) :
    (∃ equations ∈ position domain value, Unifies witness equations) ↔
      Checks witness domain value := by
  cases domain with
  | universal =>
      constructor
      · intro _; exact .universal value
      · intro _; exact ⟨[], by simp [position], by simp [Unifies]⟩
  | typed pattern =>
      constructor
      · rintro ⟨equations, member, solves⟩
        obtain ⟨actual, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨conditions, equality⟩ := (unifies_append witness _ _).mp solves
        exact .typed present conditions (equality (actual.type,pattern) (by simp))
      · intro checked
        cases checked with
        | typed member conditions equal =>
            exact ⟨_, List.mem_map.mpr ⟨_, member, rfl⟩,
              (unifies_append witness _ _).mpr
                ⟨conditions, by simpa [Unifies] using equal⟩⟩

theorem vector_iff (witness : Subst σ)
    (domains : List (Domain σ)) (values : List (Candidates σ)) :
    (∃ equations ∈ vector domains values, Unifies witness equations) ↔
      ChecksVector witness domains values := by
  induction domains generalizing values with
  | nil =>
      cases values with
      | nil =>
          constructor
          · intro _; exact .nil
          · intro _; exact ⟨[], by simp [vector], by simp [Unifies]⟩
      | cons value values =>
          constructor
          · simp [vector]
          · intro impossible; cases impossible
  | cons domain domains ih =>
      cases values with
      | nil =>
          constructor
          · simp [vector]
          · intro impossible; cases impossible
      | cons value values =>
          constructor
          · rintro ⟨equations, member, solves⟩
            obtain ⟨first, firstMember, tailMember⟩ := List.mem_flatMap.mp member
            obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp tailMember
            obtain ⟨firstSolves, restSolves⟩ := (unifies_append witness first rest).mp solves
            exact .cons ((position_iff witness domain value).mp ⟨first,firstMember,firstSolves⟩)
              ((ih values).mp ⟨rest,restMember,restSolves⟩)
          · intro checked
            cases checked with
            | cons firstChecked restChecked =>
                obtain ⟨first, firstMember, firstSolves⟩ :=
                  (position_iff witness domain value).mpr firstChecked
                obtain ⟨rest, restMember, restSolves⟩ := (ih values).mpr restChecked
                refine ⟨first ++ rest, ?_, (unifies_append witness first rest).mpr
                  ⟨firstSolves,restSolves⟩⟩
                exact List.mem_flatMap.mpr ⟨first,firstMember,
                  List.mem_map.mpr ⟨rest,restMember,rfl⟩⟩

structure Scheme (σ : LPSignature) where
  occurrence : Nat
  domains : List (Domain σ)
  result : Domain σ

inductive CallTyped (schemes : List (Scheme σ))
    (inputs : List (Candidates σ)) (result : Candidates σ) : Prop where
  | call {scheme : Scheme σ} (member : scheme ∈ schemes) (witness : Subst σ) :
      ChecksVector witness scheme.domains inputs → Checks witness scheme.result result →
      CallTyped schemes inputs result

/-- An unchanged returned value needs no second proof of a checked input
obligation. This reuses evidence, while preserving the call's scheme and its
single joint substitution. -/
theorem CallTyped.reuse_checked_result {schemes : List (Scheme σ)}
    {inputs : List (Candidates σ)} {result : Candidates σ}
    {scheme : Scheme σ} (member : scheme ∈ schemes) (witness : Subst σ)
    (checked : ChecksVector witness scheme.domains inputs)
    (same : (scheme.result,result) ∈ scheme.domains.zip inputs) :
    CallTyped schemes inputs result :=
  .call member witness checked (checked.checked_member same)

def compile (schemes : List (Scheme σ)) (inputs : List (Candidates σ))
    (result : Candidates σ) : List (Alternative σ) :=
  schemes.flatMap fun scheme =>
    (vector (scheme.domains ++ [scheme.result]) (inputs ++ [result])).map fun equations =>
      ⟨scheme.occurrence,equations⟩

theorem checksVector_append_singleton (witness : Subst σ)
    (domains : List (Domain σ)) (values : List (Candidates σ))
    (resultDomain : Domain σ) (result : Candidates σ) :
    ChecksVector witness (domains ++ [resultDomain]) (values ++ [result]) ↔
      ChecksVector witness domains values ∧ Checks witness resultDomain result := by
  induction domains generalizing values with
  | nil =>
      cases values with
      | nil =>
          constructor
          · intro checked; cases checked with | cons head tail => exact ⟨.nil,head⟩
          · rintro ⟨_,head⟩; exact .cons head .nil
      | cons value values =>
          constructor
          · intro impossible
            cases impossible with | cons _ tail => cases values <;> cases tail
          · rintro ⟨impossible,_⟩; cases impossible
  | cons domain domains ih =>
      cases values with
      | nil =>
          constructor
          · intro impossible
            cases impossible with | cons _ tail => cases domains <;> cases tail
          · rintro ⟨impossible,_⟩; cases impossible
      | cons value values =>
          constructor
          · intro checked
            cases checked with
            | cons head tail =>
                obtain ⟨rest,last⟩ := (ih values).mp tail
                exact ⟨.cons head rest,last⟩
          · rintro ⟨checked,last⟩
            cases checked with
            | cons head tail => exact .cons head ((ih values).mpr ⟨tail,last⟩)

theorem compilation_adequate (schemes : List (Scheme σ))
    (inputs : List (Candidates σ)) (result : Candidates σ) :
    Joint (compile schemes inputs result) [] ↔ CallTyped schemes inputs result := by
  constructor
  · rintro ⟨row,member,witness,solves⟩
    obtain ⟨scheme,schemeMember,compiled⟩ := List.mem_flatMap.mp member
    obtain ⟨equations,equationsMember,rfl⟩ := List.mem_map.mp compiled
    have checked := (vector_iff witness _ _).mp
      ⟨equations,equationsMember,by simpa using solves⟩
    obtain ⟨inputsChecked,resultChecked⟩ := (checksVector_append_singleton witness _ _ _ _).mp checked
    exact .call schemeMember witness inputsChecked resultChecked
  · intro checked
    cases checked with
    | call member witness inputChecked resultChecked =>
        obtain ⟨equations,equationsMember,solves⟩ := (vector_iff witness _ _).mpr
          ((checksVector_append_singleton witness _ _ _ _).mpr ⟨inputChecked,resultChecked⟩)
        exact ⟨_, List.mem_flatMap.mpr ⟨_,member,List.mem_map.mpr
          ⟨equations,equationsMember,rfl⟩⟩, witness, by simpa using solves⟩

theorem checker_exact [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (schemes : List (Scheme σ))
    (inputs : List (Candidates σ)) (result : Candidates σ) :
    guard (compile schemes inputs result) [] = true ↔ CallTyped schemes inputs result :=
  (guard_iff _ _).trans (compilation_adequate schemes inputs result)

namespace Controls

open JointSchemeContracts.Controls (sig number string shared)

def identityScheme : Scheme sig := ⟨0,[.typed shared],.typed shared⟩

theorem identity_exact (a b : String) :
    CallTyped [identityScheme] [[.plain (.const a)]] [.plain (.const b)] ↔ a = b := by
  constructor
  · intro typed
    cases typed with
    | call member witness inputs result =>
        simp only [List.mem_singleton] at member
        subst_vars
        cases inputs with
        | cons first rest =>
            cases first with
            | typed present _ firstEqual =>
                simp only [List.mem_singleton] at present
                subst_vars
                cases result with
                | typed present _ resultEqual =>
                    simp only [List.mem_singleton] at present
                    subst_vars
                    exact Term.const.inj (firstEqual.trans resultEqual.symm)
  · intro same
    subst b
    let witness := Subst.single (σ := sig) (.scheme 0 0) (.const a)
    have solves : witness.applyTerm (.const a) = witness.applyTerm shared := by
      simp [witness,shared,Subst.applyTerm,Subst.single]
    have checked : Checks witness (.typed shared) [.plain (.const a)] := by
      apply Checks.typed (actual := Candidate.plain (σ := sig) (.const a))
      · simp
      · simp [Candidate.plain,Unifies]
      · exact solves
    exact .call (scheme := identityScheme) (by simp) witness (.cons checked .nil) checked

theorem matching_polymorphic_call :
    CallTyped [identityScheme] [[.plain number]] [.plain number] := (identity_exact _ _).mpr rfl

theorem shared_result_rejects_conflict :
    ¬ CallTyped [identityScheme] [[.plain number]] [.plain string] := by
  simpa [number,string] using (identity_exact "Number" "String").not.mpr (by decide)

theorem inferred_any_is_not_a_universal_domain :
    ¬ CallTyped [identityScheme] [[.plain (.const "Any")]] [.plain number] := by
  simpa [number] using (identity_exact "Any" "Number").not.mpr (by decide)

theorem literal_universal_needs_no_type_candidates :
    ChecksVector (Subst.id sig) [.universal] [[]] := .cons (.universal []) .nil

end Controls

#print axioms compilation_adequate
#print axioms checker_exact
#print axioms ChecksVector.checked_member
#print axioms CallTyped.reuse_checked_result
#print axioms Controls.identity_exact

end Mettapedia.Languages.MeTTa.PeTTa.SchematicCallTyping
