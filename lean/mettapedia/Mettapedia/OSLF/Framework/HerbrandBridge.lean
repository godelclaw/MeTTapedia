import Mettapedia.OSLF.Framework.BackwardNarrowing
import Mettapedia.OSLF.Framework.PredFiniteSufficient
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
import Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

/-!
# First-order MeTTaIL patterns as Herbrand terms

A first-order MeTTaIL pattern, built from constructors and metavariables, is a term of the
Herbrand universe whose function symbols are constructor labels with their arities (`Labels`).
`encode` numbers the metavariables by a list of names; a ground pattern encodes with no names.
`decode` reads a Herbrand term back.

- `decode_encode`, `encode_injective`: encoding forgets nothing;
- `encode_decode`: a canonical ground Herbrand term (`Canonical`: no variable, no nullary
  application) is the encoding of its decoding;
- `encode_applyBindings`: instantiating a pattern with bindings is substituting into its encoding.

These are the facts the step correspondence of `HerbrandSteps` uses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.HerbrandBridge

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.BackwardNarrowing (Signature)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar)

/-- Constructor labels, with function symbols carrying their arity. -/
abbrev Labels : LPSignature := Signature String (String × ℕ) Prod.snd

/-- An application of a label to a list of arguments. -/
def mkApp (label : String) (terms : List (Term Labels)) : Term Labels :=
  .app (label, terms.length) fun i => terms.get i

theorem app_cast {label : String} {first second : ℕ} (same : first = second)
    {left : Fin first → Term Labels} {right : Fin second → Term Labels}
    (pointwise : ∀ i, left i = right (Fin.cast same i)) :
    Term.app (σ := Labels) (label, first) left = Term.app (label, second) right := by
  subst same
  congr 1
  funext i
  exact pointwise i

theorem applyTerm_mkApp (substitution : Subst Labels) (label : String) (terms : List (Term Labels)) :
    substitution.applyTerm (mkApp label terms) = mkApp label (terms.map substitution.applyTerm) := by
  unfold mkApp
  rw [Subst.applyTerm_app]
  exact app_cast (List.length_map _).symm fun i => by simp

/-! ## Pointwise relations of lists -/

theorem forall₂_left {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      ∀ {element : α}, element ∈ first → ∃ other ∈ second, relation element other
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, _, member => by
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨other, otherMember, related⟩ := forall₂_left tail inside
      exact ⟨other, List.mem_cons_of_mem _ otherMember, related⟩

theorem forall₂_right {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      ∀ {element : β}, element ∈ second → ∃ other ∈ first, relation other element
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, _, member => by
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨other, otherMember, related⟩ := forall₂_right tail inside
      exact ⟨other, List.mem_cons_of_mem _ otherMember, related⟩

theorem forall₂_imp_mem {α β : Type} {relation other : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      (∀ a b, a ∈ first → relation a b → other a b) → List.Forall₂ other first second
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, implies =>
    .cons (implies _ _ List.mem_cons_self head)
      (forall₂_imp_mem tail fun a b member related => implies a b (List.mem_cons_of_mem _ member) related)

/-! ## Encoding and decoding -/

mutual
/-- **The Herbrand term of a first-order pattern**, with metavariables numbered by `names`. -/
def encode (names : List String) : Pattern → Option (Term Labels)
  | .fvar name => (names.idxOf? name).map .var
  | .apply label [] => some (.const label)
  | .apply label (argument :: arguments) =>
      match encode names argument, encodeList names arguments with
      | some term, some terms => some (mkApp label (term :: terms))
      | _, _ => none
  | _ => none

def encodeList (names : List String) : List Pattern → Option (List (Term Labels))
  | [] => some []
  | argument :: arguments =>
      match encode names argument, encodeList names arguments with
      | some term, some terms => some (term :: terms)
      | _, _ => none
end

theorem encodeList_some_iff (names : List String) :
    ∀ (arguments : List Pattern) (terms : List (Term Labels)),
      encodeList names arguments = some terms ↔ List.Forall₂ (fun argument term => encode names argument = some term)
        arguments terms
  | [], terms => by cases terms <;> simp [encodeList]
  | argument :: arguments, terms => by
    rw [encodeList]
    cases encodedHead : encode names argument with
    | none =>
      simp only
      constructor
      · intro h; cases h
      · intro related
        cases related with
        | cons head _ => rw [encodedHead] at head; cases head
    | some term =>
      cases encodedTail : encodeList names arguments with
      | none =>
        simp only
        constructor
        · intro h; cases h
        · intro related
          cases related with
          | cons _ tail =>
            have := (encodeList_some_iff names arguments _).mpr tail
            rw [encodedTail] at this; cases this
      | some rest =>
        simp only [Option.some.injEq]
        constructor
        · rintro rfl
          exact .cons encodedHead ((encodeList_some_iff names arguments rest).mp encodedTail)
        · intro related
          cases related with
          | cons head tail =>
            rw [encodedHead] at head
            cases head
            rw [(encodeList_some_iff names arguments _).mpr tail] at encodedTail
            cases encodedTail
            rfl

theorem encode_apply_some {names : List String} {label : String} {arguments : List Pattern}
    {encoded : Term Labels} (read : encode names (.apply label arguments) = some encoded) :
    (arguments = [] ∧ encoded = .const label) ∨
      ∃ terms, arguments ≠ [] ∧ encodeList names arguments = some terms ∧ encoded = mkApp label terms := by
  cases arguments with
  | nil => simp only [encode, Option.some.injEq] at read; exact Or.inl ⟨rfl, read.symm⟩
  | cons argument rest =>
    right
    simp only [encode] at read
    split at read
    · rename_i term terms encodedHead encodedTail
      cases read
      exact ⟨term :: terms, List.cons_ne_nil _ _, by simp [encodeList, encodedHead, encodedTail], rfl⟩
    · cases read

/-- Read a Herbrand term back as a pattern. -/
def decode : Term Labels → Pattern
  | .var index => .fvar ("?" ++ toString index)
  | .const label => .apply label []
  | .app symbol arguments => .apply symbol.1 (List.ofFn fun i => decode (arguments i))

theorem decode_mkApp (label : String) (terms : List (Term Labels)) :
    decode (mkApp label terms) = .apply label (terms.map decode) := by
  simp only [mkApp, decode]
  congr 1
  exact List.ofFn_getElem_eq_map terms decode

/-- **Decoding inverts encoding** at ground patterns. -/
theorem decode_encode (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode [] pattern = some encoded → decode encoded = pattern := by
  induction pattern using Pattern.inductionOn with
  | hfvar name => intro encoded read; simp [encode] at read
  | happly label arguments recurse =>
    intro encoded read
    rcases encode_apply_some read with ⟨rfl, rfl⟩ | ⟨terms, _, encodedArguments, rfl⟩
    · rfl
    · rw [decode_mkApp]
      congr 1
      have mapped : ∀ (patterns : List Pattern) (encodings : List (Term Labels)),
          List.Forall₂ (fun argument term => encode [] argument = some term) patterns encodings →
          (∀ q ∈ patterns, ∀ {encoded : Term Labels}, encode [] q = some encoded → decode encoded = q) →
          encodings.map decode = patterns := by
        intro patterns encodings related
        induction related with
        | nil => intro _; rfl
        | cons head _ ih =>
          intro each
          simp only [List.map_cons]
          rw [each _ List.mem_cons_self head, ih (fun q member => each q (List.mem_cons_of_mem _ member))]
      exact mapped arguments terms ((encodeList_some_iff [] arguments terms).mp encodedArguments) recurse
  | _ => intro encoded read; simp [encode] at read

/-- **Encoding is injective** on ground patterns. -/
theorem encode_injective {first second : Pattern} {encoded : Term Labels}
    (firstRead : encode [] first = some encoded) (secondRead : encode [] second = some encoded) :
    first = second :=
  (decode_encode first firstRead).symm.trans (decode_encode second secondRead)

/-- No variable and no nullary application: the shape of a ground encoding. -/
def Canonical : Term Labels → Prop
  | .var _ => False
  | .const _ => True
  | .app symbol arguments => 0 < symbol.2 ∧ ∀ i, Canonical (arguments i)

theorem encode_canonical (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode [] pattern = some encoded → Canonical encoded := by
  induction pattern using Pattern.inductionOn with
  | hfvar name => intro encoded read; simp [encode] at read
  | happly label arguments recurse =>
    intro encoded read
    rcases encode_apply_some read with ⟨rfl, rfl⟩ | ⟨terms, nonempty, encodedArguments, rfl⟩
    · trivial
    · have related := (encodeList_some_iff [] arguments terms).mp encodedArguments
      refine ⟨?_, fun i => ?_⟩
      · rw [← related.length_eq]
        exact List.length_pos_of_ne_nil nonempty
      · have below : i.val < arguments.length := by rw [related.length_eq]; exact i.isLt
        have read := (List.forall₂_iff_get.mp related).2 i.val below i.isLt
        exact recurse _ (List.get_mem _ _) read
  | _ => intro encoded read; simp [encode] at read

theorem encodeList_ofFn : ∀ (count : ℕ) (arguments : Fin count → Term Labels),
    (∀ i, encode [] (decode (arguments i)) = some (arguments i)) →
    encodeList [] (List.ofFn fun i => decode (arguments i)) = some (List.ofFn arguments)
  | 0, _, _ => rfl
  | count + 1, arguments, each => by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [encodeList, each 0, encodeList_ofFn count (fun i => arguments i.succ) (fun i => each i.succ)]

/-- **Encoding inverts decoding** at canonical terms. -/
theorem encode_decode : ∀ (term : Term Labels), Canonical term → encode [] (decode term) = some term
  | .var _, canonical => canonical.elim
  | .const _, _ => rfl
  | .app (label, arity) arguments, ⟨positive, canonical⟩ => by
    have each : ∀ i, encode [] (decode (arguments i)) = some (arguments i) :=
      fun i => encode_decode (arguments i) (canonical i)
    obtain ⟨count, rfl⟩ : ∃ count, arity = count + 1 := ⟨arity - 1, by omega⟩
    have rest := encodeList_ofFn count (fun i => arguments i.succ) (fun i => each i.succ)
    simp only [decode, List.ofFn_succ, encode, each 0, rest, mkApp, Option.some.injEq]
    apply app_cast (by simp)
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [Fin.succ]


/-! ## Free variables and match-correctness of encodable patterns -/

theorem encode_fvar_some {names : List String} {name : String} {encoded : Term Labels}
    (read : encode names (.fvar name) = some encoded) :
    ∃ index, names.idxOf? name = some index ∧ encoded = .var index := by
  simp only [encode, Option.map_eq_some_iff] at read
  obtain ⟨index, found, rfl⟩ := read
  exact ⟨index, found, rfl⟩

theorem encode_apply_list {names : List String} {label : String} {arguments : List Pattern}
    {terms : List (Term Labels)} (nonempty : arguments ≠ []) (read : encodeList names arguments = some terms) :
    encode names (.apply label arguments) = some (mkApp label terms) := by
  cases arguments with
  | nil => exact absurd rfl nonempty
  | cons argument rest =>
    simp only [encodeList] at read
    simp only [encode]
    split at read
    · rename_i term others headRead tailRead
      cases read
      simp
    · cases read

theorem encode_isMatchCorrect {names : List String} (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode names pattern = some encoded → isMatchCorrectAux pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hfvar name => intro _ _; rfl
  | happly label arguments recurse =>
    intro encoded read
    simp only [isMatchCorrectAux]
    rw [Mettapedia.OSLF.MeTTaIL.MatchSpec.isMatchCorrectListAux_iff_forall]
    intro argument member
    rcases encode_apply_some read with ⟨rfl, _⟩ | ⟨terms, _, encodedArguments, _⟩
    · cases member
    · obtain ⟨term, _, read⟩ := forall₂_left ((encodeList_some_iff names arguments terms).mp encodedArguments) member
      exact recurse argument member read
  | _ => intro encoded read; simp [encode] at read

theorem mem_freeVars_mkApp {label : String} {terms : List (Term Labels)} {index : ℕ} :
    index ∈ (mkApp label terms).freeVars ↔ ∃ term ∈ terms, index ∈ term.freeVars := by
  simp only [mkApp, Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, inside⟩
    exact ⟨_, List.get_mem _ _, inside⟩
  · rintro ⟨term, member, inside⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem member
    exact ⟨i, inside⟩

/-- **The variables of an encoding are the numbers of the pattern's metavariables.** -/
theorem encode_freeVars {names : List String} (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode names pattern = some encoded →
      ∀ index, index ∈ encoded.freeVars ↔ ∃ name ∈ freeVars pattern, names.idxOf? name = some index := by
  induction pattern using Pattern.inductionOn with
  | hfvar name =>
    intro encoded read index
    obtain ⟨found, idx, rfl⟩ := encode_fvar_some read
    simp only [Term.freeVars, Finset.mem_singleton, freeVars, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨name, rfl, idx⟩
    · rintro ⟨_, rfl, again⟩; rw [idx] at again; cases again; rfl
  | happly label arguments recurse =>
    intro encoded read index
    rcases encode_apply_some read with ⟨rfl, rfl⟩ | ⟨terms, _, encodedArguments, rfl⟩
    · simp [Term.freeVars, freeVars]
    · have related := (encodeList_some_iff names arguments terms).mp encodedArguments
      rw [mem_freeVars_mkApp]
      simp only [freeVars, List.mem_flatMap]
      constructor
      · rintro ⟨term, termMember, inside⟩
        obtain ⟨argument, argumentMember, argumentRead⟩ := forall₂_right related termMember
        obtain ⟨name, nameMember, found⟩ :=
          (recurse argument argumentMember argumentRead index).mp inside
        exact ⟨name, ⟨argument, argumentMember, nameMember⟩, found⟩
      · rintro ⟨name, ⟨argument, argumentMember, nameMember⟩, found⟩
        obtain ⟨term, termMember, argumentRead⟩ := forall₂_left related argumentMember
        exact ⟨term, termMember, (recurse argument argumentMember argumentRead index).mpr ⟨name, nameMember, found⟩⟩
  | _ => intro encoded read; simp [encode] at read

/-- Every metavariable of an encodable pattern is named. -/
theorem encode_named {names : List String} (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode names pattern = some encoded →
      ∀ name ∈ freeVars pattern, (names.idxOf? name).isSome := by
  induction pattern using Pattern.inductionOn with
  | hfvar name =>
    intro encoded read other member
    simp only [freeVars, List.mem_singleton] at member
    subst member
    obtain ⟨index, found, _⟩ := encode_fvar_some read
    rw [found]
    rfl
  | happly label arguments recurse =>
    intro encoded read name member
    simp only [freeVars, List.mem_flatMap] at member
    obtain ⟨argument, argumentMember, nameMember⟩ := member
    rcases encode_apply_some read with ⟨rfl, _⟩ | ⟨terms, _, encodedArguments, _⟩
    · cases argumentMember
    · obtain ⟨term, _, argumentRead⟩ :=
        forall₂_left ((encodeList_some_iff names arguments terms).mp encodedArguments) argumentMember
      exact recurse argument argumentMember argumentRead name nameMember
  | _ => intro encoded read; simp [encode] at read

/-! ## Bindings as substitutions -/

/-- The substitution of bindings: the number of a name stands for the encoding of its value. -/
def substOf (names : List String) (bindings : Bindings) : Subst Labels := fun index =>
  match names[index]? with
  | some name => (encode [] (lookupOrFvar bindings name)).getD (.var index)
  | none => .var index

theorem substOf_of_found {names : List String} {bindings : Bindings} {name : String} {index : ℕ}
    (found : names.idxOf? name = some index) :
    substOf names bindings index = (encode [] (lookupOrFvar bindings name)).getD (.var index) := by
  obtain ⟨below, atIndex, _⟩ := List.idxOf?_eq_some_iff.mp found
  simp [substOf, List.getElem?_eq_getElem below, atIndex]

/-- **Instantiating a pattern is substituting into its encoding**, when every value is encodable. -/
theorem encode_applyBindings {names : List String} (bindings : Bindings) (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode names pattern = some encoded →
      (∀ name ∈ freeVars pattern, (encode [] (lookupOrFvar bindings name)).isSome) →
      encode [] (applyBindings bindings pattern) = some ((substOf names bindings).applyTerm encoded) := by
  induction pattern using Pattern.inductionOn with
  | hfvar name =>
    intro encoded read values
    obtain ⟨index, found, rfl⟩ := encode_fvar_some read
    obtain ⟨value, valueRead⟩ := Option.isSome_iff_exists.mp (values name (by simp [freeVars]))
    rw [Subst.applyTerm_var, substOf_of_found found, valueRead]
    exact valueRead
  | happly label arguments recurse =>
    intro encoded read values
    rcases encode_apply_some read with ⟨rfl, rfl⟩ | ⟨terms, nonempty, encodedArguments, rfl⟩
    · simp [applyBindings, encode, Subst.applyTerm]
    · have related := (encodeList_some_iff names arguments terms).mp encodedArguments
      have mapped : encodeList [] (arguments.map (applyBindings bindings)) =
          some (terms.map (substOf names bindings).applyTerm) := by
        rw [encodeList_some_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine forall₂_imp_mem related fun argument term argumentMember argumentRead => ?_
        exact recurse argument argumentMember argumentRead fun name member =>
          values name (by simp only [freeVars, List.mem_flatMap]; exact ⟨argument, argumentMember, member⟩)
      have applied : applyBindings bindings (.apply label arguments) =
          .apply label (arguments.map (applyBindings bindings)) := by
        simp [applyBindings]
      rw [applied, encode_apply_list (by simpa using nonempty) mapped, applyTerm_mkApp]
  | _ => intro encoded read; simp [encode] at read

/-- The values a ground instance gives to the metavariables are encodable. -/
theorem encode_values {names : List String} (bindings : Bindings) (pattern : Pattern) :
    ∀ {encoded : Term Labels}, encode names pattern = some encoded →
      ∀ {instance_ : Term Labels}, encode [] (applyBindings bindings pattern) = some instance_ →
        ∀ name ∈ freeVars pattern, (encode [] (lookupOrFvar bindings name)).isSome := by
  induction pattern using Pattern.inductionOn with
  | hfvar name =>
    intro encoded _ instance_ instanceRead other member
    simp only [freeVars, List.mem_singleton] at member
    subst member
    rw [← Mettapedia.OSLF.Framework.PredFiniteSufficient.applyBindings_fvar, instanceRead]
    rfl
  | happly label arguments recurse =>
    intro encoded read instance_ instanceRead name member
    simp only [freeVars, List.mem_flatMap] at member
    obtain ⟨argument, argumentMember, nameMember⟩ := member
    rcases encode_apply_some read with ⟨rfl, _⟩ | ⟨terms, _, encodedArguments, _⟩
    · cases argumentMember
    · obtain ⟨term, _, argumentRead⟩ :=
        forall₂_left ((encodeList_some_iff names arguments terms).mp encodedArguments) argumentMember
      have applied : applyBindings bindings (.apply label arguments) =
          .apply label (arguments.map (applyBindings bindings)) := by
        simp [applyBindings]
      rw [applied] at instanceRead
      have nonempty : arguments.map (applyBindings bindings) ≠ [] := by
        simpa using List.ne_nil_of_mem argumentMember
      rcases encode_apply_some instanceRead with ⟨empty, _⟩ | ⟨instances, _, instancesRead, _⟩
      · exact absurd empty nonempty
      · obtain ⟨argumentInstance, _, argumentInstanceRead⟩ :=
          forall₂_left ((encodeList_some_iff [] _ instances).mp instancesRead)
            (List.mem_map_of_mem argumentMember)
        exact recurse argument argumentMember argumentRead argumentInstanceRead name nameMember
  | _ => intro encoded read; simp [encode] at read

/-- A canonical instance has canonical values. -/
theorem canonical_values (substitution : Subst Labels) :
    ∀ (term : Term Labels), Canonical (substitution.applyTerm term) → ∀ index ∈ term.freeVars, Canonical (substitution index)
  | .var _, canonical, index, member => by
    simp only [Term.freeVars, Finset.mem_singleton] at member
    subst member
    exact canonical
  | .const _, _, _, member => by simp [Term.freeVars] at member
  | .app _ arguments, canonical, index, member => by
    simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at member
    obtain ⟨i, inside⟩ := member
    exact canonical_values substitution (arguments i) (canonical.2 i) index inside

/-- The bindings that read each name's number off a substitution. -/
def bindingsOf (names : List String) (substitution : Subst Labels) : Bindings :=
  names.mapIdx fun index name => (name, decode (substitution index))

theorem lookup_bindingsOf (substitution : Subst Labels) :
    ∀ (names : List String) {name : String} {index : ℕ}, names.idxOf? name = some index →
      lookupOrFvar (bindingsOf names substitution) name = decode (substitution index)
  | [], _, _, found => by simp at found
  | first :: rest, name, index, found => by
    rw [List.idxOf?_cons] at found
    unfold lookupOrFvar bindingsOf
    rw [List.mapIdx_cons]
    by_cases same : first = name
    · subst same
      simp only [beq_self_eq_true, if_true, Option.some.injEq] at found
      subst found
      simp [applyBindings]
    · have different : (first == name) = false := by simpa using same
      rw [different] at found
      simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at found
      obtain ⟨later, laterFound, rfl⟩ := found
      have earlier := lookup_bindingsOf (fun index => substitution (index + 1)) rest laterFound
      unfold lookupOrFvar bindingsOf at earlier
      simp only [applyBindings, List.find?_cons, different] at earlier ⊢
      simpa using earlier

/-- **A Herbrand instance of an encoding is a MeTTaIL instance of the pattern**, by the bindings
read off the substitution, which agrees with them on the encoding's variables. -/
theorem instance_of_encoded {names : List String} {pattern : Pattern} {encoded : Term Labels}
    (read : encode names pattern = some encoded) {state : Pattern} {stateEncoded : Term Labels}
    (stateRead : encode [] state = some stateEncoded) {substitution : Subst Labels}
    (instance_ : substitution.applyTerm encoded = stateEncoded) :
    applyBindings (bindingsOf names substitution) pattern = state ∧
      ∀ index ∈ encoded.freeVars, substOf names (bindingsOf names substitution) index = substitution index := by
  have canonical : ∀ index ∈ encoded.freeVars, Canonical (substitution index) :=
    canonical_values substitution encoded (instance_ ▸ encode_canonical state stateRead)
  have agree : ∀ index ∈ encoded.freeVars, substOf names (bindingsOf names substitution) index = substitution index := by
    intro index member
    obtain ⟨name, _, found⟩ := (encode_freeVars pattern read index).mp member
    rw [substOf_of_found found, lookup_bindingsOf substitution names found, encode_decode _ (canonical index member)]
    rfl
  refine ⟨?_, agree⟩
  apply encode_injective _ stateRead
  rw [encode_applyBindings _ pattern read]
  · rw [Narrowing.Subst.applyTerm_congr agree, instance_]
  · intro name member
    obtain ⟨index, found⟩ := Option.isSome_iff_exists.mp (encode_named pattern read name member)
    have inside : index ∈ encoded.freeVars := (encode_freeVars pattern read index).mpr ⟨name, member, found⟩
    rw [lookup_bindingsOf substitution names found, encode_decode _ (canonical index inside)]
    rfl


theorem encode_ground {pattern : Pattern} {encoded : Term Labels} (read : encode [] pattern = some encoded) :
    BackwardNarrowing.Ground encoded := by
  apply Finset.eq_empty_of_forall_notMem
  intro index member
  obtain ⟨_, _, found⟩ := (encode_freeVars pattern read index).mp member
  simp at found

/-! ## Rules and their steps -/

open Mettapedia.Logic.LP.FirstOrderRewriting (Equation)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch

/-- The metavariables of a rule, each once. -/
def ruleNames (rule : RewriteRule) : List String := (freeVars rule.left ++ freeVars rule.right).dedup

/-- **The Herbrand rule of a first-order rule.** -/
def encodeRule (rule : RewriteRule) : Option (Equation Labels) :=
  match encode (ruleNames rule) rule.left, encode (ruleNames rule) rule.right with
  | some left, some right => some ⟨left, right⟩
  | _, _ => none

theorem encodeRule_some {rule : RewriteRule} {encoded : Equation Labels} (read : encodeRule rule = some encoded) :
    encode (ruleNames rule) rule.left = some encoded.left ∧ encode (ruleNames rule) rule.right = some encoded.right := by
  unfold encodeRule at read
  split at read
  · rename_i left right leftRead rightRead
    cases read
    exact ⟨leftRead, rightRead⟩
  · cases read

/-- The Herbrand rules of a language. -/
def encodeRules (language : LanguageDef) : List (Equation Labels) := language.rewrites.filterMap encodeRule

/-- **The Herbrand profile**: every rule is first-order, and binds every metavariable of its right
side on its left side. -/
structure Profile (language : LanguageDef) : Prop where
  encodable : ∀ rule ∈ language.rewrites, (encodeRule rule).isSome
  bound : ∀ rule ∈ language.rewrites, ∀ name ∈ freeVars rule.right, name ∈ freeVars rule.left

/-- The profile, decided. -/
def profileCheck (language : LanguageDef) : Bool :=
  language.rewrites.all fun rule =>
    (encodeRule rule).isSome && (freeVars rule.right).all fun name => decide (name ∈ freeVars rule.left)

theorem Profile.of_check {language : LanguageDef} (checked : profileCheck language = true) : Profile language where
  encodable rule member := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked rule member)).1
  bound rule member name nameMember := of_decide_eq_true
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked rule member)).2 name nameMember)

/-- The root steps of a language. -/
def languageSpan (language : LanguageDef) : ReductionSpan Pattern where
  Edge := {pair : Pattern × Pattern // pair.2 ∈ rootReducts language pair.1}
  source edge := edge.1.1
  target edge := edge.1.2

theorem languageSpan_diamond (language : LanguageDef) (set : Pattern → Prop) (state : Pattern) :
    derivedDiamond (languageSpan language) set state ↔ ∃ target ∈ rootReducts language state, set target := by
  constructor
  · rintro ⟨⟨⟨source, target⟩, member⟩, rfl, holds⟩
    exact ⟨target, member, holds⟩
  · rintro ⟨target, member, holds⟩
    exact ⟨⟨(state, target), member⟩, rfl, holds⟩

theorem mem_rootReducts {language : LanguageDef} {source target : Pattern} :
    target ∈ rootReducts language source ↔ ∃ rule ∈ language.rewrites, ∃ bindings ∈ matchPattern rule.left source,
      applyBindings bindings rule.right = target := by
  simp [rootReducts, List.mem_flatMap, List.mem_map]

variable {language : LanguageDef}

/-- **A step of the language is a root step of its Herbrand rules.** -/
theorem step_forward (profile : Profile language) {source target : Pattern} {encoded : Term Labels}
    (sourceRead : encode [] source = some encoded) (step : target ∈ rootReducts language source) :
    ∃ targetEncoded, encode [] target = some targetEncoded ∧
      ∃ rule ∈ encodeRules language, ∃ substitution : Subst Labels,
        substitution.applyTerm rule.left = encoded ∧ substitution.applyTerm rule.right = targetEncoded := by
  obtain ⟨rule, ruleMember, bindings, matched, rfl⟩ := mem_rootReducts.mp step
  obtain ⟨herbrand, herbrandRead⟩ := Option.isSome_iff_exists.mp (profile.encodable rule ruleMember)
  obtain ⟨leftRead, rightRead⟩ := encodeRule_some herbrandRead
  have correct : applyBindings bindings rule.left = source :=
    Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_correct matched (encode_isMatchCorrect _ leftRead)
  have values := encode_values bindings rule.left leftRead (correct ▸ sourceRead)
  have leftInstance := encode_applyBindings bindings rule.left leftRead values
  rw [correct, sourceRead] at leftInstance
  have rightInstance := encode_applyBindings bindings rule.right rightRead fun name member =>
    values name (profile.bound rule ruleMember name member)
  exact ⟨_, rightInstance, herbrand, List.mem_filterMap.mpr ⟨rule, ruleMember, herbrandRead⟩,
    substOf (ruleNames rule) bindings, (Option.some.inj leftInstance).symm, rfl⟩

/-- **A root step of the Herbrand rules from a ground encoding is a step of the language.** -/
theorem step_backward (profile : Profile language) {source : Pattern} {encoded : Term Labels}
    (sourceRead : encode [] source = some encoded) {herbrand : Equation Labels}
    (member : herbrand ∈ encodeRules language) {substitution : Subst Labels}
    (instance_ : substitution.applyTerm herbrand.left = encoded) :
    ∃ target, encode [] target = some (substitution.applyTerm herbrand.right) ∧
      target ∈ rootReducts language source := by
  obtain ⟨rule, ruleMember, herbrandRead⟩ := List.mem_filterMap.mp member
  obtain ⟨leftRead, rightRead⟩ := encodeRule_some herbrandRead
  have leftCorrect := encode_isMatchCorrect _ leftRead
  have rightCorrect := encode_isMatchCorrect _ rightRead
  obtain ⟨applied, agree⟩ := instance_of_encoded leftRead sourceRead instance_
  let bindings := bindingsOf (ruleNames rule) substitution
  obtain ⟨matchedBindings, matched, _⟩ :=
    Mettapedia.OSLF.Framework.PredFiniteSufficient.matchPattern_applyBindings_complete (bs := bindings) leftCorrect
  rw [applied] at matched
  have sameLeft : applyBindings matchedBindings rule.left = applyBindings bindings rule.left :=
    (Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_correct matched leftCorrect).trans applied.symm
  have sameRight : applyBindings matchedBindings rule.right = applyBindings bindings rule.right :=
    Mettapedia.OSLF.Framework.PredFiniteSufficient.applyBindings_eq_of_agree_isMatchCorrect rightCorrect
      fun name inside => Mettapedia.OSLF.Framework.PredFiniteSufficient.applyBindings_injective_isMatchCorrect
        leftCorrect sameLeft name (profile.bound rule ruleMember name inside)
  refine ⟨applyBindings matchedBindings rule.right, ?_, mem_rootReducts.mpr ⟨rule, ruleMember, matchedBindings, matched, rfl⟩⟩
  have values := encode_values bindings rule.left leftRead (applied ▸ sourceRead)
  rw [sameRight, encode_applyBindings bindings rule.right rightRead fun name inside =>
    values name (profile.bound rule ruleMember name inside)]
  congr 1
  apply Narrowing.Subst.applyTerm_congr
  intro index inside
  obtain ⟨name, nameMember, found⟩ := (encode_freeVars rule.right rightRead index).mp inside
  exact agree index ((encode_freeVars rule.left leftRead index).mpr
    ⟨name, profile.bound rule ruleMember name nameMember, found⟩)

/-! ## Goals and reachability -/

/-- The metavariables of a goal, each once. -/
def goalNames (goal : Pattern) : List String := (freeVars goal).dedup

/-- The states the goals describe: their instances. -/
def Goal (goals : List Pattern) (state : Pattern) : Prop :=
  ∃ goal ∈ goals, ∃ bindings, applyBindings bindings goal = state

/-- The Herbrand goals. -/
def encodeGoals (goals : List Pattern) : List (Term Labels) :=
  goals.filterMap fun goal => encode (goalNames goal) goal

/-- Every goal is first-order. -/
def goalsCheck (goals : List Pattern) : Bool := goals.all fun goal => (encode (goalNames goal) goal).isSome

variable {goals : List Pattern}

theorem goal_iff (goalsChecked : goalsCheck goals = true) {state : Pattern} {encoded : Term Labels}
    (stateRead : encode [] state = some encoded) :
    Goal goals state ↔ ∃ goal ∈ encodeGoals goals, BackwardNarrowing.Instance goal encoded := by
  constructor
  · rintro ⟨goal, goalMember, bindings, rfl⟩
    obtain ⟨herbrand, herbrandRead⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp goalsChecked goal goalMember)
    have values := encode_values bindings goal herbrandRead stateRead
    have instance_ := encode_applyBindings bindings goal herbrandRead values
    rw [stateRead] at instance_
    exact ⟨herbrand, List.mem_filterMap.mpr ⟨goal, goalMember, herbrandRead⟩, _, (Option.some.inj instance_).symm⟩
  · rintro ⟨herbrand, herbrandMember, substitution, instance_⟩
    obtain ⟨goal, goalMember, herbrandRead⟩ := List.mem_filterMap.mp herbrandMember
    exact ⟨goal, goalMember, _, (instance_of_encoded herbrandRead stateRead instance_).1⟩

/-- **Reaching a goal is reaching its Herbrand goal**, from every ground first-order state. -/
theorem reaches_iff (profile : Profile language) (goalsChecked : goalsCheck goals = true) {state : Pattern}
    {encoded : Term Labels} (stateRead : encode [] state = some encoded) :
    Reaches (languageSpan language) (Goal goals) state ↔
      Reaches (BackwardNarrowing.rootSpan (encodeRules language))
        (fun herbrand => ∃ goal ∈ encodeGoals goals, BackwardNarrowing.Instance goal herbrand) encoded := by
  constructor
  · intro reaches
    induction reaches generalizing encoded with
    | goal atGoal => exact .goal ((goal_iff goalsChecked stateRead).mp atGoal)
    | step event _ ih =>
      obtain ⟨targetEncoded, targetRead, herbrand, member, substitution, leftSide, rightSide⟩ :=
        step_forward profile stateRead event.2
      refine Reaches.step (span := BackwardNarrowing.rootSpan (encodeRules language))
        ⟨(encoded, targetEncoded), herbrand, member, substitution, leftSide, rightSide⟩ ?_
      exact ih targetRead
  · intro reaches
    induction reaches generalizing state with
    | goal atGoal => exact .goal ((goal_iff goalsChecked stateRead).mpr atGoal)
    | step event _ ih =>
      obtain ⟨⟨source, target⟩, herbrand, member, substitution, leftSide, rightSide⟩ := event
      obtain ⟨next, nextRead, step⟩ := step_backward profile stateRead member leftSide
      rw [rightSide] at nextRead
      refine Reaches.step (span := languageSpan language) ⟨(state, next), step⟩ ?_
      exact ih nextRead

/-! ## Answers for MeTTaIL languages -/

/-- **Read a backward search for a MeTTaIL language**, through its Herbrand rules. -/
def answer (language : LanguageDef) (goals : List Pattern)
    (scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Labels)) (fuel : ℕ) (state : Pattern) :
    Presentation.Answer :=
  match encode [] state with
  | some encoded => BackwardNarrowing.rootAnswer (encodeRules language) (encodeGoals goals) scheduler fuel encoded
  | none => .unknown

theorem answer_reaches (profile : Profile language) (goalsChecked : goalsCheck goals = true)
    {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Labels)} {fuel : ℕ} {state : Pattern}
    (read : answer language goals scheduler fuel state = .reaches) : Reaches (languageSpan language) (Goal goals) state := by
  unfold answer at read
  split at read
  · rename_i encoded stateRead
    exact (reaches_iff profile goalsChecked stateRead).mpr (BackwardNarrowing.rootAnswer_reaches read)
  · cases read

theorem answer_cannotReach (profile : Profile language) (goalsChecked : goalsCheck goals = true)
    {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Labels)} {fuel : ℕ} {state : Pattern}
    (read : answer language goals scheduler fuel state = .cannotReach) :
    ¬ Reaches (languageSpan language) (Goal goals) state := by
  unfold answer at read
  split at read
  · rename_i encoded stateRead
    exact fun reaches => BackwardNarrowing.rootAnswer_cannotReach (encode_ground stateRead) read
      ((reaches_iff profile goalsChecked stateRead).mp reaches)
  · cases read

/-! ## The compiled root plans -/

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan RootProfile)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted)

variable {type : TypeExpr}

/-- The steps of the compiled root plan of a language, the semantics GSLT → MeTTa executes. -/
abbrev compiled (language : LanguageDef) (type : TypeExpr) : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.gslt (rootPlan language) [] type

/-- The well-sorted states of the compiled plan. -/
def Sorted (language : LanguageDef) (type : TypeExpr) (pattern : Pattern) : Prop :=
  OpenPatternWellSorted (rootPlan language).snapshot.language (rootPlan language).snapshot.free [] type pattern

/-- Compiled steps keep well-sortedness. -/
theorem sorted_closed (profile : RootProfile language type) :
    ∀ event : (gsltSpan (compiled language type)).Edge,
      Sorted language type ((gsltSpan (compiled language type)).source event) →
        Sorted language type ((gsltSpan (compiled language type)).target event) := by
  intro event _
  change Sorted language type event.target
  obtain ⟨representative, receipt, _, fired, after⟩ := event.step
  rw [← profile.equivalence_is_equality [] after]
  exact Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Receipt.target_sorted (rootPlan language) [] type
    (receipt := ⟨representative, [], receipt⟩) (source := representative) ⟨.nil _, fired⟩

/-- From a well-sorted state, the compiled plan and the authored root steps have the same steps. -/
theorem compiled_steps_agree (profile : RootProfile language type) {source target : Pattern}
    (typed : Sorted language type source) :
    (∃ event : (gsltSpan (compiled language type)).Edge, (gsltSpan (compiled language type)).source event = source ∧
        (gsltSpan (compiled language type)).target event = target) ↔
      ∃ event : (languageSpan language).Edge, (languageSpan language).source event = source ∧
        (languageSpan language).target event = target := by
  constructor
  · rintro ⟨event, rfl, rfl⟩
    exact ⟨⟨(_, _), (profile.general_step_iff_rootReducts [] typed).mp event.step⟩, rfl, rfl⟩
  · rintro ⟨⟨⟨first, second⟩, member⟩, rfl, rfl⟩
    exact ⟨⟨first, second, (profile.general_step_iff_rootReducts [] typed).mpr member⟩, rfl, rfl⟩

/-- Authored root steps from well-sorted states keep them well-sorted. -/
theorem language_sorted_closed (profile : RootProfile language type) :
    ∀ event : (languageSpan language).Edge, Sorted language type ((languageSpan language).source event) →
      Sorted language type ((languageSpan language).target event) := by
  intro event sourceSorted
  obtain ⟨compiledEvent, starts, ends⟩ := (compiled_steps_agree profile sourceSorted).mpr ⟨event, rfl, rfl⟩
  rw [← ends]
  exact sorted_closed profile compiledEvent (starts ▸ sourceSorted)

/-- **From a well-sorted state, the compiled plan reaches what the authored root steps reach.** -/
theorem compiled_reaches_iff (profile : RootProfile language type) {goal : Pattern → Prop} {state : Pattern}
    (typed : Sorted language type state) :
    Reaches (gsltSpan (compiled language type)) goal state ↔ Reaches (languageSpan language) goal state :=
  reaches_transfer (Sorted language type) (sorted_closed profile)
    (fun _ _ sourceTyped => compiled_steps_agree profile sourceTyped) typed

/-- **A `reaches` answer is a fact about the compiled plan.** -/
theorem compiled_reaches (rootProfile : RootProfile language type) (profile : Profile language)
    (goalsChecked : goalsCheck goals = true) {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Labels)}
    {fuel : ℕ} {state : Pattern} (typed : Sorted language type state)
    (read : answer language goals scheduler fuel state = .reaches) :
    Reaches (gsltSpan (compiled language type)) (Goal goals) state :=
  (compiled_reaches_iff rootProfile typed).mpr (answer_reaches profile goalsChecked read)

/-- **A `cannotReach` answer is a fact about the compiled plan.** -/
theorem compiled_cannotReach (rootProfile : RootProfile language type) (profile : Profile language)
    (goalsChecked : goalsCheck goals = true) {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Labels)}
    {fuel : ℕ} {state : Pattern} (typed : Sorted language type state)
    (read : answer language goals scheduler fuel state = .cannotReach) :
    ¬ Reaches (gsltSpan (compiled language type)) (Goal goals) state :=
  fun reaches => answer_cannotReach profile goalsChecked read ((compiled_reaches_iff rootProfile typed).mp reaches)

end Mettapedia.OSLF.Framework.HerbrandBridge
