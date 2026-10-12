import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory

/-!
# Private identities over dependent telescopes

Names have an identity and a presentation. Lookup uses the identity only.
The finite frame is constructed from the authored telescope; its translation
forgets presentations and identities after resolving their positions. Formation
is checked before that translation, and includes distinct private identities.
This is a scope-resolved mathematical interface, not a runtime reader model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace PrivateIdentityContexts

open Presentation

structure Name where
  identity : Nat
  spelling : String
  deriving DecidableEq, Repr

abbrev Frame (n : Nat) := Fin n → Name

def Frame.extend {n : Nat} (frame : Frame n) (name : Name) : Frame (n + 1) :=
  Fin.cases name frame

def Frame.tail {n : Nat} (frame : Frame (n + 1)) : Frame n :=
  fun index => frame index.succ

def Frame.Distinct {n : Nat} (frame : Frame n) : Prop :=
  Function.Injective (fun index => (frame index).identity)

def Frame.Fresh {n : Nat} (frame : Frame n) (name : Name) : Prop :=
  ∀ index, (frame index).identity ≠ name.identity

theorem Frame.distinct_extend {n : Nat} {frame : Frame n} {name : Name}
    (distinct : frame.Distinct) (fresh : frame.Fresh name) :
    (frame.extend name).Distinct := by
  intro left right
  refine Fin.cases ?_ ?_ left
  · refine Fin.cases ?_ ?_ right
    · intro _; rfl
    · intro old same
      exact False.elim (fresh old same.symm)
  · intro old
    refine Fin.cases ?_ ?_ right
    · intro same; exact False.elim (fresh old same)
    · intro prior same
      exact congrArg Fin.succ (distinct same)

theorem Frame.distinct_tail {n : Nat} {frame : Frame (n + 1)}
    (distinct : frame.Distinct) : frame.tail.Distinct := by
  intro left right same
  exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val (distinct same)))

def resolve : {n : Nat} → Frame n → Nat → Option (Fin n)
  | 0, _, _ => none
  | _ + 1, frame, key =>
      if (frame 0).identity = key then some 0
      else (resolve frame.tail key).map Fin.succ

theorem resolve_sound : ∀ {n : Nat} (frame : Frame n) (key : Nat) (index : Fin n),
    resolve frame key = some index → (frame index).identity = key
  | 0, _, _, index, _ => nomatch index
  | n + 1, frame, key, index, found => by
      unfold resolve at found
      split at found
      · next same =>
        have atZero : index = 0 := (Option.some.inj found).symm
        subst index
        exact same
      · next different =>
        cases tailFound : resolve frame.tail key with
        | none => simp [tailFound] at found
        | some old =>
          have atOld : old.succ = index := by simpa [tailFound] using found
          subst index
          exact resolve_sound frame.tail key old tailFound

theorem resolve_complete : ∀ {n : Nat} (frame : Frame n), frame.Distinct →
    ∀ index, resolve frame (frame index).identity = some index
  | 0, _, _, index => nomatch index
  | n + 1, frame, distinct, index => by
      refine Fin.cases ?_ ?_ index
      · simp [resolve]
      · intro old
        have different : (frame 0).identity ≠ (frame old.succ).identity := by
          intro same
          have impossible := distinct same
          exact Fin.succ_ne_zero old impossible.symm
        simp only [resolve, if_neg different]
        change (resolve frame.tail (frame.tail old).identity).map Fin.succ = some old.succ
        rw [resolve_complete frame.tail (Frame.distinct_tail distinct) old]
        rfl

theorem resolve_absent {n : Nat} (frame : Frame n) (key : Nat)
    (absent : ∀ index, (frame index).identity ≠ key) : resolve frame key = none := by
  cases found : resolve frame key with
  | none => rfl
  | some index => exact False.elim (absent index (resolve_sound frame key index found))

def Frame.mapKeys {n : Nat} (frame : Frame n) (map : Nat → Nat) : Frame n :=
  fun index => ⟨map (frame index).identity, (frame index).spelling⟩

theorem Frame.distinct_mapKeys {n : Nat} {frame : Frame n} (distinct : frame.Distinct)
    (map : Nat → Nat) (injective : Function.Injective map) :
    (frame.mapKeys map).Distinct := by
  intro left right same
  exact distinct (injective same)

theorem resolve_mapKeys : ∀ {n : Nat} (frame : Frame n) (map : Nat → Nat),
    Function.Injective map → ∀ key,
      resolve (frame.mapKeys map) (map key) = resolve frame key
  | 0, _, _, _, _ => rfl
  | n + 1, frame, map, injective, key => by
      change (if map (frame 0).identity = map key then some 0 else
        (resolve (frame.tail.mapKeys map) (map key)).map Fin.succ) = _
      simp only [injective.eq_iff, resolve_mapKeys frame.tail map injective key]
      rfl

theorem resolve_spelling_independent {n : Nat} (first second : Frame n)
    (same : ∀ index, (first index).identity = (second index).identity) (key : Nat) :
    resolve first key = resolve second key := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [resolve, same 0]
      rw [ih first.tail second.tail (fun index => same index.succ)]

def Frame.bound : {n : Nat} → Frame n → Nat
  | 0, _ => 0
  | _ + 1, frame => max ((frame 0).identity + 1) frame.tail.bound

theorem Frame.identity_lt_bound : ∀ {n : Nat} (frame : Frame n) (index : Fin n),
    (frame index).identity < frame.bound
  | 0, _, index => nomatch index
  | n + 1, frame, index => by
      refine Fin.cases ?_ ?_ index
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · intro old
        exact Nat.lt_of_lt_of_le (Frame.identity_lt_bound frame.tail old)
          (Nat.le_max_right _ _)

def Frame.freshName {n : Nat} (frame : Frame n) (spelling : String) : Name :=
  ⟨frame.bound, spelling⟩

theorem Frame.freshName_fresh {n : Nat} (frame : Frame n) (spelling : String) :
    frame.Fresh (frame.freshName spelling) := by
  intro index same
  exact Nat.ne_of_lt (frame.identity_lt_bound index) same

inductive Context (Head : Type) : Nat → Type where
  | nil : Context Head 0
  | snoc {n : Nat} : Context Head n → Name → Tm Head n → Context Head (n + 1)

def Context.erase {Head : Type} : {n : Nat} → Context Head n → Ctx Head n
  | _, .nil => .nil
  | _, .snoc context _ type => .snoc context.erase type

def Context.frame {Head : Type} : {n : Nat} → Context Head n → Frame n
  | _, .nil => Fin.elim0
  | _, .snoc context name _ => context.frame.extend name

inductive WellFormed {Head : Type} (rules : Rules Head) :
    {n : Nat} → Context Head n → Prop where
  | nil : WellFormed rules .nil
  | snoc {n : Nat} {context : Context Head n} {name : Name} {type : Tm Head n} {level : Head} :
      WellFormed rules context → context.frame.Fresh name →
      FormationSensitive.Typing rules context.erase type (.head level) → rules.isUniverse level →
      WellFormed rules (.snoc context name type)

theorem WellFormed.distinct {Head : Type} {rules : Rules Head} {n : Nat}
    {context : Context Head n} (formed : WellFormed rules context) : context.frame.Distinct := by
  induction formed with
  | nil => intro index; exact Fin.elim0 index
  | snoc _ fresh _ _ ih => exact Frame.distinct_extend ih fresh

theorem WellFormed.erase {Head : Type} {rules : Rules Head} {n : Nat}
    {context : Context Head n} (formed : WellFormed rules context) :
    FormationSensitive.ContextFormation rules context.erase := by
  induction formed with
  | nil => exact .nil
  | snoc _ _ type level ih => exact .snoc ih type level

def translateContext {Head : Type} {rules : Rules Head} {n : Nat}
    (context : Context Head n) (formed : WellFormed rules context) :
    FormationSensitiveContextual.Context rules := ⟨n, context.erase, formed.erase⟩

def Context.rekey {Head : Type} (map : Nat → Nat) :
    {n : Nat} → Context Head n → Context Head n
  | _, .nil => .nil
  | _, .snoc context name type =>
      .snoc (context.rekey map) ⟨map name.identity, name.spelling⟩ type

@[simp] theorem Context.erase_rekey {Head : Type} {n : Nat} (context : Context Head n)
    (map : Nat → Nat) : (context.rekey map).erase = context.erase := by
  induction context with
  | nil => rfl
  | snoc context name type ih => simp only [rekey, erase, ih]

theorem Context.frame_rekey {Head : Type} {n : Nat} (context : Context Head n)
    (map : Nat → Nat) : (context.rekey map).frame = context.frame.mapKeys map := by
  induction context with
  | nil => funext index; exact Fin.elim0 index
  | snoc context name type ih =>
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro old
        exact congrFun ih old

theorem WellFormed.rekey {Head : Type} {rules : Rules Head} {n : Nat}
    {context : Context Head n} (formed : WellFormed rules context)
    (map : Nat → Nat) (injective : Function.Injective map) :
    WellFormed rules (context.rekey map) := by
  induction formed with
  | nil => exact .nil
  | @snoc n context name type level _ fresh typed universeWitness ih =>
      apply WellFormed.snoc ih
      · intro index same
        rw [Context.frame_rekey] at same
        exact fresh index (injective same)
      · simpa only [Context.erase_rekey] using typed
      · exact universeWitness

/-- Import an already scoped telescope with independently allocated private
identities. Repeated presentation strings never identify its declarations. -/
def Context.ofCore {Head : Type} : {n : Nat} → Ctx Head n → Context Head n
  | _, .nil => .nil
  | _, .snoc context type =>
      let prior := Context.ofCore context
      .snoc prior (prior.frame.freshName "dependency") type

@[simp] theorem Context.erase_ofCore {Head : Type} {n : Nat} (context : Ctx Head n) :
    (Context.ofCore context).erase = context := by
  induction context with
  | nil => rfl
  | snoc context type ih => simp only [ofCore, erase, ih]

theorem Context.ofCore_formed {Head : Type} {rules : Rules Head} {n : Nat}
    {context : Ctx Head n} (formed : FormationSensitive.ContextFormation rules context) :
    WellFormed rules (Context.ofCore context) := by
  induction formed with
  | nil => exact .nil
  | @snoc n context type level _ typeFormed universeWitness ih =>
      exact .snoc ih ((Context.ofCore context).frame.freshName_fresh "dependency")
        (by simpa only [Context.erase_ofCore] using typeFormed) universeWitness

namespace Controls

def repeatedSpelling : Frame 2 := Fin.cases ⟨7, "x"⟩ (fun _ => ⟨4, "x"⟩)

theorem same_printed_name : (repeatedSpelling 0).spelling = (repeatedSpelling 1).spelling := rfl

theorem newest_identity_resolves : resolve repeatedSpelling 7 = some 0 := by decide

theorem older_identity_resolves : resolve repeatedSpelling 4 = some 1 := by decide

theorem spelling_does_not_capture : resolve repeatedSpelling 5 = none := by decide

theorem identity_collapse_is_not_distinct :
    ¬ (repeatedSpelling.mapKeys (fun _ => 0)).Distinct := by
  intro distinct
  have impossible : (0 : Fin 2) = 1 := distinct (a₁ := 0) (a₂ := 1) rfl
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

end Controls

end PrivateIdentityContexts
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
