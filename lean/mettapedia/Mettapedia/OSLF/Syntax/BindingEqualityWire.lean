import Mettapedia.OSLF.Syntax.BindingEqualityCertificates
import Mettapedia.OSLF.Syntax.BindingWireCodec

/-!
# Raw finite evidence for binding-signature equality

The existing sorted term decoder checks variables, operator result sorts and
complete binder spines. This layer uses it for the finite substitution and
metavariable tables in equality evidence. The equation environment is retained
by the checker; a packet supplies an index into that environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EqualityCertificates.Wire

open WireCodec

variable {S : Signature} [DecidableEq S.Srt]
variable (sorts : Codec S.Srt) (operators : Codec (Σ sort : S.Srt, S.Op sort))

def putSubstitution : {source target : Ctx S} → Substitution S source target → Data
  | _, _, .nil => .atom 0
  | _, _, .cons head tail => .pair (putTerm operators head) (putSubstitution tail)

def getSubstitution (target : Ctx S) : (source : Ctx S) → Data →
    Option (Substitution S source target)
  | [], .atom 0 => some .nil
  | sort :: rest, .pair head tail => do
      return .cons (← getTerm operators target sort head) (← getSubstitution target rest tail)
  | _, _ => none

theorem get_putSubstitution : ∀ {source target : Ctx S}
    (substitution : Substitution S source target),
    getSubstitution operators target source (putSubstitution operators substitution) =
      some substitution
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [putSubstitution, getSubstitution, get_putTerm,
        get_putSubstitution tail, Bind.bind, Option.bind]
      rfl

def putBodies : {ambient : Ctx S} → {metas : List (MetaArity S)} →
    Bodies S ambient metas → Data
  | _, _, .nil => .atom 0
  | _, _, .cons head tail => .pair (putTerm operators head) (putBodies tail)

def getBodies (ambient : Ctx S) : (metas : List (MetaArity S)) → Data →
    Option (Bodies S ambient metas)
  | [], .atom 0 => some .nil
  | (bound, sort) :: rest, .pair head tail => do
      return .cons (← getTerm operators (bound ++ ambient) sort head)
        (← getBodies ambient rest tail)
  | _, _ => none

theorem get_putBodies : ∀ {ambient : Ctx S} {metas : List (MetaArity S)}
    (bodies : Bodies S ambient metas),
    getBodies operators ambient metas (putBodies operators bodies) = some bodies
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [putBodies, getBodies, get_putTerm, get_putBodies tail, Bind.bind, Option.bind]
      rfl

variable {metas : List (MetaArity S)} (equations : List (EqAxiom S metas))

abbrev Packed := Σ context : Ctx S, Σ sort : S.Srt, Certificate S metas equations context sort

def atIndex (context : Ctx S) (sort : S.Srt) : Packed equations →
    Option (Certificate S metas equations context sort)
  | ⟨foundContext, foundSort, proof⟩ =>
      if sameContext : foundContext = context then
        if sameSort : foundSort = sort then
          some (sameSort ▸ sameContext ▸ proof)
        else none
      else none

@[simp] theorem atIndex_self {context : Ctx S} {sort : S.Srt}
    (proof : Certificate S metas equations context sort) :
    atIndex equations context sort ⟨context, sort, proof⟩ = some proof := by
  simp only [atIndex, dite_true]

mutual

def putCertificate : {context : Ctx S} → {sort : S.Srt} →
    Certificate S metas equations context sort → Data
  | context, _, .axiom (Θ := ambient) index bodies ambientSub ordinarySub =>
      .pair (.atom 0) (.pair (.atom index.val)
        (.pair ((Codec.list sorts).put ambient)
          (.pair ((Codec.list sorts).put context)
            (.pair (putBodies operators bodies)
              (.pair (putSubstitution operators ambientSub) (putSubstitution operators ordinarySub))))))
  | context, sort, .refl term =>
      .pair (.atom 1) (.pair ((Codec.list sorts).put context)
        (.pair (sorts.put sort) (putTerm operators term)))
  | _, _, .symm proof => .pair (.atom 2) (putCertificate proof)
  | _, _, .trans first second =>
      .pair (.atom 3) (.pair (putCertificate first) (putCertificate second))
  | context, sort, .cong operator arguments =>
      .pair (.atom 4) (.pair ((Codec.list sorts).put context)
        (.pair (operators.put ⟨sort, operator⟩) (putArguments arguments)))
  | context, _, .substitute substitution proof =>
      .pair (.atom 5) (.pair ((Codec.list sorts).put context)
        (.pair (putSubstitution operators substitution) (putCertificate proof)))

def putArguments : {arity : List (List S.Srt × S.Srt)} → {context : Ctx S} →
    ArgumentCertificates S metas equations arity context → Data
  | _, _, .nil => .atom 0
  | _, _, .cons head tail => .pair (putCertificate head) (putArguments tail)

end

mutual

def getCertificate : Data → Option (Packed equations)
  | .pair (.atom 0) (.pair (.atom index)
      (.pair ambientWire (.pair contextWire (.pair bodiesWire (.pair ambientSubWire ordinarySubWire))))) => do
      let index ← (Codec.fin equations.length).get (.atom index)
      let ambient ← (Codec.list sorts).get ambientWire
      let context ← (Codec.list sorts).get contextWire
      let bodies ← getBodies operators ambient metas bodiesWire
      let ambientSub ← getSubstitution operators context ambient ambientSubWire
      let ordinarySub ← getSubstitution operators context (equations.get index).ctx ordinarySubWire
      return ⟨context, (equations.get index).sort, .axiom index bodies ambientSub ordinarySub⟩
  | .pair (.atom 1) (.pair contextWire (.pair sortWire termWire)) => do
      let context ← (Codec.list sorts).get contextWire
      let sort ← sorts.get sortWire
      let term ← getTerm operators context sort termWire
      return ⟨context, sort, .refl term⟩
  | .pair (.atom 2) proofWire => do
      let ⟨context, sort, proof⟩ ← getCertificate proofWire
      return ⟨context, sort, .symm proof⟩
  | .pair (.atom 3) (.pair firstWire secondWire) => do
      let ⟨context, sort, first⟩ ← getCertificate firstWire
      let second ← atIndex equations context sort (← getCertificate secondWire)
      return ⟨context, sort, .trans first second⟩
  | .pair (.atom 4) (.pair contextWire (.pair operatorWire argumentsWire)) => do
      let context ← (Codec.list sorts).get contextWire
      let ⟨sort, operator⟩ ← operators.get operatorWire
      let arguments ← getArguments context (S.arity operator) argumentsWire
      return ⟨context, sort, .cong operator arguments⟩
  | .pair (.atom 5) (.pair contextWire (.pair substitutionWire proofWire)) => do
      let target ← (Codec.list sorts).get contextWire
      let ⟨source, sort, proof⟩ ← getCertificate proofWire
      let substitution ← getSubstitution operators target source substitutionWire
      return ⟨target, sort, .substitute substitution proof⟩
  | _ => none

def getArguments (context : Ctx S) (arity : List (List S.Srt × S.Srt)) : Data →
    Option (ArgumentCertificates S metas equations arity context)
  | .atom 0 => match arity with | [] => some .nil | _ => none
  | .pair headWire tailWire => match arity with
      | [] => none
      | (bound, sort) :: rest => do
          let head ← atIndex equations (bound ++ context) sort (← getCertificate headWire)
          let tail ← getArguments context rest tailWire
          return .cons head tail
  | _ => none

end

mutual

theorem get_putCertificate : ∀ {context : Ctx S} {sort : S.Srt}
    (proof : Certificate S metas equations context sort),
    getCertificate sorts operators equations (putCertificate sorts operators equations proof) =
      some ⟨context, sort, proof⟩
  | _, _, .axiom index bodies ambientSub ordinarySub => by
      simp only [putCertificate, getCertificate, Codec.fin, Codec.mapped,
        Codec.nat, index.isLt, dite_true, Codec.get_put,
        get_putBodies, get_putSubstitution, Bind.bind, Option.bind]
      rfl
  | _, _, .refl term => by
      simp only [putCertificate, getCertificate, Codec.get_put, get_putTerm,
        Bind.bind, Option.bind]
      rfl
  | _, _, .symm proof => by
      simp only [putCertificate, getCertificate, get_putCertificate proof, Bind.bind, Option.bind]
      rfl
  | _, _, .trans first second => by
      simp only [putCertificate, getCertificate, get_putCertificate first,
        get_putCertificate second, atIndex_self, Bind.bind, Option.bind]
      rfl
  | _, _, .cong operator arguments => by
      simp only [putCertificate, getCertificate, Codec.get_put, get_putArguments,
        Bind.bind, Option.bind]
      rfl
  | _, _, .substitute substitution proof => by
      simp only [putCertificate, getCertificate, Codec.get_put, get_putCertificate proof,
        get_putSubstitution, Bind.bind, Option.bind]
      rfl

theorem get_putArguments : ∀ {arity : List (List S.Srt × S.Srt)} {context : Ctx S}
    (arguments : ArgumentCertificates S metas equations arity context),
    getArguments sorts operators equations context arity
      (putArguments sorts operators equations arguments) = some arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [putArguments, getArguments, get_putCertificate head,
        get_putArguments tail, atIndex_self, Bind.bind, Option.bind]
      rfl

end

def certificate (context : Ctx S) (sort : S.Srt) :
    Codec (Certificate S metas equations context sort) where
  put := putCertificate sorts operators equations
  get raw := (getCertificate sorts operators equations raw).bind (atIndex equations context sort)
  get_put proof := by simp only [get_putCertificate, Option.bind_some, atIndex_self]

variable [∀ sort : S.Srt, DecidableEq (S.Op sort)]

/-- Reject malformed and noncanonical packets before the existing semantic
equality replay. All declaration and equation identities come from the
retained environment and codecs. -/
def check {context : Ctx S} {sort : S.Srt} (raw : Data)
    (left right : Term S context sort) : Bool :=
  match (certificate sorts operators equations context sort).canonicalGet raw with
  | none => false
  | some proof => EqualityCertificates.check proof left right

theorem check_exact {context : Ctx S} {sort : S.Srt} (raw : Data)
    (left right : Term S context sort) :
    check sorts operators equations raw left right = true ↔
      ∃ proof : Certificate S metas equations context sort,
        putCertificate sorts operators equations proof = raw ∧
          EqualityCertificates.check proof left right = true := by
  let codec := certificate sorts operators equations context sort
  change (match codec.canonicalGet raw with
    | none => false
    | some proof => EqualityCertificates.check proof left right) = true ↔ _
  cases decoded : codec.canonicalGet raw with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨proof, encoded, _⟩
        have recovered := codec.canonicalGet_put proof
        change codec.canonicalGet (putCertificate sorts operators equations proof) = some proof at recovered
        rw [encoded, decoded] at recovered
        cases recovered
  | some proof =>
      constructor
      · intro valid
        exact ⟨proof, codec.put_of_canonicalGet raw proof decoded, valid⟩
      · rintro ⟨candidate, encoded, valid⟩
        have recovered := codec.canonicalGet_put candidate
        change codec.canonicalGet (putCertificate sorts operators equations candidate) = some candidate at recovered
        rw [encoded, decoded] at recovered
        cases Option.some.inj recovered
        exact valid

theorem check_sound {context : Ctx S} {sort : S.Srt} (raw : Data)
    (left right : Term S context sort)
    (accepted : check sorts operators equations raw left right = true) : EqClosure equations left right := by
  obtain ⟨proof, _, valid⟩ := (check_exact sorts operators equations raw left right).mp accepted
  exact EqualityCertificates.check_sound proof left right valid

/-- Complete finite wire evidence for the independently generated equality,
including the full contextual metavariable and simultaneous-substitution rules. -/
theorem check_complete {context : Ctx S} {sort : S.Srt}
    (left right : Term S context sort) :
    EqClosure equations left right ↔ ∃ raw : Data,
      check sorts operators equations raw left right = true := by
  constructor
  · intro derived
    obtain ⟨proof, accepted⟩ := (EqualityCertificates.check_complete left right).mp derived
    exact ⟨putCertificate sorts operators equations proof,
      (check_exact sorts operators equations _ _ _).mpr ⟨proof, rfl, accepted⟩⟩
  · rintro ⟨raw, accepted⟩
    exact check_sound sorts operators equations raw left right accepted

end Mettapedia.OSLF.Binding.EqualityCertificates.Wire
