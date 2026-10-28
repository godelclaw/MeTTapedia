import Mettapedia.Logic.Prolog.ClauseReflection
import Mettapedia.Logic.Prolog.ReaderTerm

namespace Mettapedia.Logic.Prolog.ClauseReflectionRegression

open SourceSignature ReaderOperator ReaderTerm ReaderSource ClauseReflection

def readClause? (source : String) : Option SourceSignature.Clause := do
  let read ← (readOne defaults source).toOption
  let form ← (classify read.term).toOption
  match form with
  | .clause clause => some clause
  | _ => none

def reflects (source : String) : Bool :=
  match readClause? source with
  | none => false
  | some clause => (reflect? clause).isSome

#guard reflects "fact(a)."
#guard reflects "p(X) :- (q(X), ! ; catch(r(X), E, throw(E)))."

/-- Optional provenance is not trusted merely because it is present: changing
the executable body while retaining a valid source term is rejected. -/
def forgedBodyIsRejected : Bool :=
  match readClause? "p(a)." with
  | none => false
  | some clause =>
      let forged := { clause with body := .fail }
      (reflect? forged).isNone

/-- The symmetric forgery is rejected as well: executable content cannot be
paired with source data for a different predicate occurrence. -/
def forgedSourceIsRejected : Bool :=
  match readClause? "p(a).", readClause? "q(a)." with
  | some pClause, some qClause =>
      let forged := { pClause with sourceTerm := qClause.sourceTerm }
      (reflect? forged).isNone
  | _, _ => false

#guard forgedBodyIsRejected
#guard forgedSourceIsRejected

end Mettapedia.Logic.Prolog.ClauseReflectionRegression
