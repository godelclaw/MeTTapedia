import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Native proof combinators for the impredicative logical connectives

Truth, falsity, conjunction, disjunction and existence use only Megalodon's
implication and universal quantification. The actual proof programs import
no known propositions. Their checking equations quantify over the native
environment and the ambient term and proof contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ImpredicativeLogicalProofs

open MathdataKernel

def truth : Tm := .all .prop (.imp (.db 0) (.db 0))
def falsity : Tm := .all .prop (.db 0)

def conjunction (first second : Tm) : Tm :=
  .all .prop (.imp (.imp (Tm.shift 0 1 first) (.imp (Tm.shift 0 1 second) (.db 0))) (.db 0))

def disjunction (first second : Tm) : Tm :=
  .all .prop (.imp (.imp (Tm.shift 0 1 first) (.db 0))
    (.imp (.imp (Tm.shift 0 1 second) (.db 0)) (.db 0)))

def existential (type : Tp) (predicate : Tm) : Tm :=
  .all .prop (.imp (.all type
    (.imp (.app (Tm.shift 0 2 predicate) (.db 0)) (.db 1))) (.db 0))

def truthIntroduction : Pf := .termLam .prop (.proofLam (.db 0) (.hyp 0))

def falsityEliminationStatement : Tm := .all .prop (.imp falsity (.db 0))
def falsityElimination : Pf := .termLam .prop (.proofLam falsity (.termApp (.hyp 0) (.db 0)))

def conjunctionIntroductionStatement : Tm :=
  .all .prop (.all .prop (.imp (.db 1) (.imp (.db 0) (conjunction (.db 1) (.db 0)))))

def conjunctionIntroduction : Pf :=
  .termLam .prop (.termLam .prop (.proofLam (.db 1) (.proofLam (.db 0)
    (.termLam .prop (.proofLam (.imp (.db 2) (.imp (.db 1) (.db 0)))
      (.proofApp (.proofApp (.hyp 0) (.hyp 2)) (.hyp 1)))))))

def conjunctionLeftStatement : Tm :=
  .all .prop (.all .prop (.imp (conjunction (.db 1) (.db 0)) (.db 1)))
def conjunctionLeft : Pf :=
  .termLam .prop (.termLam .prop (.proofLam (conjunction (.db 1) (.db 0))
    (.proofApp (.termApp (.hyp 0) (.db 1)) (.proofLam (.db 1) (.proofLam (.db 0) (.hyp 1))))))

def conjunctionRightStatement : Tm :=
  .all .prop (.all .prop (.imp (conjunction (.db 1) (.db 0)) (.db 0)))
def conjunctionRight : Pf :=
  .termLam .prop (.termLam .prop (.proofLam (conjunction (.db 1) (.db 0))
    (.proofApp (.termApp (.hyp 0) (.db 0)) (.proofLam (.db 1) (.proofLam (.db 0) (.hyp 0))))))

def disjunctionLeftStatement : Tm :=
  .all .prop (.all .prop (.imp (.db 1) (disjunction (.db 1) (.db 0))))
def disjunctionLeft : Pf :=
  .termLam .prop (.termLam .prop (.proofLam (.db 1)
    (.termLam .prop (.proofLam (.imp (.db 2) (.db 0))
      (.proofLam (.imp (.db 1) (.db 0)) (.proofApp (.hyp 1) (.hyp 2)))))))

def disjunctionRightStatement : Tm :=
  .all .prop (.all .prop (.imp (.db 0) (disjunction (.db 1) (.db 0))))
def disjunctionRight : Pf :=
  .termLam .prop (.termLam .prop (.proofLam (.db 0)
    (.termLam .prop (.proofLam (.imp (.db 2) (.db 0))
      (.proofLam (.imp (.db 1) (.db 0)) (.proofApp (.hyp 0) (.hyp 2)))))))

def disjunctionEliminationStatement : Tm :=
  .all .prop (.all .prop (.all .prop
    (.imp (disjunction (.db 2) (.db 1))
      (.imp (.imp (.db 2) (.db 0)) (.imp (.imp (.db 1) (.db 0)) (.db 0))))))
def disjunctionElimination : Pf :=
  .termLam .prop (.termLam .prop (.termLam .prop
    (.proofLam (disjunction (.db 2) (.db 1))
      (.proofLam (.imp (.db 2) (.db 0)) (.proofLam (.imp (.db 1) (.db 0))
        (.proofApp (.proofApp (.termApp (.hyp 2) (.db 0)) (.hyp 1)) (.hyp 0)))))))

def existentialIntroductionStatement (type : Tp) : Tm :=
  .all (.arr type .prop) (.all type
    (.imp (.app (.db 1) (.db 0)) (existential type (.db 1))))
def existentialIntroduction (type : Tp) : Pf :=
  .termLam (.arr type .prop) (.termLam type (.proofLam (.app (.db 1) (.db 0))
    (.termLam .prop (.proofLam (.all type (.imp (.app (.db 3) (.db 0)) (.db 1)))
      (.proofApp (.termApp (.hyp 0) (.db 1)) (.hyp 1))))))

def existentialEliminationStatement (type : Tp) : Tm :=
  .all (.arr type .prop) (.all .prop
    (.imp (existential type (.db 1))
      (.imp (.all type (.imp (.app (.db 2) (.db 0)) (.db 1))) (.db 0))))
def existentialElimination (type : Tp) : Pf :=
  .termLam (.arr type .prop) (.termLam .prop
    (.proofLam (existential type (.db 1))
      (.proofLam (.all type (.imp (.app (.db 2) (.db 0)) (.db 1)))
        (.proofApp (.termApp (.hyp 1) (.db 0)) (.hyp 0)))))

theorem truthIntroduction_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses truthIntroduction = some truth := by
  simp [truthIntroduction, truth, inferProof, inferTerm, Tp.plainWellFormed,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne]

theorem falsityElimination_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses falsityElimination = some falsityEliminationStatement := by
  simp [falsityElimination, falsityEliminationStatement, falsity, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt]

theorem conjunctionIntroduction_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses conjunctionIntroduction = some conjunctionIntroductionStatement := by
  simp [conjunctionIntroduction, conjunctionIntroductionStatement, conjunction, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift]

theorem conjunctionLeft_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses conjunctionLeft = some conjunctionLeftStatement := by
  simp [conjunctionLeft, conjunctionLeftStatement, conjunction, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt]

theorem conjunctionRight_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses conjunctionRight = some conjunctionRightStatement := by
  simp [conjunctionRight, conjunctionRightStatement, conjunction, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt]

theorem disjunctionLeft_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses disjunctionLeft = some disjunctionLeftStatement := by
  simp [disjunctionLeft, disjunctionLeftStatement, disjunction, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift]

theorem disjunctionRight_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses disjunctionRight = some disjunctionRightStatement := by
  simp [disjunctionRight, disjunctionRightStatement, disjunction, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift]

theorem disjunctionElimination_infers (environment : Environment) (depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses disjunctionElimination = some disjunctionEliminationStatement := by
  simp [disjunctionElimination, disjunctionEliminationStatement, disjunction, inferProof, inferTerm,
    Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt]

theorem existentialIntroduction_infers (environment : Environment) (depth : Nat)
    (type : Tp) (formed : type.plainWellFormed depth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses (existentialIntroduction type) = some (existentialIntroductionStatement type) := by
  simp [existentialIntroduction, existentialIntroductionStatement, existential, inferProof, inferTerm,
    Tp.plainWellFormed, formed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift,
    Tm.instantiate, Tm.instantiateAt]

theorem existentialElimination_infers (environment : Environment) (depth : Nat)
    (type : Tp) (formed : type.plainWellFormed depth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 depth terms hypotheses (existentialElimination type) = some (existentialEliminationStatement type) := by
  simp [existentialElimination, existentialEliminationStatement, existential, inferProof, inferTerm,
    Tp.plainWellFormed, formed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift,
    Tm.instantiate, Tm.instantiateAt]

end Mettapedia.Languages.Megalodon.ImpredicativeLogicalProofs
