import Mettapedia.Logic.Prolog.RuntimeClauseDecode

/-!
# Dynamic clause-decoder trusted-base audit

These commands keep the support-indexed variable-copy and real-heap
round-trip dependencies visible in normal build output.
-/

#print axioms Mettapedia.Logic.Prolog.RuntimeClauseDecode.copiedVariable_occurrence_lt
#print axioms Mettapedia.Logic.Prolog.RuntimeClauseDecode.copiedVariable_eq_iff
#print axioms Mettapedia.Logic.Prolog.RuntimeClauseDecode.classifyClause_sourceTerm_present
#print axioms Mettapedia.Logic.Prolog.RuntimeClauseDecode.decodeClause_of_materialize
#print axioms Mettapedia.Logic.Prolog.ReaderSource.classify_normalizedClauseTerm
#print axioms Mettapedia.Logic.Prolog.ReaderSource.classify_clause_sourceTerm_present
