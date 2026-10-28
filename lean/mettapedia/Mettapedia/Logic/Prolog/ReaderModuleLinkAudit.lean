import Mettapedia.Logic.Prolog.ReaderModuleLink

/-!
# Trusted-base audit for static module forwarding

The forwarding-clause laws pin both endpoints and the absence of fabricated
source provenance.  Runtime execution remains ordinary canonical clause
selection.
-/

#print axioms Mettapedia.Logic.Prolog.ReaderModuleLink.moduleAliasClause_head_symbol
#print axioms Mettapedia.Logic.Prolog.ReaderModuleLink.moduleAliasClause_body_symbol
#print axioms Mettapedia.Logic.Prolog.ReaderModuleLink.moduleAliasClause_sourceTerm
