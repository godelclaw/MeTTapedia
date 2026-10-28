import Mettapedia.Logic.Prolog.Prolog

/-!
# Prolog over the shared logic-programming runtime

The typed source reader, control language and executable services extend the
canonical `Logic.LP` graph runtime. Its pure definite-clause fragment has a
scoped-SLD and least-Herbrand-model soundness theorem. Additional control and
host operations retain their own proof and compatibility boundaries, recorded
with source provenance under `Logic/Prolog/SWI`.
-/
