; Ordered live syntax state for textual MM0.
;
; A source file is runtime data.  Sort, term, delimiter, and simple-notation
; declarations update one explicit prefix state in source order; later
; declarations cannot affect the interpretation of earlier math strings.

(gslt-presentation-v1 MM0NotationEnvironmentV1
  (signature
    (operator cp 1)
    (operator node 2)
    (operator pair 2)
    (operator cons 2)
    (operator different 2)
    (operator NatSuccV1 1)
    (operator MM0IdentifierScalarsV1 2)
    (operator MM0MathClassEntryV1 2)
    (operator MM0MathClassTableConsV1 2)
    (operator MM0MathScalarsConsV1 2)
    (operator MM0MathScalarsFromListV1 2)
    (operator MM0DelimiterCharactersFoldV1 4)
    (operator MM0SecondaryLexV1 3)

    (operator MM0PrecedenceFromAstV1 2)
    (operator MM0FinitePrecedenceV1 1)
    (operator MM0ListLengthV1 2)
    (operator MM0MathTokenListLengthV1 2)

    (operator MM0TermEntryV1 4)
    (operator MM0DeclarationEntriesConsV1 2)
    (operator MM0TermSignatureV1 2)
    (operator MM0TermSignatureLookupV1 3)
    (operator MM0TermSignatureFoundV1 2)

    (operator MM0NotationEnvironmentV1 4)
    (operator MM0ConstantEntryV1 3)
    (operator MM0ConstantEntriesConsV1 2)
    (operator MM0ConstantLookupV1 3)
    (operator MM0ConstantFoundV1 2)
    (operator MM0ConstantEntriesAppendV1 3)
    (operator MM0PrefixNotationEntryV1 5)
    (operator MM0PrefixEntriesConsV1 2)
    (operator MM0PrefixLookupV1 3)
    (operator MM0PrefixFoundV1 1)
    (operator MM0PrefixEntriesAppendV1 3)
    (operator MM0InfixNotationEntryV1 5)
    (operator MM0InfixEntriesConsV1 2)
    (operator MM0InfixLookupV1 3)
    (operator MM0InfixFoundV1 1)
    (operator MM0InfixEntriesAppendV1 3)

    (operator MM0SimpleNotationStatementV1 5)
    (operator MM0InfixNotationKindV1 1)
    (operator MM0NotationConstantV1 3)
    (operator MM0NotationConstantClassV1 3)
    (operator MM0NotationTokenAllowedV1 2)
    (operator MM0CheckAcceptedV1 1)
    (operator MM0CheckRefusedV1 1)
    (operator MM0PrepareSimpleNotationV1 8)
    (operator MM0PreparePrefixAfterConstantV1 7)
    (operator MM0PrepareInfixAfterArityV1 8)
    (operator MM0PrepareInfixAfterConstantV1 6)
    (operator MM0PreparedSimpleNotationV1 3)
    (operator MM0InstallSimpleNotationV1 5)
    (operator MM0InstallPrefixFromLookupsV1 6)
    (operator MM0InstallInfixFromLookupsV1 6)

    (operator MM0NotationStepV1 5)
    (operator MM0NotationStepAcceptedV1 2)
    (operator MM0NotationStepRefusedV1 3)
    (operator MM0NotationStepAfterTermLookupV1 8)
    (operator MM0NotationStepAfterPrepareV1 4)
    (operator MM0DeclaredDelimitersV1 2)
    (operator MM0DeclaredSimpleNotationV1 4)
    (operator MM0RefusedUnknownNotationTermV1 2)
    (operator MM0RefusedInfixArityV1 3)
    (operator MM0RefusedInfixMaximumPrecedenceV1 2)
    (operator MM0RefusedNotationConstantTokenCountV1 2)
    (operator MM0RefusedNotationParenthesisV1 2)
    (operator MM0RefusedNotationPrecedenceConflictV1 4)
    (operator MM0RefusedNotationRedeclarationV1 3)

    (operator MM0TextualEnvironmentV1 2)
    (operator MM0TextualStepV1 4)
    (operator MM0TextualStepAcceptedV1 2)
    (operator MM0TextualStepRefusedV1 3)
    (operator MM0SourceStateV1 2)
    (operator MM0StatementClassV1 2)
    (operator MM0SourceStepV1 4)
    (operator MM0SourceStepByClassV1 5)
    (operator MM0SourceStepAcceptedV1 2)
    (operator MM0SourceStepRefusedV1 3)
    (operator MM0SourceFoldV1 6)
    (operator MM0SourceFoldAfterStepV1 6)
    (operator MM0SourceEnvironmentFromAstV1 4)
    (operator MM0SourceHistoryConsV1 2)

    (operator MM0NotationWithCoercionsV1 2)
    (operator MM0CoercionEntryV1 4)
    (operator MM0CoercionsConsV1 2)
    (operator MM0CoercionViewV1 3)
    (operator MM0CoercionAstV1 4)
    (operator MM0CoercionValidateV1 4)
    (operator MM0CoercionRequestV1 5)
    (operator MM0CoercionAfterTermV1 3)
    (operator MM0CoercionAfterSortsV1 5)
    (operator MM0CoercionSignatureV1 6)
    (operator MM0CoercionSignatureTypesV1 7)
    (operator MM0CoercionPendingV1 4)
    (operator MM0CoercionAfterSignatureV1 3)
    (operator MM0CoercionAfterForestV1 3)
    (operator MM0CoercionAfterProvableV1 4)
    (operator MM0CoercionInstalledV1 2)
    (operator MM0CoercionStepAfterCheckV1 3)
    (operator MM0CoercionsAppendV1 3)
    (operator MM0CoercionReachV1 5)
    (operator MM0CoercionWalkV1 6)
    (operator MM0CoercionWalkAfterSeenV1 8)
    (operator MM0CoercionNeighborsV1 4)
    (operator MM0CoercionPathV1 4)
    (operator MM0CoercionPathVisitV1 5)
    (operator MM0CoercionPathAfterSeenV1 6)
    (operator MM0CoercionPathEdgesV1 6)
    (operator MM0CoercionPathAfterBranchV1 9)
    (operator MM0CoercionPathFoundV1 1)
    (operator MM0CoercionHopV1 2)
    (operator MM0CoercionGraphCheckV1 3)
    (operator MM0CoercionGraphSourcesV1 4)
    (operator MM0CoercionGraphAfterTargetV1 5)
    (operator MM0CoercionProvableTargetV1 4)
    (operator MM0CoercionProvableScanV1 5)
    (operator MM0CoercionProvableAfterReachV1 7)
    (operator MM0CoercionProvableFoundV1 1)
    (operator MM0CoercionAmbiguousV1 3)
    (operator MM0DeclaredCoercionV1 4)
    (operator MM0RefusedCoercionSortV1 2)
    (operator MM0RefusedCoercionSignatureV1 2)
    (operator MM0RefusedCoercionForestV1 3)
    (operator MM0RefusedCoercionProvableV1 4)
    (operator MM0NotationProxyAfterStepV1 3)
    (operator MM0NameLookupV1 3)
    (operator MM0ListAppendV1 3)
    (operator MM0SortLookupV1 3)
    (operator MM0SortFoundV1 2)
    (operator MM0SortEntryV1 3)
    (operator MM0SortEntriesConsV1 2)
    (operator MM0SortModifiersV1 4)
    (operator MM0TypeV1 2)
    (operator MM0BinderV1 3)
    (operator MM0NamedBinderV1 1)
    (operator MM0BinderSequenceV1 3)
    (operator MM0ValidateExplicitBindersV1 7)
    (operator MM0ValidateReturnTypeV1 6)
    (operator GSLTPrattStrictMinimumV1 1)
    (operator MM0GeneralNotationEntryV1 6)
    (operator MM0GeneralHeadLookupV1 3)
    (operator MM0InstallSimpleUncheckedV1 5)
    (operator MM0InstallSimpleAfterGeneralHeadV1 6)
    (operator MM0GeneralLiteralV1 3)
    (operator MM0GeneralVariableV1 2)
    (operator MM0GeneralRequestV1 7)
    (operator MM0GeneralValidateV1 4)
    (operator MM0GeneralAfterTermV1 3)
    (operator MM0GeneralAfterBindersV1 4)
    (operator MM0GeneralAfterReturnV1 5)
    (operator MM0GeneralAfterSignatureV1 4)
    (operator MM0GeneralSignatureV1 3)
    (operator MM0GeneralAlphaBindersV1 4)
    (operator MM0GeneralAlphaAfterBinderV1 5)
    (operator MM0GeneralAlphaAfterBindersV1 4)
    (operator MM0GeneralAlphaTypeV1 4)
    (operator MM0GeneralMapNamesV1 3)
    (operator MM0GeneralMapNameV1 3)
    (operator MM0GeneralMappedNamesV1 4)
    (operator MM0GeneralMappedTailV1 3)
    (operator MM0GeneralDependenciesV1 3)
    (operator MM0GeneralSubsetV1 3)
    (operator MM0GeneralSubsetAfterLookupV1 4)
    (operator MM0GeneralSubsetAfterFirstV1 4)
    (operator MM0GeneralBinderNamesV1 2)
    (operator MM0GeneralAfterHeadConstantV1 5)
    (operator MM0GeneralPendingV1 6)
    (operator MM0GeneralAfterHeadLookupsV1 4)
    (operator MM0GeneralInfixyLookupV1 3)
    (operator MM0GeneralInfixyAfterBinaryV1 4)
    (operator MM0GeneralInfixyTablesV1 2)
    (operator MM0GeneralInfixyPrefixesV1 3)
    (operator MM0GeneralInfixyPatternV1 4)
    (operator MM0GeneralInfixyAfterPatternV1 4)
    (operator MM0GeneralInfixyFoundV1 2)
    (operator MM0GeneralPatternV1 9)
    (operator MM0GeneralPatternRequestV1 8)
    (operator MM0GeneralAfterVariableV1 4)
    (operator MM0GeneralUnknownVariableV1 4)
    (operator MM0GeneralRemoveNameV1 3)
    (operator MM0GeneralVariableMinimumV1 3)
    (operator MM0GeneralMinimumAfterPrecedenceV1 2)
    (operator MM0GeneralAfterMinimumV1 4)
    (operator MM0GeneralAfterLiteralV1 3)
    (operator MM0GeneralPatternAcceptedV1 2)
    (operator MM0GeneralAfterConstantV1 4)
    (operator MM0GeneralRegisterConstantV1 7)
    (operator MM0GeneralCompareTokensV1 3)
    (operator MM0GeneralRegisterAfterHeadV1 3)
    (operator MM0GeneralRegisterAfterLookupsV1 5)
    (operator MM0GeneralConstantRequestV1 5)
    (operator MM0GeneralInstallConstantV1 5)
    (operator MM0GeneralConstantAfterLookupV1 3)
    (operator MM0GeneralReplaceConstantV1 4)
    (operator MM0GeneralAfterRegisteredV1 5)
    (operator MM0GeneralAfterPatternV1 3)
    (operator MM0GeneralPatternCheckV1 3)
    (operator MM0GeneralPatternAfterLookupV1 6)
    (operator MM0GeneralInstallAfterCheckV1 4)
    (operator MM0GeneralInstalledV1 2)
    (operator MM0GeneralRestoreV1 3)
    (operator MM0GeneralStepAfterCheckV1 3)
    (operator MM0DeclaredGeneralNotationV1 4)
    (operator MM0RefusedNotationSignatureV1 2)
    (operator MM0RefusedNotationVariableV1 3)
    (operator MM0RefusedNotationUnusedVariableV1 2)
    (operator MM0RefusedNotationInfixyMaximumV1 2))
  (equations)
  (rewrites
    ; The outer grammar admits only `0` or a nonzero digit followed by digits,
    ; so its number node already carries a canonical compact decimal.  Keep
    ; that certified representation rather than expanding it to unary.
    (rule mm0-notation-precedence-number-v1
      (head
        (MM0PrecedenceFromAstV1
          (node mm0-number (pair ?first ?rest))
          (MM0FinitePrecedenceV1 (cons ?first ?rest))))
      (body))
    (rule mm0-notation-precedence-zero-v1
      (head (MM0PrecedenceFromAstV1 (node mm0-number (cp 48))
        (MM0FinitePrecedenceV1 (cons (cp 48) nil)))) (body))
    (rule mm0-notation-precedence-max-v1
      (head
        (MM0PrecedenceFromAstV1
          (cons (cp 109) (cons (cp 97) (cons (cp 120) nil)))
          MM0MaximumPrecedenceV1))
      (body))

    (rule mm0-notation-list-length-nil-v1
      (head (MM0ListLengthV1 nil NatZeroV1))
      (body))
    (rule mm0-notation-list-length-cons-v1
      (head
        (MM0ListLengthV1 (cons ?head ?rest) (NatSuccV1 ?length)))
      (body (MM0ListLengthV1 ?rest ?length)))

    (rule mm0-notation-token-list-length-nil-v1
      (head (MM0MathTokenListLengthV1 MM0MathTokensNilV1 NatZeroV1))
      (body))
    (rule mm0-notation-token-list-length-cons-v1
      (head
        (MM0MathTokenListLengthV1
          (MM0MathTokensConsV1 ?head ?rest) (NatSuccV1 ?length)))
      (body (MM0MathTokenListLengthV1 ?rest ?length)))

    ; The outer parser and secondary lexer deliberately have distinct list
    ; carriers.  Their total structural codec is part of the authored
    ; composition, not a conversion hidden in a target runtime.
    (rule mm0-notation-scalars-from-list-nil-v1
      (head (MM0MathScalarsFromListV1 nil MM0MathScalarsNilV1))
      (body))
    (rule mm0-notation-scalars-from-list-cons-v1
      (head
        (MM0MathScalarsFromListV1
          (cons ?scalar ?rest)
          (MM0MathScalarsConsV1 ?scalar ?after)))
      (body (MM0MathScalarsFromListV1 ?rest ?after)))

    ; The term environment retains the normalized signature needed to check
    ; notation arity.  Lookup is total and preserves the first position.
    (rule mm0-notation-term-signature-lookup-missing-v1
      (head
        (MM0TermSignatureLookupV1
          ?name MM0DeclarationEntriesNilV1 MM0TermSignatureMissingV1))
      (body))
    (rule mm0-notation-term-signature-lookup-found-v1
      (head
        (MM0TermSignatureLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0TermEntryV1 ?name ?signature ?position ?source) ?rest)
          (MM0TermSignatureFoundV1 ?signature ?position)))
      (body))
    (rule mm0-notation-term-signature-lookup-tail-v1
      (head
        (MM0TermSignatureLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0TermEntryV1 ?other ?signature ?position ?source) ?rest)
          ?result))
      (body
        (different ?name ?other)
        (MM0TermSignatureLookupV1 ?name ?rest ?result)))

    ; Finite ordered map helpers.  The didactic representation keeps source
    ; order; later target optimization may index the same values.
    (rule mm0-notation-constant-lookup-missing-v1
      (head
        (MM0ConstantLookupV1
          ?token MM0ConstantEntriesNilV1 MM0ConstantMissingV1))
      (body))
    (rule mm0-notation-constant-lookup-found-v1
      (head
        (MM0ConstantLookupV1
          ?token
          (MM0ConstantEntriesConsV1
            (MM0ConstantEntryV1 ?token ?precedence ?position) ?rest)
          (MM0ConstantFoundV1 ?precedence ?position)))
      (body))
    (rule mm0-notation-constant-lookup-tail-v1
      (head
        (MM0ConstantLookupV1
          ?token
          (MM0ConstantEntriesConsV1
            (MM0ConstantEntryV1 ?other ?precedence ?position) ?rest)
          ?result))
      (body
        (different ?token ?other)
        (MM0ConstantLookupV1 ?token ?rest ?result)))
    (rule mm0-notation-constant-append-nil-v1
      (head
        (MM0ConstantEntriesAppendV1
          MM0ConstantEntriesNilV1 ?entry
          (MM0ConstantEntriesConsV1 ?entry MM0ConstantEntriesNilV1)))
      (body))
    (rule mm0-notation-constant-append-cons-v1
      (head
        (MM0ConstantEntriesAppendV1
          (MM0ConstantEntriesConsV1 ?head ?rest) ?entry
          (MM0ConstantEntriesConsV1 ?head ?after)))
      (body (MM0ConstantEntriesAppendV1 ?rest ?entry ?after)))

    (rule mm0-notation-prefix-lookup-missing-v1
      (head
        (MM0PrefixLookupV1
          ?token MM0PrefixEntriesNilV1 MM0PrefixMissingV1))
      (body))
    (rule mm0-notation-prefix-lookup-found-v1
      (head
        (MM0PrefixLookupV1
          ?token
          (MM0PrefixEntriesConsV1
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?precedence ?position) ?rest)
          (MM0PrefixFoundV1 ?position)))
      (body))
    (rule mm0-notation-prefix-lookup-tail-v1
      (head
        (MM0PrefixLookupV1
          ?token
          (MM0PrefixEntriesConsV1
            (MM0PrefixNotationEntryV1
              ?other ?term ?arity ?precedence ?position) ?rest)
          ?result))
      (body
        (different ?token ?other)
        (MM0PrefixLookupV1 ?token ?rest ?result)))
    (rule mm0-notation-prefix-append-nil-v1
      (head
        (MM0PrefixEntriesAppendV1
          MM0PrefixEntriesNilV1 ?entry
          (MM0PrefixEntriesConsV1 ?entry MM0PrefixEntriesNilV1)))
      (body))
    (rule mm0-notation-prefix-append-cons-v1
      (head
        (MM0PrefixEntriesAppendV1
          (MM0PrefixEntriesConsV1 ?head ?rest) ?entry
          (MM0PrefixEntriesConsV1 ?head ?after)))
      (body (MM0PrefixEntriesAppendV1 ?rest ?entry ?after)))

    (rule mm0-notation-infix-lookup-missing-v1
      (head
        (MM0InfixLookupV1
          ?token MM0InfixEntriesNilV1 MM0InfixMissingV1))
      (body))
    (rule mm0-notation-infix-lookup-found-v1
      (head
        (MM0InfixLookupV1
          ?token
          (MM0InfixEntriesConsV1
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?precedence ?position) ?rest)
          (MM0InfixFoundV1 ?position)))
      (body))
    (rule mm0-notation-infix-lookup-tail-v1
      (head
        (MM0InfixLookupV1
          ?token
          (MM0InfixEntriesConsV1
            (MM0InfixNotationEntryV1
              ?other ?term ?associativity ?precedence ?position) ?rest)
          ?result))
      (body
        (different ?token ?other)
        (MM0InfixLookupV1 ?token ?rest ?result)))
    (rule mm0-notation-infix-append-nil-v1
      (head
        (MM0InfixEntriesAppendV1
          MM0InfixEntriesNilV1 ?entry
          (MM0InfixEntriesConsV1 ?entry MM0InfixEntriesNilV1)))
      (body))
    (rule mm0-notation-infix-append-cons-v1
      (head
        (MM0InfixEntriesAppendV1
          (MM0InfixEntriesConsV1 ?head ?rest) ?entry
          (MM0InfixEntriesConsV1 ?head ?after)))
      (body (MM0InfixEntriesAppendV1 ?rest ?entry ?after)))

    ; Outer syntax discriminants become a target-neutral notation kind.
    (rule mm0-notation-simple-statement-prefix-v1
      (head
        (MM0SimpleNotationStatementV1
          (node mm0-simple-notation-statement
            (pair (node mm0-prefix-kind ?keyword)
              (pair ?identifier (pair ?constant ?precedence))))
          MM0PrefixNotationKindV1 ?termName ?constant ?precedence))
      (body (MM0IdentifierScalarsV1 ?identifier ?termName)))
    (rule mm0-notation-simple-statement-infixl-v1
      (head
        (MM0SimpleNotationStatementV1
          (node mm0-simple-notation-statement
            (pair (node mm0-infixl-kind ?keyword)
              (pair ?identifier (pair ?constant ?precedence))))
          (MM0InfixNotationKindV1 MM0LeftAssociativeV1)
          ?termName ?constant ?precedence))
      (body (MM0IdentifierScalarsV1 ?identifier ?termName)))
    (rule mm0-notation-simple-statement-infixr-v1
      (head
        (MM0SimpleNotationStatementV1
          (node mm0-simple-notation-statement
            (pair (node mm0-infixr-kind ?keyword)
              (pair ?identifier (pair ?constant ?precedence))))
          (MM0InfixNotationKindV1 MM0RightAssociativeV1)
          ?termName ?constant ?precedence))
      (body (MM0IdentifierScalarsV1 ?identifier ?termName)))

    ; A notation constant must lex to exactly one non-parenthesis token under
    ; the delimiter state that precedes the declaration.
    (rule mm0-notation-constant-v1
      (head
        (MM0NotationConstantV1
          ?delimiterTable (node mm0-math-string ?scalars) ?result))
      (body
        (MM0MathScalarsFromListV1 ?scalars ?mathScalars)
        (MM0SecondaryLexV1 ?delimiterTable ?mathScalars ?tokens)
        (MM0NotationConstantClassV1 ?tokens ?scalars ?result)))
    (rule mm0-notation-constant-class-single-v1
      (head
        (MM0NotationConstantClassV1
          (MM0MathTokensConsV1
            (MM0MathTokenV1 ?token) MM0MathTokensNilV1)
          ?source ?result))
      (body (MM0NotationTokenAllowedV1 ?token ?result)))
    (rule mm0-notation-constant-class-empty-v1
      (head
        (MM0NotationConstantClassV1
          MM0MathTokensNilV1 ?source
          (MM0CheckRefusedV1
            (MM0RefusedNotationConstantTokenCountV1 ?source NatZeroV1))))
      (body))
    (rule mm0-notation-constant-class-many-v1
      (head
        (MM0NotationConstantClassV1
          (MM0MathTokensConsV1 ?first
            (MM0MathTokensConsV1 ?second ?rest))
          ?source
          (MM0CheckRefusedV1
            (MM0RefusedNotationConstantTokenCountV1
              ?source ?count))))
      (body
        (MM0MathTokenListLengthV1
          (MM0MathTokensConsV1 ?first
            (MM0MathTokensConsV1 ?second ?rest))
          ?count)))
    (rule mm0-notation-token-left-paren-v1
      (head
        (MM0NotationTokenAllowedV1
          (MM0MathScalarsConsV1 (cp 40) MM0MathScalarsNilV1)
          (MM0CheckRefusedV1
            (MM0RefusedNotationParenthesisV1 (cp 40) MM0LeftParenthesisV1))))
      (body))
    (rule mm0-notation-token-right-paren-v1
      (head
        (MM0NotationTokenAllowedV1
          (MM0MathScalarsConsV1 (cp 41) MM0MathScalarsNilV1)
          (MM0CheckRefusedV1
            (MM0RefusedNotationParenthesisV1 (cp 41) MM0RightParenthesisV1))))
      (body))
    (rule mm0-notation-token-allowed-v1
      (head
        (MM0NotationTokenAllowedV1
          ?token (MM0CheckAcceptedV1 ?token)))
      (body
        (different ?token
          (MM0MathScalarsConsV1 (cp 40) MM0MathScalarsNilV1))
        (different ?token
          (MM0MathScalarsConsV1 (cp 41) MM0MathScalarsNilV1))))

    ; Prefix arity is the declared term arity.  Infix notation is exactly
    ; binary and cannot use maximum precedence.
    (rule mm0-notation-prepare-prefix-v1
      (head
        (MM0PrepareSimpleNotationV1
          ?position MM0PrefixNotationKindV1 ?termName
          (MM0TermSignatureV1 ?binders ?returnType)
          ?delimiterTable ?constantAst ?precedenceAst ?result))
      (body
        (MM0ListLengthV1 ?binders ?arity)
        (MM0PrecedenceFromAstV1 ?precedenceAst ?precedence)
        (MM0NotationConstantV1 ?delimiterTable ?constantAst ?constantResult)
        (MM0PreparePrefixAfterConstantV1
          ?position ?termName ?arity ?precedence
          ?delimiterTable ?constantResult ?result)))
    (rule mm0-notation-prepare-prefix-constant-accepted-v1
      (head
        (MM0PreparePrefixAfterConstantV1
          ?position ?termName ?arity ?precedence ?delimiterTable
          (MM0CheckAcceptedV1 ?token)
          (MM0CheckAcceptedV1
            (MM0PreparedSimpleNotationV1
              ?token ?precedence
              (MM0PrefixNotationEntryV1
                ?token ?termName ?arity ?precedence ?position)))))
      (body))
    (rule mm0-notation-prepare-prefix-constant-refused-v1
      (head
        (MM0PreparePrefixAfterConstantV1
          ?position ?termName ?arity ?precedence ?delimiterTable
          (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason)))
      (body))

    (rule mm0-notation-prepare-infix-v1
      (head
        (MM0PrepareSimpleNotationV1
          ?position (MM0InfixNotationKindV1 ?associativity) ?termName
          (MM0TermSignatureV1 ?binders ?returnType)
          ?delimiterTable ?constantAst ?precedenceAst ?result))
      (body
        (MM0ListLengthV1 ?binders ?arity)
        (MM0PrepareInfixAfterArityV1
          ?position ?termName ?associativity ?arity
          ?constantAst ?precedenceAst ?delimiterTable ?result)))
    (rule mm0-notation-prepare-infix-arity-refused-v1
      (head
        (MM0PrepareInfixAfterArityV1
          ?position ?termName ?associativity ?arity
          ?constantAst ?precedenceAst ?delimiterTable
          (MM0CheckRefusedV1
            (MM0RefusedInfixArityV1 ?position ?termName ?arity))))
      (body
        (different ?arity
          (NatSuccV1 (NatSuccV1 NatZeroV1)))))
    (rule mm0-notation-prepare-infix-max-refused-v1
      (head
        (MM0PrepareInfixAfterArityV1
          ?position ?termName ?associativity
          (NatSuccV1 (NatSuccV1 NatZeroV1))
          ?constantAst ?precedenceAst ?delimiterTable
          (MM0CheckRefusedV1
            (MM0RefusedInfixMaximumPrecedenceV1 ?position ?termName))))
      (body
        (MM0PrecedenceFromAstV1 ?precedenceAst MM0MaximumPrecedenceV1)))
    (rule mm0-notation-prepare-infix-finite-v1
      (head
        (MM0PrepareInfixAfterArityV1
          ?position ?termName ?associativity
          (NatSuccV1 (NatSuccV1 NatZeroV1))
          ?constantAst ?precedenceAst ?delimiterTable ?result))
      (body
        (MM0PrecedenceFromAstV1
          ?precedenceAst (MM0FinitePrecedenceV1 ?precedence))
        (MM0NotationConstantV1 ?delimiterTable ?constantAst ?constantResult)
        (MM0PrepareInfixAfterConstantV1
          ?position ?termName ?associativity ?precedence
          ?constantResult ?result)))
    (rule mm0-notation-prepare-infix-constant-accepted-v1
      (head
        (MM0PrepareInfixAfterConstantV1
          ?position ?termName ?associativity ?precedence
          (MM0CheckAcceptedV1 ?token)
          (MM0CheckAcceptedV1
            (MM0PreparedSimpleNotationV1
              ?token (MM0FinitePrecedenceV1 ?precedence)
              (MM0InfixNotationEntryV1
                ?token ?termName ?associativity
                (MM0FinitePrecedenceV1 ?precedence) ?position)))))
      (body))
    (rule mm0-notation-prepare-infix-constant-refused-v1
      (head
        (MM0PrepareInfixAfterConstantV1
          ?position ?termName ?associativity ?precedence
          (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason)))
      (body))

    ; A general production's head remains unique when later simple notation
    ; declarations are encountered. Installation is transactional.
    (rule mm0-notation-install-check-general-head-v1
      (head (MM0InstallSimpleNotationV1 ?position
        (MM0PreparedSimpleNotationV1 ?token ?prec ?entry)
        (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?result ?source))
      (body (MM0GeneralHeadLookupV1 ?token ?p ?lookup)
        (MM0InstallSimpleAfterGeneralHeadV1 ?position
          (MM0PreparedSimpleNotationV1 ?token ?prec ?entry)
          (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?source ?lookup ?result)))
    (rule mm0-notation-install-general-head-missing-v1
      (head (MM0InstallSimpleAfterGeneralHeadV1 ?position ?prepared ?base ?source MM0PrefixMissingV1 ?result))
      (body (MM0InstallSimpleUncheckedV1 ?position ?prepared ?base ?result ?source)))
    (rule mm0-notation-install-general-head-refused-v1
      (head (MM0InstallSimpleAfterGeneralHeadV1 ?position
        (MM0PreparedSimpleNotationV1 ?token ?prec ?entry) ?base ?source (MM0PrefixFoundV1 ?first)
        (MM0NotationStepRefusedV1 (MM0RefusedNotationRedeclarationV1 ?position ?token ?first)
          ?base (MM0RefusedNotationRedeclarationV1 ?position ?token ?first)))) (body))
    (rule mm0-general-head-lookup-empty-v1
      (head (MM0GeneralHeadLookupV1 ?token MM0PrefixEntriesNilV1 MM0PrefixMissingV1)) (body))
    (rule mm0-general-head-lookup-simple-v1
      (head (MM0GeneralHeadLookupV1 ?token
        (MM0PrefixEntriesConsV1 (MM0PrefixNotationEntryV1 ?head ?term ?arity ?prec ?pos) ?rest) ?result))
      (body (MM0GeneralHeadLookupV1 ?token ?rest ?result)))
    (rule mm0-general-head-lookup-found-v1
      (head (MM0GeneralHeadLookupV1 ?token
        (MM0PrefixEntriesConsV1 (MM0GeneralNotationEntryV1 ?token ?term ?names ?prec ?pattern ?pos) ?rest)
        (MM0PrefixFoundV1 ?pos))) (body))
    (rule mm0-general-head-lookup-tail-v1
      (head (MM0GeneralHeadLookupV1 ?token
        (MM0PrefixEntriesConsV1 (MM0GeneralNotationEntryV1 ?other ?term ?names ?prec ?pattern ?pos) ?rest) ?result))
      (body (different ?token ?other) (MM0GeneralHeadLookupV1 ?token ?rest ?result)))
    (rule mm0-notation-install-prefix-v1
      (head
        (MM0InstallSimpleUncheckedV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?result ?source))
      (body
        (MM0ConstantLookupV1
          ?token ?constants ?constantLookup)
        (MM0PrefixLookupV1 ?token ?prefixes ?prefixLookup)
        (MM0InstallPrefixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?constantLookup ?prefixLookup ?result)))
    (rule mm0-notation-install-infix-v1
      (head
        (MM0InstallSimpleUncheckedV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?result ?source))
      (body
        (MM0ConstantLookupV1
          ?token ?constants ?constantLookup)
        (MM0InfixLookupV1 ?token ?infixes ?infixLookup)
        (MM0InstallInfixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?constantLookup ?infixLookup ?result)))

    (rule mm0-notation-install-prefix-new-constant-v1
      (head
        (MM0InstallPrefixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          MM0ConstantMissingV1 MM0PrefixMissingV1
          (MM0NotationStepAcceptedV1
            (MM0NotationEnvironmentV1
              ?delimiters ?afterConstants ?afterPrefixes ?infixes)
            (MM0DeclaredSimpleNotationV1
              ?position ?term MM0PrefixNotationKindV1 ?token))))
      (body
        (MM0ConstantEntriesAppendV1 ?constants
          (MM0ConstantEntryV1 ?token ?precedence ?position) ?afterConstants)
        (MM0PrefixEntriesAppendV1 ?prefixes
          (MM0PrefixNotationEntryV1
            ?token ?term ?arity ?precedence ?position) ?afterPrefixes)))
    (rule mm0-notation-install-prefix-existing-constant-v1
      (head
        (MM0InstallPrefixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0ConstantFoundV1 ?precedence ?constantPosition)
          MM0PrefixMissingV1
          (MM0NotationStepAcceptedV1
            (MM0NotationEnvironmentV1
              ?delimiters ?constants ?afterPrefixes ?infixes)
            (MM0DeclaredSimpleNotationV1
              ?position ?term MM0PrefixNotationKindV1 ?token))))
      (body
        (MM0PrefixEntriesAppendV1 ?prefixes
          (MM0PrefixNotationEntryV1
            ?token ?term ?arity ?precedence ?position) ?afterPrefixes)))
    (rule mm0-notation-install-infix-new-constant-v1
      (head
        (MM0InstallInfixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          MM0ConstantMissingV1 MM0InfixMissingV1
          (MM0NotationStepAcceptedV1
            (MM0NotationEnvironmentV1
              ?delimiters ?afterConstants ?prefixes ?afterInfixes)
            (MM0DeclaredSimpleNotationV1
              ?position ?term
              (MM0InfixNotationKindV1 ?associativity) ?token))))
      (body
        (MM0ConstantEntriesAppendV1 ?constants
          (MM0ConstantEntryV1 ?token ?precedence ?position) ?afterConstants)
        (MM0InfixEntriesAppendV1 ?infixes
          (MM0InfixNotationEntryV1
            ?token ?term ?associativity ?precedence ?position) ?afterInfixes)))
    (rule mm0-notation-install-infix-existing-constant-v1
      (head
        (MM0InstallInfixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0ConstantFoundV1 ?precedence ?constantPosition)
          MM0InfixMissingV1
          (MM0NotationStepAcceptedV1
            (MM0NotationEnvironmentV1
              ?delimiters ?constants ?prefixes ?afterInfixes)
            (MM0DeclaredSimpleNotationV1
              ?position ?term
              (MM0InfixNotationKindV1 ?associativity) ?token))))
      (body
        (MM0InfixEntriesAppendV1 ?infixes
          (MM0InfixNotationEntryV1
            ?token ?term ?associativity ?precedence ?position) ?afterInfixes)))
    (rule mm0-notation-install-prefix-precedence-conflict-v1
      (head
        (MM0InstallPrefixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?newPrecedence
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?newPrecedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0ConstantFoundV1 ?oldPrecedence ?constantPosition)
          ?prefixLookup
          (MM0NotationStepRefusedV1
            (MM0RefusedNotationPrecedenceConflictV1
              ?position ?token ?oldPrecedence ?newPrecedence)
            (MM0NotationEnvironmentV1
              ?delimiters ?constants ?prefixes ?infixes)
            (MM0RefusedNotationPrecedenceConflictV1
              ?position ?token ?oldPrecedence ?newPrecedence))))
      (body
        (different ?oldPrecedence ?newPrecedence)))
    (rule mm0-notation-install-infix-precedence-conflict-v1
      (head
        (MM0InstallInfixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?newPrecedence
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?newPrecedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0ConstantFoundV1 ?oldPrecedence ?constantPosition)
          ?infixLookup
          (MM0NotationStepRefusedV1
            (MM0RefusedNotationPrecedenceConflictV1
              ?position ?token ?oldPrecedence ?newPrecedence)
            (MM0NotationEnvironmentV1
              ?delimiters ?constants ?prefixes ?infixes)
            (MM0RefusedNotationPrecedenceConflictV1
              ?position ?token ?oldPrecedence ?newPrecedence))))
      (body
        (different ?oldPrecedence ?newPrecedence)))
    (rule mm0-notation-install-prefix-redeclared-v1
      (head
        (MM0InstallPrefixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0PrefixNotationEntryV1
              ?token ?term ?arity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0ConstantFoundV1 ?precedence ?constantPosition)
          (MM0PrefixFoundV1 ?firstPosition)
          (MM0NotationStepRefusedV1
            (MM0RefusedNotationRedeclarationV1
              ?position ?token ?firstPosition)
            (MM0NotationEnvironmentV1
              ?delimiters ?constants ?prefixes ?infixes)
            (MM0RefusedNotationRedeclarationV1
              ?position ?token ?firstPosition))))
      (body))
    (rule mm0-notation-install-infix-redeclared-v1
      (head
        (MM0InstallInfixFromLookupsV1
          ?position
          (MM0PreparedSimpleNotationV1 ?token ?precedence
            (MM0InfixNotationEntryV1
              ?token ?term ?associativity ?precedence ?position))
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0ConstantFoundV1 ?precedence ?constantPosition)
          (MM0InfixFoundV1 ?firstPosition)
          (MM0NotationStepRefusedV1
            (MM0RefusedNotationRedeclarationV1
              ?position ?token ?firstPosition)
            (MM0NotationEnvironmentV1
              ?delimiters ?constants ?prefixes ?infixes)
            (MM0RefusedNotationRedeclarationV1
              ?position ?token ?firstPosition))))
      (body))

    ; Delimiters and simple notations are state transitions over the current
    ; prefix.  No later statement participates in either transition.
    (rule mm0-notation-step-delimiter-both-v1
      (head
        (MM0NotationStepV1
          ?position
          (node mm0-delimiter-statement
            (pair (node mm0-math-string ?both) none))
          (MM0NotationEnvironmentV1
            ?before ?constants ?prefixes ?infixes)
          ?declarations
          (MM0NotationStepAcceptedV1
            (MM0NotationEnvironmentV1
              ?after ?constants ?prefixes ?infixes)
            (MM0DeclaredDelimitersV1 ?position MM0BothDelimitersV1))))
      (body
        (MM0DelimiterCharactersFoldV1
          ?both MM0MathBothDelimiterV1 ?before ?after)))
    (rule mm0-notation-step-delimiter-left-right-v1
      (head
        (MM0NotationStepV1
          ?position
          (node mm0-delimiter-statement
            (pair (node mm0-math-string ?left)
              (some (node mm0-math-string ?right))))
          (MM0NotationEnvironmentV1
            ?before ?constants ?prefixes ?infixes)
          ?declarations
          (MM0NotationStepAcceptedV1
            (MM0NotationEnvironmentV1
              ?after ?constants ?prefixes ?infixes)
            (MM0DeclaredDelimitersV1 ?position MM0LeftRightDelimitersV1))))
      (body
        (MM0DelimiterCharactersFoldV1
          ?left MM0MathLeftDelimiterV1 ?before ?middle)
        (MM0DelimiterCharactersFoldV1
          ?right MM0MathRightDelimiterV1 ?middle ?after)))
    (rule mm0-notation-step-simple-v1
      (head
        (MM0NotationStepV1
          ?position ?statement
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?declarations ?result))
      (body
        (MM0SimpleNotationStatementV1
          ?statement ?kind ?termName ?constantAst ?precedenceAst)
        (MM0TermSignatureLookupV1 ?termName ?declarations ?lookup)
        (MM0NotationStepAfterTermLookupV1
          ?position ?kind ?termName ?constantAst ?precedenceAst
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?lookup ?result)))
    (rule mm0-notation-step-unknown-term-v1
      (head
        (MM0NotationStepAfterTermLookupV1
          ?position ?kind ?termName ?constantAst ?precedenceAst ?before
          MM0TermSignatureMissingV1
          (MM0NotationStepRefusedV1
            (MM0RefusedUnknownNotationTermV1 ?position ?termName)
            ?before
            (MM0RefusedUnknownNotationTermV1 ?position ?termName))))
      (body))
    (rule mm0-notation-step-found-term-v1
      (head
        (MM0NotationStepAfterTermLookupV1
          ?position ?kind ?termName ?constantAst ?precedenceAst
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          (MM0TermSignatureFoundV1 ?signature ?termPosition) ?result))
      (body
        (MM0PrepareSimpleNotationV1
          ?position ?kind ?termName ?signature
          ?delimiters ?constantAst ?precedenceAst ?prepared)
        (MM0NotationStepAfterPrepareV1
          ?position
          (MM0NotationEnvironmentV1
            ?delimiters ?constants ?prefixes ?infixes)
          ?prepared ?result)))
    (rule mm0-notation-step-prepare-refused-v1
      (head
        (MM0NotationStepAfterPrepareV1
          ?position ?before (MM0CheckRefusedV1 ?reason)
          (MM0NotationStepRefusedV1 ?reason ?before ?reason)))
      (body))
    (rule mm0-notation-step-prepare-accepted-v1
      (head
        (MM0NotationStepAfterPrepareV1
          ?position ?before (MM0CheckAcceptedV1 ?prepared) ?result))
      (body
        (MM0InstallSimpleNotationV1
          ?position ?prepared ?before ?result MM0RuntimeTextualSourceV1)))

    ; General notation shares the term namespace and normalizes its typed
    ; signature with the same binder and return-type judgments as terms.
    (rule mm0-general-validate-v1
      (head (MM0GeneralValidateV1 ?position
        (node mm0-general-notation-statement
          (pair ?termAst (pair ?bindersAst (pair ?returnAst (pair ?headAst ?literals)))))
        (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation) ?result))
      (body (MM0IdentifierScalarsV1 ?termAst ?term)
        (MM0TermSignatureLookupV1 ?term ?decls ?lookup)
        (MM0GeneralAfterTermV1
          (MM0GeneralRequestV1 ?position ?term
            (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation)
            ?bindersAst ?returnAst ?headAst ?literals) ?lookup ?result)))
    (rule mm0-general-unknown-term-v1
      (head (MM0GeneralAfterTermV1
        (MM0GeneralRequestV1 ?position ?term ?state ?binders ?return ?head ?lits)
        MM0TermSignatureMissingV1
        (MM0CheckRefusedV1 (MM0RefusedUnknownNotationTermV1 ?position ?term)))) (body))
    (rule mm0-general-found-term-v1
      (head (MM0GeneralAfterTermV1
        (MM0GeneralRequestV1 ?position ?term
          (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation)
          ?bindersAst ?returnAst ?headAst ?lits)
        (MM0TermSignatureFoundV1 ?signature ?first) ?result))
      (body (MM0ValidateExplicitBindersV1 ?position ?term ?sorts ?bindersAst nil nil ?check)
        (MM0GeneralAfterBindersV1
          (MM0GeneralRequestV1 ?position ?term
            (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation)
            ?bindersAst ?returnAst ?headAst ?lits) ?signature ?check ?result)))
    (rule mm0-general-binders-refused-v1
      (head (MM0GeneralAfterBindersV1 ?request ?signature
        (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-binders-accepted-v1
      (head (MM0GeneralAfterBindersV1
        (MM0GeneralRequestV1 ?position ?term
          (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation)
          ?bindersAst ?returnAst ?headAst ?lits) ?signature
        (MM0CheckAcceptedV1 (MM0BinderSequenceV1 ?binders ?boundNames ?allNames)) ?result))
      (body (MM0ValidateReturnTypeV1 ?position ?term ?sorts ?boundNames ?returnAst ?check)
        (MM0GeneralAfterReturnV1
          (MM0GeneralRequestV1 ?position ?term
            (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation)
            ?bindersAst ?returnAst ?headAst ?lits) ?signature ?binders ?check ?result)))
    (rule mm0-general-return-refused-v1
      (head (MM0GeneralAfterReturnV1 ?request ?signature ?binders
        (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-return-accepted-v1
      (head (MM0GeneralAfterReturnV1 ?request ?signature ?binders
        (MM0CheckAcceptedV1 ?return) ?result))
      (body (MM0GeneralSignatureV1 ?signature (MM0TermSignatureV1 ?binders ?return) ?check)
        (MM0GeneralAfterSignatureV1 ?request ?binders ?check ?result)))

    ; Dependency masks are compared as sets after renaming notation binders
    ; to the corresponding declaration binders. Source spelling is irrelevant.
    (rule mm0-general-signature-v1
      (head (MM0GeneralSignatureV1 (MM0TermSignatureV1 ?old ?oldReturn)
        (MM0TermSignatureV1 ?new ?newReturn) ?result))
      (body (MM0GeneralAlphaBindersV1 ?old ?new nil ?check)
        (MM0GeneralAlphaAfterBindersV1 ?oldReturn ?newReturn ?check ?result)))
    (rule mm0-general-alpha-empty-v1
      (head (MM0GeneralAlphaBindersV1 nil nil ?map (MM0CheckAcceptedV1 ?map))) (body))
    (rule mm0-general-alpha-too-many-v1
      (head (MM0GeneralAlphaBindersV1 nil (cons ?head ?rest) ?map
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1))) (body))
    (rule mm0-general-alpha-too-few-v1
      (head (MM0GeneralAlphaBindersV1 (cons ?head ?rest) nil ?map
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1))) (body))
    (rule mm0-general-alpha-anonymous-v1
      (head (MM0GeneralAlphaBindersV1 (cons ?old ?oldRest)
        (cons (MM0BinderV1 ?kind MM0AnonymousBinderV1 ?type) ?newRest) ?map
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1))) (body))
    (rule mm0-general-alpha-kind-refused-v1
      (head (MM0GeneralAlphaBindersV1
        (cons (MM0BinderV1 ?oldKind ?oldName ?oldType) ?oldRest)
        (cons (MM0BinderV1 ?newKind (MM0NamedBinderV1 ?newName) ?newType) ?newRest)
        ?map (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1)))
      (body (different ?oldKind ?newKind)))
    (rule mm0-general-alpha-binder-v1
      (head (MM0GeneralAlphaBindersV1
        (cons (MM0BinderV1 ?kind ?oldName ?oldType) ?oldRest)
        (cons (MM0BinderV1 ?kind (MM0NamedBinderV1 ?newName) ?newType) ?newRest)
        ?map ?result))
      (body (MM0GeneralAlphaTypeV1 ?oldType ?newType ?map ?check)
        (MM0GeneralAlphaAfterBinderV1 ?oldRest ?newRest
          (cons (pair ?newName ?oldName) ?map) ?check ?result)))
    (rule mm0-general-alpha-binder-refused-v1
      (head (MM0GeneralAlphaAfterBinderV1 ?old ?new ?map
        (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-alpha-binder-accepted-v1
      (head (MM0GeneralAlphaAfterBinderV1 ?old ?new ?map
        (MM0CheckAcceptedV1 MM0GeneralTypesEqualV1) ?result))
      (body (MM0GeneralAlphaBindersV1 ?old ?new ?map ?result)))
    (rule mm0-general-alpha-binders-refused-v1
      (head (MM0GeneralAlphaAfterBindersV1 ?oldReturn ?newReturn
        (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-alpha-return-v1
      (head (MM0GeneralAlphaAfterBindersV1 ?oldReturn ?newReturn
        (MM0CheckAcceptedV1 ?map) ?result))
      (body (MM0GeneralAlphaTypeV1 ?oldReturn ?newReturn ?map ?result)))
    (rule mm0-general-alpha-sort-refused-v1
      (head (MM0GeneralAlphaTypeV1 (MM0TypeV1 ?oldSort ?oldDeps)
        (MM0TypeV1 ?newSort ?newDeps) ?map
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1)))
      (body (different ?oldSort ?newSort)))
    (rule mm0-general-alpha-dependencies-v1
      (head (MM0GeneralAlphaTypeV1 (MM0TypeV1 ?sort ?oldDeps)
        (MM0TypeV1 ?sort ?newDeps) ?map ?result))
      (body (MM0GeneralMapNamesV1 ?newDeps ?map ?mapped)
        (MM0GeneralDependenciesV1 ?oldDeps ?mapped ?result)))
    (rule mm0-general-map-names-empty-v1
      (head (MM0GeneralMapNamesV1 nil ?map (MM0CheckAcceptedV1 nil))) (body))
    (rule mm0-general-map-names-cons-v1
      (head (MM0GeneralMapNamesV1 (cons ?name ?rest) ?map ?result))
      (body (MM0GeneralMapNameV1 ?name ?map ?mapped)
        (MM0GeneralMappedNamesV1 ?rest ?map ?mapped ?result)))
    (rule mm0-general-map-name-missing-v1
      (head (MM0GeneralMapNameV1 ?name nil
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1))) (body))
    (rule mm0-general-map-name-found-v1
      (head (MM0GeneralMapNameV1 ?name
        (cons (pair ?name (MM0NamedBinderV1 ?oldName)) ?rest)
        (MM0CheckAcceptedV1 ?oldName))) (body))
    (rule mm0-general-map-name-anonymous-v1
      (head (MM0GeneralMapNameV1 ?name (cons (pair ?name MM0AnonymousBinderV1) ?rest)
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1))) (body))
    (rule mm0-general-map-name-tail-v1
      (head (MM0GeneralMapNameV1 ?name (cons (pair ?other ?oldName) ?rest) ?result))
      (body (different ?name ?other) (MM0GeneralMapNameV1 ?name ?rest ?result)))
    (rule mm0-general-mapped-names-refused-v1
      (head (MM0GeneralMappedNamesV1 ?rest ?map (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-mapped-names-accepted-v1
      (head (MM0GeneralMappedNamesV1 ?rest ?map (MM0CheckAcceptedV1 ?name) ?result))
      (body (MM0GeneralMapNamesV1 ?rest ?map ?check)
        (MM0GeneralMappedTailV1 ?name ?check ?result)))
    (rule mm0-general-mapped-tail-accepted-v1
      (head (MM0GeneralMappedTailV1 ?name (MM0CheckAcceptedV1 ?mapped)
        (MM0CheckAcceptedV1 (cons ?name ?mapped)))) (body))
    (rule mm0-general-mapped-tail-refused-v1
      (head (MM0GeneralMappedTailV1 ?name (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-dependencies-refused-v1
      (head (MM0GeneralDependenciesV1 ?old (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-dependencies-mapped-v1
      (head (MM0GeneralDependenciesV1 ?old (MM0CheckAcceptedV1 ?new) ?result))
      (body (MM0GeneralSubsetV1 ?old ?new ?first)
        (MM0GeneralSubsetAfterFirstV1 ?old ?new ?first ?result)))
    (rule mm0-general-subset-empty-v1
      (head (MM0GeneralSubsetV1 nil ?other (MM0CheckAcceptedV1 MM0GeneralTypesEqualV1))) (body))
    (rule mm0-general-subset-cons-v1
      (head (MM0GeneralSubsetV1 (cons ?name ?rest) ?other ?result))
      (body (MM0NameLookupV1 ?name ?other ?lookup)
        (MM0GeneralSubsetAfterLookupV1 ?rest ?other ?lookup ?result)))
    (rule mm0-general-subset-missing-v1
      (head (MM0GeneralSubsetAfterLookupV1 ?rest ?other MM0NameMissingV1
        (MM0CheckRefusedV1 MM0GeneralSignatureMismatchV1))) (body))
    (rule mm0-general-subset-found-v1
      (head (MM0GeneralSubsetAfterLookupV1 ?rest ?other MM0NameFoundV1 ?result))
      (body (MM0GeneralSubsetV1 ?rest ?other ?result)))
    (rule mm0-general-subset-first-refused-v1
      (head (MM0GeneralSubsetAfterFirstV1 ?old ?new (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-subset-both-v1
      (head (MM0GeneralSubsetAfterFirstV1 ?old ?new
        (MM0CheckAcceptedV1 MM0GeneralTypesEqualV1) ?result))
      (body (MM0GeneralSubsetV1 ?new ?old ?result)))
    (rule mm0-general-signature-refused-v1
      (head (MM0GeneralAfterSignatureV1
        (MM0GeneralRequestV1 ?position ?term ?state ?bindersAst ?returnAst ?headAst ?lits)
        ?binders (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 (MM0RefusedNotationSignatureV1 ?position ?term)))) (body))
    (rule mm0-general-signature-accepted-v1
      (head (MM0GeneralAfterSignatureV1
        (MM0GeneralRequestV1 ?position ?term
          (MM0SourceStateV1 ?textual ?notation) ?bindersAst ?returnAst
          (node mm0-precedence-constant (pair ?constantAst ?precedenceAst)) ?lits)
        ?binders (MM0CheckAcceptedV1 MM0GeneralTypesEqualV1) ?result))
      (body (MM0GeneralBinderNamesV1 ?binders ?names)
        (MM0PrecedenceFromAstV1 ?precedenceAst ?precedence)
        (MM0CoercionViewV1 ?notation
          (MM0NotationEnvironmentV1 ?delimiters ?constants ?prefixes ?infixes) ?edges)
        (MM0NotationConstantV1 ?delimiters ?constantAst ?check)
        (MM0GeneralAfterHeadConstantV1
          (MM0GeneralRequestV1 ?position ?term (MM0SourceStateV1 ?textual ?notation)
            ?bindersAst ?returnAst
            (node mm0-precedence-constant (pair ?constantAst ?precedenceAst)) ?lits)
          ?names ?precedence ?check ?result)))
    (rule mm0-general-binder-names-empty-v1
      (head (MM0GeneralBinderNamesV1 nil nil)) (body))
    (rule mm0-general-binder-names-cons-v1
      (head (MM0GeneralBinderNamesV1
        (cons (MM0BinderV1 ?kind (MM0NamedBinderV1 ?name) ?type) ?rest) (cons ?name ?names)))
      (body (MM0GeneralBinderNamesV1 ?rest ?names)))
    (rule mm0-general-head-constant-refused-v1
      (head (MM0GeneralAfterHeadConstantV1 ?request ?names ?prec
        (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-head-constant-accepted-v1
      (head (MM0GeneralAfterHeadConstantV1
        (MM0GeneralRequestV1 ?position ?term (MM0SourceStateV1 ?textual ?notation)
          ?bindersAst ?returnAst ?headAst ?lits)
        ?names ?prec (MM0CheckAcceptedV1 ?token) ?result))
      (body (MM0CoercionViewV1 ?notation
          (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?edges)
        (MM0PrefixLookupV1 ?token ?p ?prefixLookup)
        (MM0GeneralInfixyLookupV1 ?token (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?infixyLookup)
        (MM0GeneralAfterHeadLookupsV1
          (MM0GeneralPendingV1
            (MM0GeneralRequestV1 ?position ?term (MM0SourceStateV1 ?textual ?notation)
              ?bindersAst ?returnAst ?headAst ?lits) ?names ?token ?prec
              (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?edges)
          ?prefixLookup ?infixyLookup ?result)))
    (rule mm0-general-head-prefix-refused-v1
      (head (MM0GeneralAfterHeadLookupsV1
        (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term ?state ?bs ?rt ?ha ?ls)
          ?names ?token ?prec ?base ?edges) (MM0PrefixFoundV1 ?first) ?infixy
        (MM0CheckRefusedV1 (MM0RefusedNotationRedeclarationV1 ?position ?token ?first)))) (body))
    (rule mm0-general-head-infixy-refused-v1
      (head (MM0GeneralAfterHeadLookupsV1
        (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term ?state ?bs ?rt ?ha ?ls)
          ?names ?token ?prec ?base ?edges) MM0PrefixMissingV1 (MM0GeneralInfixyFoundV1 ?p ?first)
        (MM0CheckRefusedV1 (MM0RefusedNotationRedeclarationV1 ?position ?token ?first)))) (body))
    (rule mm0-general-head-accepted-v1
      (head (MM0GeneralAfterHeadLookupsV1
        (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term ?state ?bs ?rt ?ha ?lits)
          ?names ?token ?prec ?base ?edges) MM0PrefixMissingV1 MM0GeneralInfixyMissingV1 ?result))
      (body (MM0GeneralPatternV1 ?position ?base ?token ?prec ?names ?names ?lits
          MM0GeneralAfterConstantRoleV1 ?check)
        (MM0GeneralAfterPatternV1
          (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term ?state ?bs ?rt ?ha ?lits)
            ?names ?token ?prec ?base ?edges) ?check ?result)))

    (rule mm0-general-prefix-lookup-found-v1
      (head (MM0PrefixLookupV1 ?token
        (MM0PrefixEntriesConsV1 (MM0GeneralNotationEntryV1 ?token ?term ?names ?prec ?pattern ?pos) ?rest)
        (MM0PrefixFoundV1 ?pos))) (body))
    (rule mm0-general-prefix-lookup-tail-v1
      (head (MM0PrefixLookupV1 ?token
        (MM0PrefixEntriesConsV1 (MM0GeneralNotationEntryV1 ?other ?term ?names ?prec ?pattern ?pos) ?rest) ?result))
      (body (different ?token ?other) (MM0PrefixLookupV1 ?token ?rest ?result)))
    (rule mm0-general-infixy-lookup-v1
      (head (MM0GeneralInfixyLookupV1 ?token (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?result))
      (body (MM0InfixLookupV1 ?token ?i ?lookup)
        (MM0GeneralInfixyAfterBinaryV1 ?token (MM0GeneralInfixyTablesV1 ?c ?p) ?lookup ?result)))
    (rule mm0-general-infixy-binary-found-v1
      (head (MM0GeneralInfixyAfterBinaryV1 ?token (MM0GeneralInfixyTablesV1 ?constants ?prefixes) (MM0InfixFoundV1 ?pos)
        (MM0GeneralInfixyFoundV1 ?prec ?pos)))
      (body (MM0ConstantLookupV1 ?token ?constants (MM0ConstantFoundV1 ?prec ?first))))
    (rule mm0-general-infixy-binary-missing-v1
      (head (MM0GeneralInfixyAfterBinaryV1 ?token (MM0GeneralInfixyTablesV1 ?constants ?prefixes) MM0InfixMissingV1 ?result))
      (body (MM0GeneralInfixyPrefixesV1 ?token ?prefixes ?result)))
    (rule mm0-general-infixy-prefixes-empty-v1
      (head (MM0GeneralInfixyPrefixesV1 ?token MM0PrefixEntriesNilV1 MM0GeneralInfixyMissingV1)) (body))
    (rule mm0-general-infixy-prefixes-simple-v1
      (head (MM0GeneralInfixyPrefixesV1 ?token
        (MM0PrefixEntriesConsV1 (MM0PrefixNotationEntryV1 ?h ?t ?a ?p ?pos) ?rest) ?result))
      (body (MM0GeneralInfixyPrefixesV1 ?token ?rest ?result)))
    (rule mm0-general-infixy-prefixes-general-v1
      (head (MM0GeneralInfixyPrefixesV1 ?token
        (MM0PrefixEntriesConsV1 (MM0GeneralNotationEntryV1 ?h ?t ?names ?p ?pattern ?pos) ?rest) ?result))
      (body (MM0GeneralInfixyPatternV1 ?token ?pattern ?pos ?lookup)
        (MM0GeneralInfixyAfterPatternV1 ?token ?rest ?lookup ?result)))
    (rule mm0-general-infixy-pattern-empty-v1
      (head (MM0GeneralInfixyPatternV1 ?token nil ?position MM0GeneralInfixyMissingV1)) (body))
    (rule mm0-general-infixy-pattern-variable-v1
      (head (MM0GeneralInfixyPatternV1 ?token (cons (MM0GeneralVariableV1 ?name ?min) ?rest) ?position ?result))
      (body (MM0GeneralInfixyPatternV1 ?token ?rest ?position ?result)))
    (rule mm0-general-infixy-pattern-plain-v1
      (head (MM0GeneralInfixyPatternV1 ?token
        (cons (MM0GeneralLiteralV1 ?other ?prec MM0GeneralAfterConstantRoleV1) ?rest) ?position ?result))
      (body (MM0GeneralInfixyPatternV1 ?token ?rest ?position ?result)))
    (rule mm0-general-infixy-pattern-found-v1
      (head (MM0GeneralInfixyPatternV1 ?token
        (cons (MM0GeneralLiteralV1 ?token ?prec MM0GeneralAfterVariableRoleV1) ?rest) ?position
        (MM0GeneralInfixyFoundV1 ?prec ?position))) (body))
    (rule mm0-general-infixy-pattern-tail-v1
      (head (MM0GeneralInfixyPatternV1 ?token
        (cons (MM0GeneralLiteralV1 ?other ?prec MM0GeneralAfterVariableRoleV1) ?rest) ?position ?result))
      (body (different ?token ?other) (MM0GeneralInfixyPatternV1 ?token ?rest ?position ?result)))
    (rule mm0-general-infixy-pattern-missing-v1
      (head (MM0GeneralInfixyAfterPatternV1 ?token ?rest MM0GeneralInfixyMissingV1 ?result))
      (body (MM0GeneralInfixyPrefixesV1 ?token ?rest ?result)))
    (rule mm0-general-infixy-pattern-accepted-v1
      (head (MM0GeneralInfixyAfterPatternV1 ?token ?rest (MM0GeneralInfixyFoundV1 ?prec ?pos)
        (MM0GeneralInfixyFoundV1 ?prec ?pos))) (body))

    ; Each notation variable occurs exactly once. Its parse minimum is
    ; determined by the next literal, using the documented P(lits, q).
    (rule mm0-general-pattern-empty-v1
      (head (MM0GeneralPatternV1 ?position ?base ?head ?prec ?all nil nil ?previous
        (MM0CheckAcceptedV1 (MM0GeneralPatternAcceptedV1 nil ?base)))) (body))
    (rule mm0-general-pattern-unused-v1
      (head (MM0GeneralPatternV1 ?position ?base ?head ?prec ?all (cons ?name ?names) nil ?previous
        (MM0CheckRefusedV1 (MM0RefusedNotationUnusedVariableV1 ?position ?name)))) (body))
    (rule mm0-general-pattern-variable-v1
      (head (MM0GeneralPatternV1 ?position ?base ?head ?prec ?all ?remaining
        (cons (node mm0-identifier ?chars) ?rest) ?previous ?result))
      (body (MM0IdentifierScalarsV1 (node mm0-identifier ?chars) ?name)
        (MM0NameLookupV1 ?name ?remaining ?lookup)
        (MM0GeneralAfterVariableV1
          (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
          ?name ?lookup ?result)))
    (rule mm0-general-pattern-variable-missing-v1
      (head (MM0GeneralAfterVariableV1
        (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
        ?name MM0NameMissingV1 ?result))
      (body (MM0NameLookupV1 ?name ?all ?lookup)
        (MM0GeneralUnknownVariableV1 ?position ?name ?lookup ?result)))
    (rule mm0-general-pattern-variable-unknown-v1
      (head (MM0GeneralUnknownVariableV1 ?position ?name MM0NameMissingV1
        (MM0CheckRefusedV1 (MM0RefusedNotationVariableV1 ?position ?name MM0GeneralUnknownVariableKindV1)))) (body))
    (rule mm0-general-pattern-variable-duplicate-v1
      (head (MM0GeneralUnknownVariableV1 ?position ?name MM0NameFoundV1
        (MM0CheckRefusedV1 (MM0RefusedNotationVariableV1 ?position ?name MM0GeneralDuplicateVariableKindV1)))) (body))
    (rule mm0-general-pattern-variable-found-v1
      (head (MM0GeneralAfterVariableV1
        (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
        ?name MM0NameFoundV1 ?result))
      (body (MM0GeneralVariableMinimumV1 ?prec ?rest ?check)
        (MM0GeneralAfterMinimumV1
          (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
          ?name ?check ?result)))
    (rule mm0-general-remove-name-head-v1
      (head (MM0GeneralRemoveNameV1 ?name (cons ?name ?rest) ?rest)) (body))
    (rule mm0-general-remove-name-tail-v1
      (head (MM0GeneralRemoveNameV1 ?name (cons ?other ?rest) (cons ?other ?after)))
      (body (different ?name ?other) (MM0GeneralRemoveNameV1 ?name ?rest ?after)))
    (rule mm0-general-variable-minimum-last-v1
      (head (MM0GeneralVariableMinimumV1 ?prec nil (MM0CheckAcceptedV1 ?prec))) (body))
    (rule mm0-general-variable-minimum-adjacent-v1
      (head (MM0GeneralVariableMinimumV1 ?prec (cons (node mm0-identifier ?chars) ?rest)
        (MM0CheckAcceptedV1 MM0MaximumPrecedenceV1))) (body))
    (rule mm0-general-variable-minimum-constant-v1
      (head (MM0GeneralVariableMinimumV1 ?headPrec
        (cons (node mm0-precedence-constant (pair ?constant ?precAst)) ?rest) ?result))
      (body (MM0PrecedenceFromAstV1 ?precAst ?precedence)
        (MM0GeneralMinimumAfterPrecedenceV1 ?precedence ?result)))
    (rule mm0-general-minimum-finite-v1
      (head (MM0GeneralMinimumAfterPrecedenceV1 (MM0FinitePrecedenceV1 ?digits)
        (MM0CheckAcceptedV1 (GSLTPrattStrictMinimumV1 (MM0FinitePrecedenceV1 ?digits))))) (body))
    (rule mm0-general-minimum-maximum-v1
      (head (MM0GeneralMinimumAfterPrecedenceV1 MM0MaximumPrecedenceV1
        (MM0CheckRefusedV1 MM0GeneralInfixyMaximumV1))) (body))
    (rule mm0-general-minimum-refused-v1
      (head (MM0GeneralAfterMinimumV1
        (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
        ?name (MM0CheckRefusedV1 MM0GeneralInfixyMaximumV1)
        (MM0CheckRefusedV1 (MM0RefusedNotationInfixyMaximumV1 ?position ?name)))) (body))
    (rule mm0-general-minimum-accepted-v1
      (head (MM0GeneralAfterMinimumV1
        (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
        ?name (MM0CheckAcceptedV1 ?minimum) ?result))
      (body (MM0GeneralRemoveNameV1 ?name ?remaining ?after)
        (MM0GeneralPatternV1 ?position ?base ?head ?prec ?all ?after ?rest
          MM0GeneralAfterVariableRoleV1 ?check)
        (MM0GeneralAfterLiteralV1 (MM0GeneralVariableV1 ?name ?minimum) ?check ?result)))
    (rule mm0-general-pattern-constant-v1
      (head (MM0GeneralPatternV1 ?position
        (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?head ?prec ?all ?remaining
        (cons (node mm0-precedence-constant (pair ?constantAst ?precAst)) ?rest) ?previous ?result))
      (body (MM0PrecedenceFromAstV1 ?precAst ?constantPrec)
        (MM0NotationConstantV1 ?d ?constantAst ?check)
        (MM0GeneralAfterConstantV1
          (MM0GeneralPatternRequestV1 ?position (MM0NotationEnvironmentV1 ?d ?c ?p ?i)
            ?head ?prec ?all ?remaining ?rest ?previous) ?constantPrec ?check ?result)))
    (rule mm0-general-pattern-constant-refused-v1
      (head (MM0GeneralAfterConstantV1 ?request ?prec (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-pattern-constant-accepted-v1
      (head (MM0GeneralAfterConstantV1
        (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
        ?constantPrec (MM0CheckAcceptedV1 ?token) ?result))
      (body (MM0GeneralRegisterConstantV1 ?position ?token ?constantPrec ?previous ?head ?base ?check)
        (MM0GeneralAfterRegisteredV1
          (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
          ?token ?constantPrec ?check ?result)))
    (rule mm0-general-registered-refused-v1
      (head (MM0GeneralAfterRegisteredV1 ?request ?token ?prec (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-registered-accepted-v1
      (head (MM0GeneralAfterRegisteredV1
        (MM0GeneralPatternRequestV1 ?position ?base ?head ?prec ?all ?remaining ?rest ?previous)
        ?token ?constantPrec (MM0CheckAcceptedV1 ?afterBase) ?result))
      (body (MM0GeneralPatternV1 ?position ?afterBase ?head ?prec ?all ?remaining ?rest
          MM0GeneralAfterConstantRoleV1 ?check)
        (MM0GeneralAfterLiteralV1 (MM0GeneralLiteralV1 ?token ?constantPrec ?previous) ?check ?result)))
    (rule mm0-general-literal-tail-refused-v1
      (head (MM0GeneralAfterLiteralV1 ?literal (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-literal-tail-accepted-v1
      (head (MM0GeneralAfterLiteralV1 ?literal
        (MM0CheckAcceptedV1 (MM0GeneralPatternAcceptedV1 ?pattern ?base))
        (MM0CheckAcceptedV1 (MM0GeneralPatternAcceptedV1 (cons ?literal ?pattern) ?base)))) (body))

    ; Only constants immediately after variables acquire infix precedence.
    ; Other literal constants may be shared at different annotated levels.
    (rule mm0-general-register-plain-v1
      (head (MM0GeneralRegisterConstantV1 ?position ?token ?prec
        MM0GeneralAfterConstantRoleV1 ?head (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?result))
      (body (MM0ConstantLookupV1 ?token ?c ?lookup)
        (MM0GeneralConstantAfterLookupV1
          (MM0GeneralConstantRequestV1 ?position ?token ?prec MM0GeneralAfterConstantRoleV1
            (MM0NotationEnvironmentV1 ?d ?c ?p ?i)) ?lookup ?result)))
    (rule mm0-general-register-infixy-v1
      (head (MM0GeneralRegisterConstantV1 ?position ?token ?prec MM0GeneralAfterVariableRoleV1
        ?head (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?result))
      (body (MM0GeneralCompareTokensV1 ?token ?head ?comparison)
        (MM0GeneralRegisterAfterHeadV1
          (MM0GeneralConstantRequestV1 ?position ?token ?prec MM0GeneralAfterVariableRoleV1
            (MM0NotationEnvironmentV1 ?d ?c ?p ?i)) ?comparison ?result)))
    (rule mm0-general-compare-tokens-equal-v1
      (head (MM0GeneralCompareTokensV1 ?token ?token MM0GeneralTokensEqualV1)) (body))
    (rule mm0-general-compare-tokens-different-v1
      (head (MM0GeneralCompareTokensV1 ?left ?right MM0GeneralTokensDifferentV1))
      (body (different ?left ?right)))
    (rule mm0-general-register-own-head-refused-v1
      (head (MM0GeneralRegisterAfterHeadV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role ?base) MM0GeneralTokensEqualV1
        (MM0CheckRefusedV1 (MM0RefusedNotationRedeclarationV1 ?position ?token ?position)))) (body))
    (rule mm0-general-register-other-head-v1
      (head (MM0GeneralRegisterAfterHeadV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role (MM0NotationEnvironmentV1 ?d ?c ?p ?i))
        MM0GeneralTokensDifferentV1 ?result))
      (body (MM0PrefixLookupV1 ?token ?p ?prefixLookup)
        (MM0GeneralInfixyLookupV1 ?token (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?infixyLookup)
        (MM0ConstantLookupV1 ?token ?c ?constantLookup)
        (MM0GeneralRegisterAfterLookupsV1
          (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role
            (MM0NotationEnvironmentV1 ?d ?c ?p ?i)) ?prefixLookup ?infixyLookup ?constantLookup ?result)))
    (rule mm0-general-register-prefix-refused-v1
      (head (MM0GeneralRegisterAfterLookupsV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role ?base)
        (MM0PrefixFoundV1 ?first) ?infixy ?constant
        (MM0CheckRefusedV1 (MM0RefusedNotationRedeclarationV1 ?position ?token ?first)))) (body))
    (rule mm0-general-register-precedence-refused-v1
      (head (MM0GeneralRegisterAfterLookupsV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role ?base)
        MM0PrefixMissingV1 (MM0GeneralInfixyFoundV1 ?oldPrec ?first) ?constant
        (MM0CheckRefusedV1 (MM0RefusedNotationPrecedenceConflictV1 ?position ?token ?oldPrec ?prec))))
      (body (different ?oldPrec ?prec)))
    (rule mm0-general-register-infixy-new-v1
      (head (MM0GeneralRegisterAfterLookupsV1 ?request MM0PrefixMissingV1 MM0GeneralInfixyMissingV1
        ?constant ?result))
      (body (MM0GeneralConstantAfterLookupV1 ?request ?constant ?result)))
    (rule mm0-general-register-infixy-shared-v1
      (head (MM0GeneralRegisterAfterLookupsV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role ?base)
        MM0PrefixMissingV1 (MM0GeneralInfixyFoundV1 ?prec ?first) ?constant ?result))
      (body (MM0GeneralConstantAfterLookupV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role ?base) ?constant ?result)))
    (rule mm0-general-constant-new-v1
      (head (MM0GeneralConstantAfterLookupV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec ?role (MM0NotationEnvironmentV1 ?d ?c ?p ?i))
        MM0ConstantMissingV1 (MM0CheckAcceptedV1 (MM0NotationEnvironmentV1 ?d ?after ?p ?i))))
      (body (MM0ConstantEntriesAppendV1 ?c (MM0ConstantEntryV1 ?token ?prec ?position) ?after)))
    (rule mm0-general-constant-plain-shared-v1
      (head (MM0GeneralConstantAfterLookupV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec MM0GeneralAfterConstantRoleV1 ?base)
        (MM0ConstantFoundV1 ?oldPrec ?first) (MM0CheckAcceptedV1 ?base))) (body))
    (rule mm0-general-constant-infixy-shared-v1
      (head (MM0GeneralConstantAfterLookupV1
        (MM0GeneralConstantRequestV1 ?position ?token ?prec MM0GeneralAfterVariableRoleV1
          (MM0NotationEnvironmentV1 ?d ?c ?p ?i)) (MM0ConstantFoundV1 ?oldPrec ?first)
        (MM0CheckAcceptedV1 (MM0NotationEnvironmentV1 ?d ?after ?p ?i))))
      (body (MM0GeneralReplaceConstantV1 ?c ?token ?prec ?after)))
    (rule mm0-general-replace-constant-head-v1
      (head (MM0GeneralReplaceConstantV1
        (MM0ConstantEntriesConsV1 (MM0ConstantEntryV1 ?token ?oldPrec ?first) ?rest) ?token ?prec
        (MM0ConstantEntriesConsV1 (MM0ConstantEntryV1 ?token ?prec ?first) ?rest))) (body))
    (rule mm0-general-replace-constant-tail-v1
      (head (MM0GeneralReplaceConstantV1
        (MM0ConstantEntriesConsV1 (MM0ConstantEntryV1 ?other ?oldPrec ?first) ?rest) ?token ?prec
        (MM0ConstantEntriesConsV1 (MM0ConstantEntryV1 ?other ?oldPrec ?first) ?after)))
      (body (different ?token ?other) (MM0GeneralReplaceConstantV1 ?rest ?token ?prec ?after)))
    (rule mm0-general-install-constant-v1
      (head (MM0GeneralInstallConstantV1 ?position ?token ?prec (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?result))
      (body (MM0ConstantLookupV1 ?token ?c ?lookup)
        (MM0GeneralConstantAfterLookupV1
          (MM0GeneralConstantRequestV1 ?position ?token ?prec MM0GeneralAfterVariableRoleV1
            (MM0NotationEnvironmentV1 ?d ?c ?p ?i)) ?lookup ?result)))
    (rule mm0-general-pattern-refused-v1
      (head (MM0GeneralAfterPatternV1 ?pending (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-pattern-accepted-v1
      (head (MM0GeneralAfterPatternV1
        (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term (MM0SourceStateV1 ?textual ?notation)
          ?bs ?rt ?ha ?ls) ?names ?token ?prec ?before ?edges)
        (MM0CheckAcceptedV1 (MM0GeneralPatternAcceptedV1 ?pattern ?base)) ?result))
      (body (MM0GeneralPatternCheckV1 ?position ?pattern ?check)
        (MM0GeneralInstallAfterCheckV1
          (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term (MM0SourceStateV1 ?textual ?notation)
            ?bs ?rt ?ha ?ls) ?names ?token ?prec ?before ?edges)
          (MM0GeneralPatternAcceptedV1 ?pattern ?base) ?check ?result)))
    (rule mm0-general-pattern-check-empty-v1
      (head (MM0GeneralPatternCheckV1 ?position nil (MM0CheckAcceptedV1 MM0GeneralPatternValidV1))) (body))
    (rule mm0-general-pattern-check-variable-v1
      (head (MM0GeneralPatternCheckV1 ?position (cons (MM0GeneralVariableV1 ?name ?min) ?rest) ?result))
      (body (MM0GeneralPatternCheckV1 ?position ?rest ?result)))
    (rule mm0-general-pattern-check-plain-v1
      (head (MM0GeneralPatternCheckV1 ?position
        (cons (MM0GeneralLiteralV1 ?token ?prec MM0GeneralAfterConstantRoleV1) ?rest) ?result))
      (body (MM0GeneralPatternCheckV1 ?position ?rest ?result)))
    (rule mm0-general-pattern-check-infixy-v1
      (head (MM0GeneralPatternCheckV1 ?position
        (cons (MM0GeneralLiteralV1 ?token ?prec MM0GeneralAfterVariableRoleV1) ?rest) ?result))
      (body (MM0GeneralInfixyPatternV1 ?token ?rest ?position ?lookup)
        (MM0GeneralPatternAfterLookupV1 ?position ?token ?prec ?rest ?lookup ?result)))
    (rule mm0-general-pattern-check-new-v1
      (head (MM0GeneralPatternAfterLookupV1 ?position ?token ?prec ?rest MM0GeneralInfixyMissingV1 ?result))
      (body (MM0GeneralPatternCheckV1 ?position ?rest ?result)))
    (rule mm0-general-pattern-check-same-v1
      (head (MM0GeneralPatternAfterLookupV1 ?position ?token ?prec ?rest (MM0GeneralInfixyFoundV1 ?prec ?first) ?result))
      (body (MM0GeneralPatternCheckV1 ?position ?rest ?result)))
    (rule mm0-general-pattern-check-conflict-v1
      (head (MM0GeneralPatternAfterLookupV1 ?position ?token ?prec ?rest (MM0GeneralInfixyFoundV1 ?other ?first)
        (MM0CheckRefusedV1 (MM0RefusedNotationPrecedenceConflictV1 ?position ?token ?prec ?other))))
      (body (different ?prec ?other)))
    (rule mm0-general-install-check-refused-v1
      (head (MM0GeneralInstallAfterCheckV1 ?pending ?pattern (MM0CheckRefusedV1 ?reason)
        (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-general-install-checked-v1
      (head (MM0GeneralInstallAfterCheckV1
        (MM0GeneralPendingV1 (MM0GeneralRequestV1 ?position ?term (MM0SourceStateV1 ?textual ?notation)
          ?bs ?rt ?ha ?ls) ?names ?token ?prec ?before ?edges)
        (MM0GeneralPatternAcceptedV1 ?pattern ?base) (MM0CheckAcceptedV1 MM0GeneralPatternValidV1)
        (MM0CheckAcceptedV1 (MM0GeneralInstalledV1 ?afterNotation
          (MM0DeclaredGeneralNotationV1 ?position ?term ?token ?pattern)))))
      (body (MM0GeneralInstallConstantV1 ?position ?token ?prec ?base
          (MM0CheckAcceptedV1 (MM0NotationEnvironmentV1 ?d ?c ?p ?i)))
        (MM0PrefixEntriesAppendV1 ?p
          (MM0GeneralNotationEntryV1 ?token ?term ?names ?prec ?pattern ?position) ?afterPrefixes)
        (MM0GeneralRestoreV1 ?notation (MM0NotationEnvironmentV1 ?d ?c ?afterPrefixes ?i) ?afterNotation)))
    (rule mm0-general-restore-plain-v1
      (head (MM0GeneralRestoreV1 (MM0NotationEnvironmentV1 ?d ?c ?p ?i) ?base ?base)) (body))
    (rule mm0-general-restore-coercions-v1
      (head (MM0GeneralRestoreV1 (MM0NotationWithCoercionsV1 ?before ?edges) ?base
        (MM0NotationWithCoercionsV1 ?base ?edges))) (body))
    (rule mm0-source-statement-class-general-v1
      (head (MM0StatementClassV1 (node mm0-general-notation-statement ?payload) MM0GeneralStatementV1)) (body))
    (rule mm0-source-step-general-v1
      (head (MM0SourceStepByClassV1 ?position ?ast ?state MM0GeneralStatementV1 ?result))
      (body (MM0GeneralValidateV1 ?position ?ast ?state ?check)
        (MM0GeneralStepAfterCheckV1 ?state ?check ?result)))
    (rule mm0-source-step-general-accepted-v1
      (head (MM0GeneralStepAfterCheckV1 (MM0SourceStateV1 ?textual ?before)
        (MM0CheckAcceptedV1 (MM0GeneralInstalledV1 ?after ?history))
        (MM0SourceStepAcceptedV1 (MM0SourceStateV1 ?textual ?after) ?history))) (body))
    (rule mm0-source-step-general-refused-v1
      (head (MM0GeneralStepAfterCheckV1 ?state (MM0CheckRefusedV1 ?reason)
        (MM0SourceStepRefusedV1 ?reason ?state ?reason))) (body))

    ; Coercions extend notation metadata without changing the declaration
    ; namespace. Existing files retain the original four-field notation value.
    (rule mm0-coercion-view-empty-v1
      (head (MM0CoercionViewV1
        (MM0NotationEnvironmentV1 ?d ?c ?p ?i)
        (MM0NotationEnvironmentV1 ?d ?c ?p ?i) MM0CoercionsNilV1)) (body))
    (rule mm0-coercion-view-present-v1
      (head (MM0CoercionViewV1
        (MM0NotationWithCoercionsV1 ?base ?edges) ?base ?edges)) (body))
    (rule mm0-coercion-ast-v1
      (head (MM0CoercionAstV1
        (node mm0-coercion-statement (pair ?term (pair ?from ?to))) ?name ?s ?t))
      (body (MM0IdentifierScalarsV1 ?term ?name)
        (MM0IdentifierScalarsV1 ?from ?s) (MM0IdentifierScalarsV1 ?to ?t)))
    (rule mm0-coercion-validate-v1
      (head (MM0CoercionValidateV1 ?position ?ast
        (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation) ?result))
      (body (MM0CoercionAstV1 ?ast ?term ?from ?to)
        (MM0TermSignatureLookupV1 ?term ?decls ?lookup)
        (MM0CoercionAfterTermV1
          (MM0CoercionRequestV1 ?position ?term ?from ?to
            (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
          ?lookup ?result)))
    (rule mm0-coercion-term-missing-v1
      (head (MM0CoercionAfterTermV1
        (MM0CoercionRequestV1 ?position ?term ?from ?to ?state)
        MM0TermSignatureMissingV1
        (MM0CheckRefusedV1 (MM0RefusedUnknownNotationTermV1 ?position ?term)))) (body))
    (rule mm0-coercion-term-found-v1
      (head (MM0CoercionAfterTermV1
        (MM0CoercionRequestV1 ?position ?term ?from ?to
          (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
        (MM0TermSignatureFoundV1 ?signature ?first) ?result))
      (body (MM0SortLookupV1 ?from ?sorts ?fromLookup)
        (MM0SortLookupV1 ?to ?sorts ?toLookup)
        (MM0CoercionAfterSortsV1
          (MM0CoercionRequestV1 ?position ?term ?from ?to
            (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
          ?signature ?fromLookup ?toLookup ?result)))
    (rule mm0-coercion-source-sort-missing-v1
      (head (MM0CoercionAfterSortsV1
        (MM0CoercionRequestV1 ?position ?term ?from ?to ?state)
        ?sig MM0SortMissingV1 ?toLookup
        (MM0CheckRefusedV1 (MM0RefusedCoercionSortV1 ?position ?from)))) (body))
    (rule mm0-coercion-target-sort-missing-v1
      (head (MM0CoercionAfterSortsV1
        (MM0CoercionRequestV1 ?position ?term ?from ?to ?state)
        ?sig (MM0SortFoundV1 ?flags ?first) MM0SortMissingV1
        (MM0CheckRefusedV1 (MM0RefusedCoercionSortV1 ?position ?to)))) (body))
    (rule mm0-coercion-sorts-found-v1
      (head (MM0CoercionAfterSortsV1
        (MM0CoercionRequestV1 ?position ?term ?from ?to
          (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
        ?signature (MM0SortFoundV1 ?fromFlags ?fromFirst)
        (MM0SortFoundV1 ?toFlags ?toFirst) ?result))
      (body (MM0CoercionViewV1 ?notation ?base ?edges)
        (MM0CoercionSignatureV1 ?position ?term ?from ?to ?signature ?check)
        (MM0CoercionAfterSignatureV1
          (MM0CoercionPendingV1
            (MM0CoercionRequestV1 ?position ?term ?from ?to
              (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
            ?base ?edges (MM0CoercionEntryV1 ?term ?from ?to ?position)) ?check ?result)))
    (rule mm0-coercion-signature-nullary-v1
      (head (MM0CoercionSignatureV1 ?position ?term ?from ?to
        (MM0TermSignatureV1 nil ?type)
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term)))) (body))
    (rule mm0-coercion-signature-many-v1
      (head (MM0CoercionSignatureV1 ?position ?term ?from ?to
        (MM0TermSignatureV1 (cons ?first (cons ?second ?rest)) ?type)
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term)))) (body))
    (rule mm0-coercion-signature-bound-v1
      (head (MM0CoercionSignatureV1 ?position ?term ?from ?to
        (MM0TermSignatureV1 (cons (MM0BinderV1 MM0BoundBinderKindV1 ?name ?type) nil) ?return)
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term)))) (body))
    (rule mm0-coercion-signature-regular-v1
      (head (MM0CoercionSignatureV1 ?position ?term ?from ?to
        (MM0TermSignatureV1
          (cons (MM0BinderV1 MM0RegularBinderKindV1 ?name (MM0TypeV1 ?actualFrom ?deps)) nil)
          (MM0TypeV1 ?actualTo ?returnDeps)) ?result))
      (body (MM0CoercionSignatureTypesV1 ?position ?term ?from ?to
        (MM0TypeV1 ?actualFrom ?deps) (MM0TypeV1 ?actualTo ?returnDeps) ?result)))
    (rule mm0-coercion-signature-accepted-v1
      (head (MM0CoercionSignatureTypesV1 ?position ?term ?from ?to
        (MM0TypeV1 ?from nil) (MM0TypeV1 ?to nil)
        (MM0CheckAcceptedV1 MM0CoercionSignatureAcceptedV1))) (body))
    (rule mm0-coercion-signature-source-mismatch-v1
      (head (MM0CoercionSignatureTypesV1 ?position ?term ?from ?to
        (MM0TypeV1 ?actual ?deps) ?return
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term))))
      (body (different ?from ?actual)))
    (rule mm0-coercion-signature-target-mismatch-v1
      (head (MM0CoercionSignatureTypesV1 ?position ?term ?from ?to
        (MM0TypeV1 ?from ?deps) (MM0TypeV1 ?actual ?returnDeps)
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term))))
      (body (different ?to ?actual)))
    (rule mm0-coercion-signature-input-dependencies-v1
      (head (MM0CoercionSignatureTypesV1 ?position ?term ?from ?to
        (MM0TypeV1 ?from (cons ?dep ?rest)) (MM0TypeV1 ?to ?returnDeps)
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term)))) (body))
    (rule mm0-coercion-signature-output-dependencies-v1
      (head (MM0CoercionSignatureTypesV1 ?position ?term ?from ?to
        (MM0TypeV1 ?from nil) (MM0TypeV1 ?to (cons ?dep ?rest))
        (MM0CheckRefusedV1 (MM0RefusedCoercionSignatureV1 ?position ?term)))) (body))
    (rule mm0-coercion-signature-refused-v1
      (head (MM0CoercionAfterSignatureV1 ?pending
        (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason))) (body))
    (rule mm0-coercion-signature-check-forest-v1
      (head (MM0CoercionAfterSignatureV1
        (MM0CoercionPendingV1 ?request ?base ?edges
          (MM0CoercionEntryV1 ?term ?from ?to ?position))
        (MM0CheckAcceptedV1 MM0CoercionSignatureAcceptedV1) ?result))
      (body (MM0CoercionReachV1 ?edges MM0CoercionUndirectedV1 ?from ?to ?connected)
        (MM0CoercionAfterForestV1
          (MM0CoercionPendingV1 ?request ?base ?edges
            (MM0CoercionEntryV1 ?term ?from ?to ?position)) ?connected ?result)))
    (rule mm0-coercion-forest-refused-v1
      (head (MM0CoercionAfterForestV1
        (MM0CoercionPendingV1 ?request ?base ?edges
          (MM0CoercionEntryV1 ?term ?from ?to ?position)) MM0CoercionConnectedV1
        (MM0CheckRefusedV1 (MM0RefusedCoercionForestV1 ?position ?from ?to)))) (body))
    (rule mm0-coercion-forest-accepted-v1
      (head (MM0CoercionAfterForestV1
        (MM0CoercionPendingV1
          (MM0CoercionRequestV1 ?position ?term ?from ?to
            (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
          ?base ?edges ?edge) MM0CoercionSeparateV1 ?result))
      (body (MM0CoercionsAppendV1 ?edges ?edge ?after)
        (MM0CoercionGraphCheckV1 ?sorts ?after ?check)
        (MM0CoercionAfterProvableV1
          (MM0CoercionPendingV1
            (MM0CoercionRequestV1 ?position ?term ?from ?to
              (MM0SourceStateV1 (MM0TextualEnvironmentV1 ?sorts ?decls) ?notation))
            ?base ?edges ?edge) ?after ?check ?result)))
    (rule mm0-coercion-provable-accepted-v1
      (head (MM0CoercionAfterProvableV1
        (MM0CoercionPendingV1 ?request ?base ?before
          (MM0CoercionEntryV1 ?term ?from ?to ?position)) ?after MM0CoercionGraphAcceptedV1
        (MM0CheckAcceptedV1 (MM0CoercionInstalledV1
          (MM0NotationWithCoercionsV1 ?base ?after)
          (MM0DeclaredCoercionV1 ?position ?term ?from ?to))))) (body))
    (rule mm0-coercion-provable-refused-v1
      (head (MM0CoercionAfterProvableV1
        (MM0CoercionPendingV1 ?request ?base ?before
          (MM0CoercionEntryV1 ?term ?from ?to ?position)) ?after
        (MM0CoercionAmbiguousV1 ?source ?first ?second)
        (MM0CheckRefusedV1 (MM0RefusedCoercionProvableV1 ?position ?source ?first ?second)))) (body))

    (rule mm0-coercion-append-nil-v1
      (head (MM0CoercionsAppendV1 MM0CoercionsNilV1 ?entry
        (MM0CoercionsConsV1 ?entry MM0CoercionsNilV1))) (body))
    (rule mm0-coercion-append-cons-v1
      (head (MM0CoercionsAppendV1 (MM0CoercionsConsV1 ?head ?rest) ?entry
        (MM0CoercionsConsV1 ?head ?after)))
      (body (MM0CoercionsAppendV1 ?rest ?entry ?after)))
    (rule mm0-coercion-reach-v1
      (head (MM0CoercionReachV1 ?edges ?direction ?from ?to ?result))
      (body (MM0CoercionWalkV1 ?edges ?direction (cons ?from nil) nil ?to ?result)))
    (rule mm0-coercion-walk-empty-v1
      (head (MM0CoercionWalkV1 ?edges ?direction nil ?seen ?to MM0CoercionSeparateV1)) (body))
    (rule mm0-coercion-walk-found-v1
      (head (MM0CoercionWalkV1 ?edges ?direction (cons ?to ?rest) ?seen ?to MM0CoercionConnectedV1)) (body))
    (rule mm0-coercion-walk-other-v1
      (head (MM0CoercionWalkV1 ?edges ?direction (cons ?current ?rest) ?seen ?to ?result))
      (body (different ?current ?to) (MM0NameLookupV1 ?current ?seen ?lookup)
        (MM0CoercionWalkAfterSeenV1 ?edges ?direction ?current ?rest ?seen ?to
          ?lookup ?result)))
    (rule mm0-coercion-walk-seen-v1
      (head (MM0CoercionWalkAfterSeenV1 ?edges ?direction ?current ?rest ?seen ?to
        MM0NameFoundV1 ?result))
      (body (MM0CoercionWalkV1 ?edges ?direction ?rest ?seen ?to ?result)))
    (rule mm0-coercion-walk-new-v1
      (head (MM0CoercionWalkAfterSeenV1 ?edges ?direction ?current ?rest ?seen ?to
        MM0NameMissingV1 ?result))
      (body (MM0CoercionNeighborsV1 ?edges ?direction ?current ?neighbors)
        (MM0ListAppendV1 ?neighbors ?rest ?pending)
        (MM0CoercionWalkV1 ?edges ?direction ?pending (cons ?current ?seen) ?to ?result)))
    (rule mm0-coercion-neighbors-empty-v1
      (head (MM0CoercionNeighborsV1 MM0CoercionsNilV1 ?direction ?current nil)) (body))
    (rule mm0-coercion-neighbors-forward-head-v1
      (head (MM0CoercionNeighborsV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?current ?to ?position) ?rest)
        MM0CoercionDirectedV1 ?current (cons ?to ?after)))
      (body (MM0CoercionNeighborsV1 ?rest MM0CoercionDirectedV1 ?current ?after)))
    (rule mm0-coercion-neighbors-forward-tail-v1
      (head (MM0CoercionNeighborsV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?from ?to ?position) ?rest)
        MM0CoercionDirectedV1 ?current ?after))
      (body (different ?current ?from)
        (MM0CoercionNeighborsV1 ?rest MM0CoercionDirectedV1 ?current ?after)))
    (rule mm0-coercion-neighbors-both-source-v1
      (head (MM0CoercionNeighborsV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?current ?to ?position) ?rest)
        MM0CoercionUndirectedV1 ?current (cons ?to ?after)))
      (body (MM0CoercionNeighborsV1 ?rest MM0CoercionUndirectedV1 ?current ?after)))
    (rule mm0-coercion-neighbors-both-target-v1
      (head (MM0CoercionNeighborsV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?from ?current ?position) ?rest)
        MM0CoercionUndirectedV1 ?current (cons ?from ?after)))
      (body (different ?from ?current)
        (MM0CoercionNeighborsV1 ?rest MM0CoercionUndirectedV1 ?current ?after)))
    (rule mm0-coercion-neighbors-both-tail-v1
      (head (MM0CoercionNeighborsV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?from ?to ?position) ?rest)
        MM0CoercionUndirectedV1 ?current ?after))
      (body (different ?current ?from) (different ?current ?to)
        (MM0CoercionNeighborsV1 ?rest MM0CoercionUndirectedV1 ?current ?after)))

    ; Paths retain real term constructors in source-to-target order. Visited
    ; sorts make the search finite even on a malformed externally supplied graph.
    (rule mm0-coercion-path-v1
      (head (MM0CoercionPathV1 ?edges ?from ?to ?result))
      (body (MM0CoercionPathVisitV1 ?edges ?from ?to nil ?result)))
    (rule mm0-coercion-path-identity-v1
      (head (MM0CoercionPathVisitV1 ?edges ?sort ?sort ?seen
        (MM0CoercionPathFoundV1 nil))) (body))
    (rule mm0-coercion-path-different-v1
      (head (MM0CoercionPathVisitV1 ?edges ?from ?to ?seen ?result))
      (body (different ?from ?to) (MM0NameLookupV1 ?from ?seen ?lookup)
        (MM0CoercionPathAfterSeenV1 ?edges ?from ?to ?seen ?lookup ?result)))
    (rule mm0-coercion-path-seen-v1
      (head (MM0CoercionPathAfterSeenV1 ?edges ?from ?to ?seen MM0NameFoundV1 MM0CoercionPathMissingV1)) (body))
    (rule mm0-coercion-path-new-v1
      (head (MM0CoercionPathAfterSeenV1 ?edges ?from ?to ?seen MM0NameMissingV1 ?result))
      (body (MM0CoercionPathEdgesV1 ?edges ?edges ?from ?to (cons ?from ?seen) ?result)))
    (rule mm0-coercion-path-edges-empty-v1
      (head (MM0CoercionPathEdgesV1 MM0CoercionsNilV1 ?all ?from ?to ?seen MM0CoercionPathMissingV1)) (body))
    (rule mm0-coercion-path-edges-skip-v1
      (head (MM0CoercionPathEdgesV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?other ?next ?position) ?rest)
        ?all ?from ?to ?seen ?result))
      (body (different ?other ?from)
        (MM0CoercionPathEdgesV1 ?rest ?all ?from ?to ?seen ?result)))
    (rule mm0-coercion-path-edges-branch-v1
      (head (MM0CoercionPathEdgesV1
        (MM0CoercionsConsV1 (MM0CoercionEntryV1 ?term ?from ?next ?position) ?rest)
        ?all ?from ?to ?seen ?result))
      (body (MM0CoercionPathVisitV1 ?all ?next ?to ?seen ?branch)
        (MM0CoercionPathAfterBranchV1 ?rest ?all ?from ?to ?seen ?term ?next ?branch ?result)))
    (rule mm0-coercion-path-branch-found-v1
      (head (MM0CoercionPathAfterBranchV1 ?rest ?all ?from ?to ?seen ?term ?next
        (MM0CoercionPathFoundV1 ?path)
        (MM0CoercionPathFoundV1 (cons (MM0CoercionHopV1 ?term ?next) ?path)))) (body))
    (rule mm0-coercion-path-branch-missing-v1
      (head (MM0CoercionPathAfterBranchV1 ?rest ?all ?from ?to ?seen ?term ?next
        MM0CoercionPathMissingV1 ?result))
      (body (MM0CoercionPathEdgesV1 ?rest ?all ?from ?to ?seen ?result)))

    ; A reachable provable target is unique across all directed paths, not
    ; merely per destination. Registration checks every existing source sort.
    (rule mm0-coercion-graph-check-v1
      (head (MM0CoercionGraphCheckV1 ?sorts ?edges ?result))
      (body (MM0CoercionGraphSourcesV1 ?sorts ?sorts ?edges ?result)))
    (rule mm0-coercion-graph-sources-empty-v1
      (head (MM0CoercionGraphSourcesV1 MM0SortEntriesNilV1 ?all ?edges MM0CoercionGraphAcceptedV1)) (body))
    (rule mm0-coercion-graph-sources-cons-v1
      (head (MM0CoercionGraphSourcesV1
        (MM0SortEntriesConsV1 (MM0SortEntryV1 ?source ?flags ?position) ?rest)
        ?all ?edges ?result))
      (body (MM0CoercionProvableTargetV1 ?edges ?source ?all ?target)
        (MM0CoercionGraphAfterTargetV1 ?rest ?all ?edges ?target ?result)))
    (rule mm0-coercion-graph-target-missing-v1
      (head (MM0CoercionGraphAfterTargetV1 ?rest ?all ?edges MM0CoercionProvableMissingV1 ?result))
      (body (MM0CoercionGraphSourcesV1 ?rest ?all ?edges ?result)))
    (rule mm0-coercion-graph-target-found-v1
      (head (MM0CoercionGraphAfterTargetV1 ?rest ?all ?edges (MM0CoercionProvableFoundV1 ?target) ?result))
      (body (MM0CoercionGraphSourcesV1 ?rest ?all ?edges ?result)))
    (rule mm0-coercion-graph-target-ambiguous-v1
      (head (MM0CoercionGraphAfterTargetV1 ?rest ?all ?edges
        (MM0CoercionAmbiguousV1 ?source ?first ?second)
        (MM0CoercionAmbiguousV1 ?source ?first ?second))) (body))
    (rule mm0-coercion-provable-target-v1
      (head (MM0CoercionProvableTargetV1 ?edges ?source ?sorts ?result))
      (body (MM0CoercionProvableScanV1 ?edges ?source ?sorts none ?result)))
    (rule mm0-coercion-provable-empty-missing-v1
      (head (MM0CoercionProvableScanV1 ?edges ?source MM0SortEntriesNilV1 none MM0CoercionProvableMissingV1)) (body))
    (rule mm0-coercion-provable-empty-found-v1
      (head (MM0CoercionProvableScanV1 ?edges ?source MM0SortEntriesNilV1 (some ?target)
        (MM0CoercionProvableFoundV1 ?target))) (body))
    (rule mm0-coercion-provable-skip-absent-v1
      (head (MM0CoercionProvableScanV1 ?edges ?source
        (MM0SortEntriesConsV1
          (MM0SortEntryV1 ?target (MM0SortModifiersV1 ?pure ?strict MM0ModifierAbsentV1 ?free) ?position) ?rest)
        ?found ?result))
      (body (MM0CoercionProvableScanV1 ?edges ?source ?rest ?found ?result)))
    (rule mm0-coercion-provable-skip-identity-v1
      (head (MM0CoercionProvableScanV1 ?edges ?source
        (MM0SortEntriesConsV1
          (MM0SortEntryV1 ?source (MM0SortModifiersV1 ?pure ?strict MM0ModifierPresentV1 ?free) ?position) ?rest)
        ?found ?result))
      (body (MM0CoercionProvableScanV1 ?edges ?source ?rest ?found ?result)))
    (rule mm0-coercion-provable-candidate-v1
      (head (MM0CoercionProvableScanV1 ?edges ?source
        (MM0SortEntriesConsV1
          (MM0SortEntryV1 ?target (MM0SortModifiersV1 ?pure ?strict MM0ModifierPresentV1 ?free) ?position) ?rest)
        ?found ?result))
      (body (different ?source ?target)
        (MM0CoercionReachV1 ?edges MM0CoercionDirectedV1 ?source ?target ?reachable)
        (MM0CoercionProvableAfterReachV1 ?edges ?source ?target ?rest ?found ?reachable ?result)))
    (rule mm0-coercion-provable-unreachable-v1
      (head (MM0CoercionProvableAfterReachV1 ?edges ?source ?target ?rest ?found MM0CoercionSeparateV1 ?result))
      (body (MM0CoercionProvableScanV1 ?edges ?source ?rest ?found ?result)))
    (rule mm0-coercion-provable-first-v1
      (head (MM0CoercionProvableAfterReachV1 ?edges ?source ?target ?rest none MM0CoercionConnectedV1 ?result))
      (body (MM0CoercionProvableScanV1 ?edges ?source ?rest (some ?target) ?result)))
    (rule mm0-coercion-provable-second-v1
      (head (MM0CoercionProvableAfterReachV1 ?edges ?source ?target ?rest (some ?first)
        MM0CoercionConnectedV1 (MM0CoercionAmbiguousV1 ?source ?first ?target)))
      (body (different ?first ?target)))

    ; Notation updates preserve the separately checked coercion graph.
    (rule mm0-notation-coercion-proxy-v1
      (head (MM0NotationStepV1 ?position ?ast
        (MM0NotationWithCoercionsV1 ?base ?edges) ?decls ?result))
      (body (MM0NotationStepV1 ?position ?ast ?base ?decls ?step)
        (MM0NotationProxyAfterStepV1 ?edges ?step ?result)))
    (rule mm0-notation-coercion-proxy-accepted-v1
      (head (MM0NotationProxyAfterStepV1 ?edges (MM0NotationStepAcceptedV1 ?after ?history)
        (MM0NotationStepAcceptedV1 (MM0NotationWithCoercionsV1 ?after ?edges) ?history))) (body))
    (rule mm0-notation-coercion-proxy-refused-v1
      (head (MM0NotationProxyAfterStepV1 ?edges (MM0NotationStepRefusedV1 ?reason ?before ?history)
        (MM0NotationStepRefusedV1 ?reason (MM0NotationWithCoercionsV1 ?before ?edges) ?history))) (body))
    (rule mm0-source-statement-class-coercion-v1
      (head (MM0StatementClassV1 (node mm0-coercion-statement ?payload) MM0CoercionStatementV1)) (body))
    (rule mm0-source-step-coercion-v1
      (head (MM0SourceStepByClassV1 ?position ?ast ?state MM0CoercionStatementV1 ?result))
      (body (MM0CoercionValidateV1 ?position ?ast ?state ?check)
        (MM0CoercionStepAfterCheckV1 ?state ?check ?result)))
    (rule mm0-source-step-coercion-accepted-v1
      (head (MM0CoercionStepAfterCheckV1 (MM0SourceStateV1 ?textual ?before)
        (MM0CheckAcceptedV1 (MM0CoercionInstalledV1 ?after ?history))
        (MM0SourceStepAcceptedV1 (MM0SourceStateV1 ?textual ?after) ?history))) (body))
    (rule mm0-source-step-coercion-refused-v1
      (head (MM0CoercionStepAfterCheckV1 ?state (MM0CheckRefusedV1 ?reason)
        (MM0SourceStepRefusedV1 ?reason ?state ?reason))) (body))

    ; Compose the existing ordered sort/term fold with live syntax state.
    ; The source fold dispatches by an authored statement partition.  This
    ; keeps syntax ownership in the source presentation and makes the four
    ; runtime cases constructor-disjoint before either target is selected.
    (rule mm0-source-statement-class-sort-v1
      (head
        (MM0StatementClassV1
          (node mm0-sort-statement ?payload) MM0TextualStatementV1))
      (body))
    (rule mm0-source-statement-class-term-v1
      (head
        (MM0StatementClassV1
          (node mm0-term-statement ?payload) MM0TextualStatementV1))
      (body))
    (rule mm0-source-statement-class-delimiter-v1
      (head
        (MM0StatementClassV1
          (node mm0-delimiter-statement ?payload) MM0NotationStatementV1))
      (body))
    (rule mm0-source-statement-class-simple-notation-v1
      (head
        (MM0StatementClassV1
          (node mm0-simple-notation-statement ?payload)
          MM0NotationStatementV1))
      (body))
    (rule mm0-source-step-dispatch-v1
      (head
        (MM0SourceStepV1 ?position ?statement ?before ?result))
      (body
        (MM0StatementClassV1 ?statement ?class)
        (MM0SourceStepByClassV1
          ?position ?statement ?before ?class ?result)))
    (rule mm0-source-step-textual-accepted-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement
          (MM0SourceStateV1 ?textual ?notation)
          MM0TextualStatementV1
          (MM0SourceStepAcceptedV1
            (MM0SourceStateV1 ?afterTextual ?notation) ?historyEntry)))
      (body
        (MM0TextualStepV1
          ?position ?statement ?textual
          (MM0TextualStepAcceptedV1 ?afterTextual ?historyEntry))))
    (rule mm0-source-step-textual-refused-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement
          (MM0SourceStateV1 ?textual ?notation)
          MM0TextualStatementV1
          (MM0SourceStepRefusedV1
            ?reason (MM0SourceStateV1 ?textual ?notation) ?historyEntry)))
      (body
        (MM0TextualStepV1
          ?position ?statement ?textual
          (MM0TextualStepRefusedV1
            ?reason ?textual ?historyEntry))))
    (rule mm0-source-step-notation-accepted-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          MM0NotationStatementV1
          (MM0SourceStepAcceptedV1
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?afterNotation)
            ?historyEntry)))
      (body
        (MM0NotationStepV1
          ?position ?statement ?notation ?declarations
          (MM0NotationStepAcceptedV1 ?afterNotation ?historyEntry))))
    (rule mm0-source-step-notation-refused-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          MM0NotationStatementV1
          (MM0SourceStepRefusedV1
            ?reason
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?historyEntry)))
      (body
        (MM0NotationStepV1
          ?position ?statement ?notation ?declarations
          (MM0NotationStepRefusedV1 ?reason ?notation ?historyEntry))))

    (rule mm0-source-fold-nil-v1
      (head
        (MM0SourceFoldV1
          nil ?position ?state MM0AcceptedV1 ?state MM0SourceHistoryNilV1))
      (body))
    (rule mm0-source-fold-cons-v1
      (head
        (MM0SourceFoldV1
          (cons ?statement ?rest) ?position ?before
          ?outcome ?after ?history))
      (body
        (MM0SourceStepV1 ?position ?statement ?before ?stepResult)
        (MM0SourceFoldAfterStepV1
          ?rest (NatSuccV1 ?position) ?stepResult
          ?outcome ?after ?history)))
    (rule mm0-source-fold-after-accepted-v1
      (head
        (MM0SourceFoldAfterStepV1
          ?rest ?position
          (MM0SourceStepAcceptedV1 ?next ?historyEntry)
          ?outcome ?after
          (MM0SourceHistoryConsV1 ?historyEntry ?history)))
      (body
        (MM0SourceFoldV1
          ?rest ?position ?next ?outcome ?after ?history)))
    (rule mm0-source-fold-after-refused-v1
      (head
        (MM0SourceFoldAfterStepV1
          ?rest ?position
          (MM0SourceStepRefusedV1 ?reason ?state ?historyEntry)
          ?reason ?state
          (MM0SourceHistoryConsV1
            ?historyEntry MM0SourceHistoryNilV1)))
      (body))

    (rule mm0-source-environment-from-ast-v1
      (head
        (MM0SourceEnvironmentFromAstV1
          (node mm0-file ?statements) ?outcome ?state ?history))
      (body
        (MM0SourceFoldV1
          ?statements NatZeroV1
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1
              MM0SortEntriesNilV1 MM0DeclarationEntriesNilV1)
            (MM0NotationEnvironmentV1
              (MM0MathClassTableConsV1
                (MM0MathClassEntryV1 (cp 32) MM0MathWhitespaceV1)
                (MM0MathClassTableConsV1
                  (MM0MathClassEntryV1 (cp 10) MM0MathWhitespaceV1)
                  MM0MathClassTableNilV1))
              MM0ConstantEntriesNilV1
              MM0PrefixEntriesNilV1
              MM0InfixEntriesNilV1))
          ?outcome ?state ?history)))))
