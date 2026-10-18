; Project the authored MM0 textual environment into the existing MM0 service.
; Names retain their raw GSLT representation. Source positions order entries;
; dense sort, term and assertion IDs belong to separate namespaces.
!(import! &self langdef)

(: mm0:text:raw-list-view (-> Atom %Undefined%))
(= (mm0:text:raw-list-view $value)
   (case $value
     ((nil MM0:TextNil)
      ($other
       (if (== (size-atom $other) 3)
         (if (== (index-atom $other 0) cons)
           (let* (($first (index-atom $other 1))
                  ($rest (index-atom $other 2)))
             (MM0:TextCons $first $rest))
           MM0:TextMalformed)
         MM0:TextMalformed)))))

(: mm0:text:index (-> Atom %Undefined%))
(= (mm0:text:index $value)
   (case $value
     ((NatZeroV1 (Some 0))
      ((NatSuccV1 $rest)
       (let $previous (mm0:text:index $rest)
         (case $previous (((Some $index) (Some (+ $index 1))) ($bad None)))))
      ($bad None))))

(: mm0:text:flag (-> Atom %Undefined%))
(= (mm0:text:flag $value)
   (case $value
     ((MM0ModifierAbsentV1 (Some False))
      (MM0ModifierPresentV1 (Some True))
      ($bad None))))

(: mm0:text:sort-info (-> Atom %Undefined%))
(= (mm0:text:sort-info $value)
   (case $value
     (((MM0SortModifiersV1 $pure $strict $provable $free)
       (let* (($p (mm0:text:flag $pure)) ($s (mm0:text:flag $strict))
              ($v (mm0:text:flag $provable)) ($f (mm0:text:flag $free)))
         (case ($p $s $v $f)
           ((((Some $pureFlag) (Some $strictFlag)
              (Some $provableFlag) (Some $freeFlag))
             (Some (MM0:L (MM0:Sort $pureFlag $strictFlag $provableFlag $freeFlag))))
            ($bad None)))))
      ($bad None))))

(: mm0:text:sort-index (-> Atom Atom Number %Undefined%))
(= (mm0:text:sort-index $entries $name $index)
   (case $entries
     ((MM0SortEntriesNilV1 None)
      ((MM0SortEntriesConsV1 (MM0SortEntryV1 $stored $flags $position) $rest)
       (if (== $stored $name) (Some $index)
         (mm0:text:sort-index $rest $name (+ $index 1))))
      ($bad None))))

(: mm0:text:visible-sort (-> Atom Atom Number %Undefined%))
(= (mm0:text:visible-sort $entries $name $limit)
   (let $found (mm0:text:sort-index $entries $name 0)
     (case $found
       (((Some $index) (if (< $index $limit) (Some $index) None))
        ($bad None)))))

(: mm0:text:term-index (-> Atom Atom Number %Undefined%))
(= (mm0:text:term-index $entries $name $index)
   (case $entries
     ((MM0DeclarationEntriesNilV1 None)
      ((MM0DeclarationEntriesConsV1
         (MM0TermEntryV1 $stored $signature $position $source) $rest)
       (if (== $stored $name) (Some $index)
         (mm0:text:term-index $rest $name (+ $index 1))))
      ((MM0DeclarationEntriesConsV1
         (MM0AssertionEntryV1 $kind $stored $signature $position $source) $rest)
       (mm0:text:term-index $rest $name $index))
      ($bad None))))

(: mm0:text:binder-index (-> Atom Atom Number %Undefined%))
(= (mm0:text:binder-index $binders $name $index)
   (let $view (mm0:text:raw-list-view $binders)
     (case $view
       ((MM0:TextNil None)
        ((MM0:TextCons (MM0BinderV1 $kind (MM0NamedBinderV1 $stored) $type) $rest)
         (if (== $stored $name) (Some (MM0:TextBinder $kind $index))
           (mm0:text:binder-index $rest $name (+ $index 1))))
        ((MM0:TextCons (MM0BinderV1 $kind MM0AnonymousBinderV1 $type) $rest)
         (mm0:text:binder-index $rest $name (+ $index 1)))
        ($bad None)))))

; Canonical dependency sets use increasing full-context positions.
(: mm0:text:insert-index (-> Number Atom %Undefined%))
(= (mm0:text:insert-index $index $indices)
   (let $view (mm0:list-view $indices)
     (case $view
       ((List:Nil (mm0:list-cons $index $indices))
        ((List:Cons $first $rest)
         (if (== $index $first) $indices
           (if (< $index $first) (mm0:list-cons $index $indices)
             (let $tail (mm0:text:insert-index $index $rest)
               (mm0:list-cons $first $tail)))))
        ($bad MM0:Malformed)))))

(: mm0:text:dependencies (-> Atom Atom Number %Undefined%))
(= (mm0:text:dependencies $names $binders $limit)
   (let $view (mm0:text:raw-list-view $names)
     (case $view
       ((MM0:TextNil (Some (MM0:L ())))
        ((MM0:TextCons $name $rest)
         (let $found (mm0:text:binder-index $binders $name 0)
           (case $found
             (((Some (MM0:TextBinder MM0BoundBinderKindV1 $index))
               (if (< $index $limit)
                 (let $tail (mm0:text:dependencies $rest $binders $limit)
                   (case $tail
                     (((Some $indices)
                       (let $result (mm0:text:insert-index $index $indices) (Some $result)))
                      ($bad None))))
                 None))
              ($bad None)))))
        ($bad None)))))

(: mm0:text:context (-> Atom Number Atom Atom Number %Undefined%))
(= (mm0:text:context $sorts $sortLimit $all $remaining $position)
   (let $view (mm0:text:raw-list-view $remaining)
     (case $view
       ((MM0:TextNil (Some (MM0:L ())))
        ((MM0:TextCons $binder $rest)
         (let* (($head (mm0:text:binder $sorts $sortLimit $all $binder $position))
                ($tail (mm0:text:context $sorts $sortLimit $all $rest (+ $position 1))))
           (case ($head $tail)
             ((((Some $first) (Some $after))
               (let $result (mm0:list-cons $first $after) (Some $result)))
              ($bad None)))))
        ($bad None)))))

(: mm0:text:binder (-> Atom Number Atom Atom Number %Undefined%))
(= (mm0:text:binder $sorts $sortLimit $all $binder $position)
   (case $binder
     (((MM0BinderV1 MM0BoundBinderKindV1 $name (MM0TypeV1 $sort nil))
       (let $found (mm0:text:visible-sort $sorts $sort $sortLimit)
         (case $found
           (((Some $index) (Some (MM0:L (MM0:Bound $index)))) ($bad None)))))
      ((MM0BinderV1 MM0RegularBinderKindV1 $name (MM0TypeV1 $sort $names))
       (let* (($found (mm0:text:visible-sort $sorts $sort $sortLimit))
              ($deps (mm0:text:dependencies $names $all $position)))
         (case ($found $deps)
           ((((Some $index) (Some $indices))
             (Some (MM0:L (MM0:Regular $index $indices))))
            ($bad None)))))
      ($bad None))))

(: mm0:text:term-signature (-> Atom Number Atom %Undefined%))
(= (mm0:text:term-signature $sorts $sortLimit $signature)
   (case $signature
     (((MM0TermSignatureV1 $binders (MM0TypeV1 $sort $names))
       (let* (($context (mm0:text:context $sorts $sortLimit $binders $binders 0))
              ($found (mm0:text:visible-sort $sorts $sort $sortLimit)))
         (case ($context $found)
           ((((Some (MM0:L $arguments)) (Some $index))
             (let $deps (mm0:text:dependencies $names $binders (size-atom $arguments))
               (case $deps
                 (((Some $indices)
                   (Some (MM0:L (MM0:TermDecl (MM0:L $arguments) $index $indices))))
                  ($bad None)))))
            ($bad None)))))
      ($bad None))))

(: mm0:text:expression (-> Atom Number Atom Atom %Undefined%))
(= (mm0:text:expression $declarations $termLimit $binders $expression)
   (case $expression
     (((MM0ExpressionVariableV1 $name $sort)
       (let $found (mm0:text:binder-index $binders $name 0)
         (case $found
           (((Some (MM0:TextBinder $kind $index)) (Some (MM0:Var $index)))
            ($bad None)))))
      ((MM0ExpressionTermApplicationV1 $name $arguments $sort)
       (let $found (mm0:text:term-index $declarations $name 0)
         (case $found
           (((Some $index)
             (if (< $index $termLimit)
               (let $head (MM0:Term $index)
                 (mm0:text:apply-arguments $declarations $termLimit $binders $arguments $head))
               None))
            ($bad None)))))
      ($bad None))))

(: mm0:text:apply-arguments (-> Atom Number Atom Atom Atom %Undefined%))
(= (mm0:text:apply-arguments $declarations $termLimit $binders $arguments $head)
   (case $arguments
     ((MM0ExpressionArgumentsNilV1 (Some $head))
      ((MM0ExpressionArgumentsConsV1 $first $rest)
       (let $argument (mm0:text:expression $declarations $termLimit $binders $first)
         (case $argument
           (((Some $value)
             (let $next (MM0:App $head $value)
               (mm0:text:apply-arguments $declarations $termLimit $binders $rest $next)))
            ($bad None)))))
      ($bad None))))

(: mm0:text:hypotheses (-> Atom Number Atom Atom %Undefined%))
(= (mm0:text:hypotheses $declarations $termLimit $binders $hypotheses)
   (let $view (mm0:text:raw-list-view $hypotheses)
     (case $view
       ((MM0:TextNil (Some (MM0:L ())))
        ((MM0:TextCons (MM0HypothesisV1 $name $expression) $rest)
         (let* (($head (mm0:text:expression $declarations $termLimit $binders $expression))
                ($tail (mm0:text:hypotheses $declarations $termLimit $binders $rest)))
           (case ($head $tail)
             ((((Some $first) (Some $after))
               (let $result (mm0:list-cons $first $after) (Some $result)))
              ($bad None)))))
        ($bad None)))))

(: mm0:text:assertion-signature (-> Atom Number Atom Number Atom %Undefined%))
(= (mm0:text:assertion-signature $sorts $sortLimit $declarations $termLimit $signature)
   (case $signature
     (((MM0AssertionSignatureV1 $binders $hypotheses $conclusion)
       (let* (($context (mm0:text:context $sorts $sortLimit $binders $binders 0))
              ($hyps (mm0:text:hypotheses $declarations $termLimit $binders $hypotheses))
              ($claim (mm0:text:expression $declarations $termLimit $binders $conclusion)))
         (case ($context $hyps $claim)
           ((((Some $arguments) (Some $premises) (Some $expression))
             (Some (MM0:L (MM0:Theorem $arguments $premises $expression))))
            ($bad None)))))
      ($bad None))))

(: mm0:text:declaration-position (-> Atom %Undefined%))
(= (mm0:text:declaration-position $entry)
   (case $entry
     (((MM0TermEntryV1 $name $signature $position $source) (mm0:text:index $position))
      ((MM0AssertionEntryV1 $kind $name $signature $position $source) (mm0:text:index $position))
      ($bad None))))

(: mm0:text:prepend (-> Atom Atom %Undefined%))
(= (mm0:text:prepend $entry $remaining)
   (case ($entry $remaining)
     ((((Some $first) (Some $rest))
       (let $result (mm0:list-cons $first $rest) (Some $result)))
      ($bad None))))

(: mm0:text:project-sort (-> Atom Number %Undefined%))
(= (mm0:text:project-sort $entry $index)
   (case $entry
     (((MM0SortEntryV1 $name $flags $position)
       (let $info (mm0:text:sort-info $flags)
         (case $info
           (((Some $value) (Some (MM0:L (MM0:SpecSort $index $value)))) ($bad None)))))
      ($bad None))))

(: mm0:text:project-declaration (-> Atom Atom Number Atom Number Number %Undefined%))
(= (mm0:text:project-declaration $entry $sorts $sortLimit $declarations $termIndex $assertionIndex)
   (case $entry
     (((MM0TermEntryV1 $name $signature $position $source)
       (let $declaration (mm0:text:term-signature $sorts $sortLimit $signature)
         (case $declaration
           (((Some $value)
             (mm0:text:term-entry $source $signature $sorts $sortLimit $declarations $termIndex $value))
            ($bad None)))))
      ((MM0AssertionEntryV1 MM0AxiomDeclarationV1 $name $signature $position $source)
       (let $declaration (mm0:text:assertion-signature $sorts $sortLimit $declarations $termIndex $signature)
         (case $declaration
           (((Some $value) (Some (MM0:L (MM0:SpecAxiom $assertionIndex $value)))) ($bad None)))))
      ((MM0AssertionEntryV1 MM0TheoremDeclarationV1 $name $signature $position $source)
       (let $declaration (mm0:text:assertion-signature $sorts $sortLimit $declarations $termIndex $signature)
         (case $declaration
           (((Some $value) (Some (MM0:L (MM0:SpecTheorem $assertionIndex $value)))) ($bad None)))))
      ($bad None))))

(: mm0:text:take-sort (-> Atom Atom Atom Atom Atom Number Number Number %Undefined%))
(= (mm0:text:take-sort $entry $rest $declarations $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex)
   (let* (($head (mm0:text:project-sort $entry $sortIndex))
          ($tail (mm0:text:project-entries $rest $declarations $allSorts $allDeclarations
                   (+ $sortIndex 1) $termIndex $assertionIndex)))
     (mm0:text:prepend $head $tail)))

(: mm0:text:take-declaration (-> Atom Atom Atom Atom Atom Number Number Number %Undefined%))
(= (mm0:text:take-declaration $entry $sorts $rest $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex)
   (let $head (mm0:text:project-declaration $entry $allSorts $sortIndex $allDeclarations $termIndex $assertionIndex)
     (let $tail
       (case $entry
         (((MM0TermEntryV1 $name $signature $position $source)
           (mm0:text:project-entries $sorts $rest $allSorts $allDeclarations
             $sortIndex (+ $termIndex 1) $assertionIndex))
          ((MM0AssertionEntryV1 $kind $name $signature $position $source)
           (mm0:text:project-entries $sorts $rest $allSorts $allDeclarations
             $sortIndex $termIndex (+ $assertionIndex 1)))
          ($bad None)))
       (mm0:text:prepend $head $tail))))

(: mm0:text:project-entries (-> Atom Atom Atom Atom Number Number Number %Undefined%))
(= (mm0:text:project-entries $sorts $declarations $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex)
   (case ($sorts $declarations)
     (((MM0SortEntriesNilV1 MM0DeclarationEntriesNilV1) (Some (MM0:L ())))
      (((MM0SortEntriesConsV1 $entry $rest) MM0DeclarationEntriesNilV1)
       (mm0:text:take-sort $entry $rest $declarations $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex))
      ((MM0SortEntriesNilV1 (MM0DeclarationEntriesConsV1 $entry $rest))
       (mm0:text:take-declaration $entry $sorts $rest $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex))
      (((MM0SortEntriesConsV1 (MM0SortEntryV1 $name $flags $position) $sortRest)
        (MM0DeclarationEntriesConsV1 $entry $declarationRest))
       (let* (($sortPosition (mm0:text:index $position))
              ($declarationPosition (mm0:text:declaration-position $entry)))
         (case ($sortPosition $declarationPosition)
           ((((Some $first) (Some $second))
             (if (< $first $second)
               (let $sortEntry (MM0SortEntryV1 $name $flags $position)
                 (mm0:text:take-sort $sortEntry $sortRest $declarations $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex))
               (if (< $second $first)
                 (mm0:text:take-declaration $entry $sorts $declarationRest $allSorts $allDeclarations $sortIndex $termIndex $assertionIndex)
                 None)))
            ($bad None)))))
      ($bad None))))

(: mm0:text:specification (-> Atom %Undefined%))
(= (mm0:text:specification $state)
   (case $state
     (((MM0SourceStateV1 (MM0TextualEnvironmentV1 $sorts $declarations) $notation)
       (mm0:text:project-entries $sorts $declarations $sorts $declarations 0 0 0))
      ($bad None))))

(: mm0:text:read-environment (-> Atom %Undefined%))
(= (mm0:text:read-environment $path)
   (let $grammar (langdef:load "langdef/mm0/langdef.metta")
     (let $parsed (langdef:parse-file $grammar $path)
       (case $parsed
         (((LangDef:ParseAccepted MM0TextualV1 $digest ($ast))
           (let $results (collapse (gslt:mode:MM0SourceEnvironmentFromAstV1:1000 $ast))
             (case $results
               ((((gslt:result:MM0SourceEnvironmentFromAstV1:1000 MM0AcceptedV1 $state $history))
                 (Some (MM0:TextualParsed $digest $ast $state $history)))
                ($bad None)))))
          ($bad None))))))

(: mm0:text:read-specification (-> Atom %Undefined%))
(= (mm0:text:read-specification $path)
   (let $parsed (mm0:text:read-environment $path)
     (case $parsed
       (((Some (MM0:TextualParsed $digest $ast $state $history))
         (mm0:text:specification $state))
        ($bad None)))))

(: mm0:text:start-file (-> Atom %Undefined%))
(= (mm0:text:start-file $path)
   (let $specification (mm0:text:read-specification $path)
     (case $specification
       (((Some $pending) (mm0:start $pending))
        ($bad MM0:FrontendRefused)))))

; Definition bodies use the full public-plus-dummy context, while their
; signatures retain only public binders. Definitions share the term namespace.
(: mm0:text:raw-append (-> Atom Atom %Undefined%))
(= (mm0:text:raw-append $first $second)
   (let $view (mm0:text:raw-list-view $first)
     (case $view
       ((MM0:TextNil (Some $second))
        ((MM0:TextCons $head $tail)
         (let $after (mm0:text:raw-append $tail $second)
           (case $after
             (((Some $rest) (Some (quote (cons $head $rest)))) ($bad None)))))
        ($bad None)))))

(: mm0:text:dummy-sorts (-> Atom Number Atom %Undefined%))
(= (mm0:text:dummy-sorts $sorts $sortLimit $binders)
   (let $view (mm0:text:raw-list-view $binders)
     (case $view
       ((MM0:TextNil (Some (MM0:L ())))
        ((MM0:TextCons
           (MM0BinderV1 MM0BoundBinderKindV1 (MM0NamedBinderV1 $name)
             (MM0TypeV1 $sort nil)) $rest)
         (let* (($found (mm0:text:visible-sort $sorts $sort $sortLimit))
                ($remaining (mm0:text:dummy-sorts $sorts $sortLimit $rest)))
           (case ($found $remaining)
             ((((Some $index) (Some $tail))
               (let $result (mm0:list-cons $index $tail) (Some $result)))
              ($bad None)))))
        ($bad None)))))

; A definition enters the session in canonical form: its dummies are exactly
; those its definiens uses, in declared order. An unused dummy changes nothing
; about the definition, and the reference verifier ignores it, so a proof file
; may omit it. The proof-file frontends bring their definitions to this form.
(: mm0:text:dummy-occurrences (-> Atom Number Number Atom %Undefined%))
(= (mm0:text:dummy-occurrences $expression $arity $count (MM0:L $seen))
   (case $expression
     (((MM0:Var $index)
       (if (and (<= $arity $index) (< $index (+ $arity $count)))
         (let $dummy (- $index $arity)
           (if (is-member $dummy $seen) (MM0:L $seen)
             (mm0:list-cons $dummy (MM0:L $seen))))
         (MM0:L $seen)))
      ((MM0:Term $index) (MM0:L $seen))
      ((MM0:App $function $argument)
       (let $after (mm0:text:dummy-occurrences $function $arity $count (MM0:L $seen))
         (mm0:text:dummy-occurrences $argument $arity $count $after)))
      ($bad MM0:Malformed))))
(: mm0:text:used-dummies (-> Number Atom Atom %Undefined%))
(= (mm0:text:used-dummies $index (MM0:L $seen) $kept)
   (if (< $index 0) $kept
     (let $next (if (is-member $index $seen) (mm0:list-cons $index $kept) $kept)
       (mm0:text:used-dummies (- $index 1) (MM0:L $seen) $next))))
(: mm0:text:used-position (-> Atom Number Number %Undefined%))
(= (mm0:text:used-position (MM0:L $kept) $dummy $position)
   (case $kept
     ((() None)
      ((cons $first $rest)
       (if (== $first $dummy) (Some $position)
         (mm0:text:used-position (MM0:L $rest) $dummy (+ $position 1))))
      ($bad None))))
(: mm0:text:used-sorts (-> Atom Atom %Undefined%))
(= (mm0:text:used-sorts (MM0:L $sorts) (MM0:L $kept))
   (case $kept
     ((() (MM0:L ()))
      ((cons $index $rest)
       (let* (($sort (index-atom $sorts $index))
              ($tail (mm0:text:used-sorts (MM0:L $sorts) (MM0:L $rest))))
         (mm0:list-cons $sort $tail))))))
(: mm0:text:renumber-dummies (-> Atom Number Atom %Undefined%))
(= (mm0:text:renumber-dummies $expression $arity $kept)
   (case $expression
     (((MM0:Var $index)
       (if (< $index $arity)
         (let $variable (mm0:make-var $index) (Some $variable))
         (case (mm0:text:used-position $kept (- $index $arity) 0)
           (((Some $position)
             (let $variable (mm0:make-var (+ $arity $position)) (Some $variable)))
            ($bad None)))))
      ((MM0:Term $index) (let $term (mm0:make-term $index) (Some $term)))
      ((MM0:App $function $argument)
       (let* (($head (mm0:text:renumber-dummies $function $arity $kept))
              ($child (mm0:text:renumber-dummies $argument $arity $kept)))
         (case ($head $child)
           ((((Some $headValue) (Some $childValue))
             (let $application (mm0:make-app $headValue $childValue) (Some $application)))
            ($bad None)))))
      ($bad None))))
; The result also lists the retained original dummy positions, in order.
(: mm0:text:canonical-definition (-> Number Atom %Undefined%))
(= (mm0:text:canonical-definition $arity (MM0:L (MM0:Definition (MM0:L $dummies) $expression)))
   (let* (($count (size-atom $dummies))
          ($seen (mm0:text:dummy-occurrences $expression $arity $count (MM0:L ())))
          ($kept (mm0:text:used-dummies (- $count 1) $seen (MM0:L ()))))
     (case (mm0:text:renumber-dummies $expression $arity $kept)
       (((Some $body)
         (let $sorts (mm0:text:used-sorts (MM0:L $dummies) $kept)
           (Some (MM0:TextCanonical (MM0:L (MM0:Definition $sorts $body)) $kept))))
        ($bad None)))))
(: mm0:text:raw-length (-> Atom Number %Undefined%))
(= (mm0:text:raw-length $value $count)
   (case (mm0:text:raw-list-view $value)
     ((MM0:TextNil (Some $count))
      ((MM0:TextCons $first $rest) (mm0:text:raw-length $rest (+ $count 1)))
      ($bad None))))

(: mm0:text:definition-body (-> Atom Number Atom Number Atom Atom Atom %Undefined%))
(= (mm0:text:definition-body $sorts $sortLimit $declarations $termLimit $public $dummies $optional)
   (case ($dummies $optional)
     (((nil none) (Some None))
      (($dummyBinders (some $body))
       (let* (($sortsFound (mm0:text:dummy-sorts $sorts $sortLimit $dummyBinders))
              ($full (mm0:text:raw-append $public $dummyBinders))
              ($arity (mm0:text:raw-length $public 0)))
         (case ($sortsFound $full $arity)
           ((((Some $dummySorts) (Some $context) (Some $publicCount))
             (let $expression (mm0:text:expression $declarations $termLimit $context $body)
               (case $expression
                 (((Some $value)
                   (case (mm0:text:canonical-definition $publicCount
                           (MM0:L (MM0:Definition $dummySorts $value)))
                     (((Some (MM0:TextCanonical $definition $kept))
                       (Some (Some $definition)))
                      ($bad None))))
                  ($bad None)))))
            ($bad None)))))
      ($bad None))))

(: mm0:text:term-entry (-> Atom Atom Atom Number Atom Number Atom %Undefined%))
(= (mm0:text:term-entry $source $signature $sorts $sortLimit $declarations $termIndex $declaration)
   (case ($source $signature)
     (((MM0RuntimeTextualSourceV1 $ordinary)
       (Some (MM0:L (MM0:SpecTerm $termIndex $declaration))))
      (((MM0DefinitionSourceV1 $dummies $body MM0RuntimeTextualSourceV1)
        (MM0TermSignatureV1 $public $return))
       (let $projected (mm0:text:definition-body $sorts $sortLimit $declarations $termIndex $public $dummies $body)
         (case $projected
           (((Some $optionalBody)
             (Some (MM0:L (MM0:SpecDefinition $termIndex $declaration $optionalBody))))
            ($bad None)))))
      ($bad None))))
