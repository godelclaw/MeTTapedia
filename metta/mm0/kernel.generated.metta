; MM0 logical core: supplied evidence is checked, never searched for.
; Read the proof operations first, then conversion and dependency checks.
; Some carries a checked result; None is a completed logical refusal.
; MM0:Malformed marks data outside an operation's declared representation.
; Lists are MM0:L values; constructor heads retain their own identities.
; Native containers, arithmetic and scoped caches are defined in data.metta.

; Supplied proofs: hypotheses, theorem application and conversion

(: mm0:proof (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof $table $definitions $theorems $context $hypotheses $witness)
  (case $witness
    (
      ((MM0:L (MM0:Hyp $index))
        (mm0:data-at $hypotheses $index))
      ((MM0:L (MM0:TheoremApp $index $arguments $children))
        (let $declaration (mm0:nat-table-get $theorems $index)
          (mm0:proof-declaration $declaration $table $definitions $theorems $context
            $hypotheses $arguments $children)))
      ((MM0:L (MM0:Conversion $conversion $child))
        (let $converted (mm0:conversion $table $definitions $context $conversion)
          (mm0:proof-converted $converted $table $definitions $theorems $context $hypotheses
            $child)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-proof (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:check-proof $table $definitions $theorems $context $hypotheses $proof $claim)
  (let $checked (mm0:proof $table $definitions $theorems $context $hypotheses $proof)
    (let $answer (Some $claim) (mm0:data-eq $checked $answer))))

(: mm0:proof-declaration (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof-declaration $valueInput $table $definitions $theorems $context $hypotheses $arguments $children)
  (case $valueInput
    (
      (None
        None)
      ((Some $declaration)
        (let $instance (mm0:instantiate-theorem $table $context $declaration $arguments)
          (mm0:proof-instance $instance $table $definitions $theorems $context $hypotheses
            $children)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-instance (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof-instance $valueInput $table $definitions $theorems $context $hypotheses $children)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Instance $premises $conclusion)
        (let $checkedChildren (mm0:proof-children $table $definitions $theorems $context $hypotheses $children)
          (mm0:proof-premises $checkedChildren $premises $conclusion)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-premises (-> Atom Atom Atom %Undefined%))
(= (mm0:proof-premises $valueInput $premises $conclusion)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Expressions $actual)
        (let $equal (mm0:data-eq $actual $premises) (mm0:proof-matched $equal $conclusion)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-matched (-> Atom Atom %Undefined%))
(= (mm0:proof-matched $conditionInput $conclusion)
  (case $conditionInput
    (
      (False
        None)
      (True
        (Some $conclusion))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-converted (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof-converted $valueInput $table $definitions $theorems $context $hypotheses $child)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Converted $left $right $sort)
        (let $checked (mm0:proof $table $definitions $theorems $context $hypotheses $child)
          (mm0:proof-left $checked $left $right)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-left (-> Atom Atom Atom %Undefined%))
(= (mm0:proof-left $valueInput $left $right)
  (case $valueInput
    (
      (None
        None)
      ((Some $conclusion)
        (let $equal (mm0:data-eq $conclusion $left)
          (mm0:proof-conversion-matched $equal $right)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-conversion-matched (-> Atom Atom %Undefined%))
(= (mm0:proof-conversion-matched $conditionInput $right)
  (case $conditionInput ((False None) (True (Some $right)) ($mm0Malformed MM0:Malformed))))

(: mm0:proof-children (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof-children $table $definitions $theorems $context $hypotheses $children)
  (let $view (mm0:list-view $children)
    (mm0:proof-children-view $view $table $definitions $theorems $context $hypotheses)))

(: mm0:proof-children-view (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof-children-view $valueInput $table $definitions $theorems $context $hypotheses)
  (case $valueInput
    (
      (List:Nil
        (let $items (MM0:L ()) (MM0:Expressions $items)))
      ((List:Cons $child $children)
        (let $checked (mm0:proof $table $definitions $theorems $context $hypotheses $child)
          (mm0:proof-child $checked $table $definitions $theorems $context $hypotheses
            $children)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-child (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:proof-child $valueInput $table $definitions $theorems $context $hypotheses $children)
  (case $valueInput
    (
      (None
        None)
      ((Some $first)
        (let $checkedChildren (mm0:proof-children $table $definitions $theorems $context $hypotheses $children)
          (mm0:proof-tail $checkedChildren $first)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:proof-tail (-> Atom Atom %Undefined%))
(= (mm0:proof-tail $valueInput $first)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Expressions $rest)
        (let $extended (mm0:list-cons $first $rest) (MM0:Expressions $extended)))
      ($mm0Malformed
        MM0:Malformed))))

; Conversion witnesses: reflexivity, symmetry, transitivity, congruence and unfolding

(: mm0:unfold (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:unfold $table $definitions $target $symbol $arguments $images)
  (let $declaration (mm0:declaration $table $symbol)
    (mm0:unfold-declaration $declaration $table $definitions $target $symbol $arguments
      $images)))

(: mm0:unfold-declaration (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:unfold-declaration $valueInput $table $definitions $target $symbol $arguments $images)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:TermDecl $formal $sort $dependencies)))
        (let $declaration (mm0:nat-table-get $definitions $symbol)
          (mm0:unfold-body $declaration $table $target $formal $arguments $images)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:unfold-body (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:unfold-body $valueInput $table $target $formal $arguments $images)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:Definition $dummies $expression)))
        (let $argumentsFit (mm0:check-arguments $table $target $arguments $formal)
          (mm0:unfold-arguments $argumentsFit $target $arguments $dummies $images $expression)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:unfold-arguments (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:unfold-arguments $conditionInput $target $arguments $dummies $images $expression)
  (case $conditionInput
    (
      (False
        None)
      (True
        (let $checkDummiesResult (mm0:check-dummies $target $arguments $dummies $images)
          (mm0:unfold-dummies $checkDummiesResult $arguments $images $expression)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:unfold-dummies (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:unfold-dummies $conditionInput $arguments $images $expression)
  (case $conditionInput
    (
      (False
        None)
      (True
        (let $substitutionValuesResult (let $combined (let $variableImagesResult (mm0:variable-images $images)
              (mm0:list-append $arguments $variableImagesResult))
            (mm0:substitution-values $combined))
          (mm0:subst $expression $substitutionValuesResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion $table $definitions $context $witness)
  (case $witness
    (
      ((MM0:L (MM0:ConvRefl $expression))
        (let $inferred (mm0:infer $table $context $expression)
          (mm0:conversion-refl-type $inferred $expression)))
      ((MM0:L (MM0:ConvSymm $child))
        (let $converted (mm0:conversion $table $definitions $context $child)
          (mm0:conversion-swap $converted)))
      ((MM0:L (MM0:ConvTrans $first $second))
        (let $converted2 (mm0:conversion $table $definitions $context $first)
          (mm0:conversion-first $converted2 $table $definitions $context $second)))
      ((MM0:L (MM0:ConvCongruence $symbol $children))
        (let $declaration (mm0:declaration $table $symbol)
          (mm0:conversion-declaration $declaration $table $definitions $context $symbol
            $children)))
      ((MM0:L (MM0:ConvUnfold $symbol $arguments $images))
        (let $declaration2 (mm0:declaration $table $symbol)
          (mm0:conversion-unfold-declaration $declaration2 $table $definitions $context
            $symbol $arguments $images)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-refl-type (-> Atom Atom %Undefined%))
(= (mm0:conversion-refl-type $valueInput $expression)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Inferred $remaining $sort)
        (let $view (mm0:list-view $remaining)
          (mm0:conversion-refl-saturated $view $expression $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-refl-saturated (-> Atom Atom Atom %Undefined%))
(= (mm0:conversion-refl-saturated $valueInput $expression $sort)
  (case $valueInput
    (
      (List:Nil
        (MM0:Converted $expression $expression $sort))
      ((List:Cons $first $rest)
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-swap (-> Atom %Undefined%))
(= (mm0:conversion-swap $valueInput)
  (case ($valueInput)
    (
      ((None)
        None)
      (((MM0:Converted $left $right $sort))
        (MM0:Converted $right $left $sort))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-first (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-first $valueInput $table $definitions $context $second)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Converted $left $middle $sort)
        (let $converted (mm0:conversion $table $definitions $context $second)
          (mm0:conversion-join $left $middle $sort $converted)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-join (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-join $left $middle $sort $valueInput)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Converted $start $right $other-sort)
        (let $equal (let $items (MM0:L ($middle $sort))
            (let $items2 (MM0:L ($start $other-sort)) (mm0:data-eq $items $items2)))
          (mm0:conversion-joined $equal $left $right $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-joined (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-joined $conditionInput $left $right $sort)
  (case $conditionInput
    (
      (True
        (MM0:Converted $left $right $sort))
      (False
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-declaration (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-declaration $valueInput $table $definitions $context $symbol $children)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:TermDecl $formal $sort $dependencies)))
        (let $conversionArgumentsResult (mm0:conversion-arguments $table $definitions $context $children $formal)
          (mm0:conversion-congruent $conversionArgumentsResult $symbol $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-congruent (-> Atom Atom Atom %Undefined%))
(= (mm0:conversion-congruent $valueInput $symbol $sort)
  (case $valueInput
    (
      (None
        None)
      ((MM0:ConvertedArgs $left $right)
        (let $applyArgsResult (let $term (MM0:Term $symbol) (mm0:apply-args $term $left))
          (let $applyArgsResult2 (let $term2 (MM0:Term $symbol) (mm0:apply-args $term2 $right))
            (MM0:Converted $applyArgsResult $applyArgsResult2 $sort))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-unfold-declaration (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-unfold-declaration $valueInput $table $definitions $context $symbol $arguments $images)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:TermDecl $formal $sort $dependencies)))
        (let $unfoldResult (mm0:unfold $table $definitions $context $symbol $arguments $images)
          (mm0:conversion-unfold-result $unfoldResult $table $context $symbol $arguments
            $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-unfold-result (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-unfold-result $valueInput $table $context $symbol $arguments $sort)
  (case $valueInput
    (
      (None
        None)
      ((Some $result)
        (let $equal (let $inferred (mm0:infer $table $context $result)
            (let $inferred2 (let $items (MM0:L ()) (MM0:Inferred $items $sort))
              (mm0:data-eq $inferred $inferred2)))
          (mm0:conversion-unfold-typed $equal $symbol $arguments $result $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-unfold-typed (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-unfold-typed $conditionInput $symbol $arguments $result $sort)
  (case $conditionInput
    (
      (True
        (let $applyArgsResult (let $term (MM0:Term $symbol) (mm0:apply-args $term $arguments))
          (MM0:Converted $applyArgsResult $result $sort)))
      (False
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-arguments (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-arguments $table $definitions $context $children $formal)
  (let $view (mm0:list-view $children)
    (let $view2 (mm0:list-view $formal)
      (mm0:conversion-arguments-view $view $view2 $table $definitions $context))))

(: mm0:conversion-arguments-view (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-arguments-view $valueInput $valueInputValue $table $definitions $context)
  (case ($valueInput $valueInputValue)
    (
      ((List:Nil List:Nil)
        (let $items (MM0:L ()) (let $items2 (MM0:L ()) (MM0:ConvertedArgs $items $items2))))
      ((List:Nil (List:Cons $binder $binders))
        None)
      (((List:Cons $child $children) List:Nil)
        None)
      (((List:Cons $child $children) (List:Cons $binder $binders))
        (let $converted (mm0:conversion $table $definitions $context $child)
          (mm0:conversion-argument $converted $table $definitions $context $children $binder
            $binders)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-argument (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-argument $valueInput $table $definitions $context $children $binder $binders)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Converted $left $right $sort)
        (let $equal (let $conversionBinderSortResult (mm0:conversion-binder-sort $binder)
            (mm0:data-eq $sort $conversionBinderSortResult))
          (let $binderFits (mm0:check-binder $table $context $left $binder)
            (let $binderFits2 (mm0:check-binder $table $context $right $binder)
              (mm0:conversion-argument-checked $equal $binderFits $binderFits2 $table
                $definitions $context $children $binders $left $right)))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-binder-sort (-> Atom %Undefined%))
(= (mm0:conversion-binder-sort $valueInput)
  (case ($valueInput)
    (
      (((MM0:L (MM0:Bound $sort)))
        $sort)
      (((MM0:L (MM0:Regular $sort $dependencies)))
        $sort)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-argument-checked (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:conversion-argument-checked $sort-okInput $left-okInput $right-okInput $table $definitions $context $children $binders $left $right)
  (case ($sort-okInput $left-okInput $right-okInput)
    (
      ((True True True)
        (let $conversionArgumentsResult (mm0:conversion-arguments $table $definitions $context $children $binders)
          (mm0:conversion-argument-tail $conversionArgumentsResult $left $right)))
      (($sort-ok $left-ok $right-ok)
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:conversion-argument-tail (-> Atom Atom Atom %Undefined%))
(= (mm0:conversion-argument-tail $valueInput $left $right)
  (case $valueInput
    (
      (None
        None)
      ((MM0:ConvertedArgs $lefts $rights)
        (let $extended (mm0:list-cons $left $lefts)
          (let $extended2 (mm0:list-cons $right $rights)
            (MM0:ConvertedArgs $extended $extended2))))
      ($mm0Malformed
        MM0:Malformed))))

; Substitution and bound-variable dependency checks

(: mm0:check-pair (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:check-pair $target $formal-bound $target-bound $binder $position $expression)
  (let $dependsResult (mm0:depends $binder $position $formal-bound)
    (mm0:pair-depends $dependsResult $target $target-bound $expression)))

(: mm0:pair-depends (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:pair-depends $conditionInput $target $target-bound $expression)
  (case $conditionInput
    (
      (True
        True)
      (False
        (let $supportResult (mm0:support $target $expression)
          (mm0:support-disjoint $supportResult $target-bound)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-binder (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:check-binder $table $target $expression $valueInput)
  (case $valueInput
    (
      ((MM0:L (MM0:Bound $sort))
        (let $boundSortResult (mm0:bound-sort $target $expression)
          (mm0:check-sort $boundSortResult $sort)))
      ((MM0:L (MM0:Regular $sort $dependencies))
        (let $inferred (mm0:infer $table $target $expression)
          (mm0:check-type $inferred $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-sort (-> Atom Atom %Undefined%))
(= (mm0:check-sort $valueInput $expected)
  (case $valueInput
    (
      (None
        False)
      ((Some $actual)
        (mm0:nat-eq $actual $expected))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-type (-> Atom Atom %Undefined%))
(= (mm0:check-type $valueInput $expected)
  (case $valueInput
    (
      (None
        False)
      ((MM0:Inferred $remaining $actual)
        (let $view (mm0:list-view $remaining) (mm0:check-saturated $view $actual $expected)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-saturated (-> Atom Atom Atom %Undefined%))
(= (mm0:check-saturated $valueInput $actual $expected)
  (case $valueInput
    (
      (List:Nil
        (mm0:nat-eq $actual $expected))
      ((List:Cons $first $rest)
        False)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-arguments (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:check-arguments $table $target $expressions $formal)
  (let $view (mm0:list-view $expressions)
    (let $view2 (mm0:list-view $formal)
      (mm0:check-arguments-view $view $view2 $table $target))))

(: mm0:check-arguments-view (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:check-arguments-view $valueInput $valueInputValue $table $target)
  (case ($valueInput $valueInputValue)
    (
      ((List:Nil List:Nil)
        True)
      ((List:Nil (List:Cons $binder $formal))
        False)
      (((List:Cons $expression $expressions) List:Nil)
        False)
      (((List:Cons $expression $expressions) (List:Cons $binder $formal))
        (let $binderFits (mm0:check-binder $table $target $expression $binder)
          (mm0:check-arguments-next $binderFits $table $target $expressions $formal)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-arguments-next (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:check-arguments-next $conditionInput $table $target $expressions $formal)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:check-arguments $table $target $expressions $formal))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:entries (-> Atom Atom Atom %Undefined%))
(= (mm0:entries $formal $expressions $index)
  (let $view (mm0:list-view $formal)
    (let $view2 (mm0:list-view $expressions) (mm0:entries-view $view $view2 $index))))

(: mm0:entries-view (-> Atom Atom Atom %Undefined%))
(= (mm0:entries-view $valueInput $expressionsInput $index)
  (case ($valueInput $expressionsInput)
    (
      ((List:Nil $expressions)
        (MM0:L ()))
      (((List:Cons $binder $formal) List:Nil)
        (MM0:L ()))
      (((List:Cons $binder $formal) (List:Cons $expression $expressions))
        (let $entry (MM0:Entry $binder $expression $index)
          (let $entriesResult (let $natAddResult (mm0:nat-add $index 1)
              (mm0:entries $formal $expressions $natAddResult))
            (mm0:list-cons $entry $entriesResult))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-pairs (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:check-pairs $target $formal-bound $target-bound $entries)
  (let $view (mm0:list-view $entries)
    (mm0:pairs-view $view $target $formal-bound $target-bound)))

(: mm0:pairs-view (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:pairs-view $valueInput $target $formal-bound $target-bound)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons (MM0:Entry $binder $expression $position) $rest)
        (let $checkPairResult (mm0:check-pair $target $formal-bound $target-bound $binder $position $expression)
          (mm0:pairs-next $checkPairResult $target $formal-bound $target-bound $rest)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:pairs-next (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:pairs-next $conditionInput $target $formal-bound $target-bound $rest)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:check-pairs $target $formal-bound $target-bound $rest))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-row (-> Atom Atom Atom %Undefined%))
(= (mm0:check-row $target $all $valueInput)
  (case $valueInput
    (
      ((MM0:Entry (MM0:L (MM0:Bound $sort)) (MM0:Var $image) $position)
        (mm0:check-pairs $target $position $image $all))
      ((MM0:Entry (MM0:L (MM0:Bound $sort)) (MM0:Term $symbol) $position)
        True)
      ((MM0:Entry (MM0:L (MM0:Bound $sort)) (MM0:App $function $argument) $position)
        True)
      ((MM0:Entry (MM0:L (MM0:Regular $sort $dependencies)) $expression $position)
        True)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-rows (-> Atom Atom Atom %Undefined%))
(= (mm0:check-rows $target $all $entries)
  (let $view (mm0:list-view $entries) (mm0:rows-view $view $target $all)))

(: mm0:rows-view (-> Atom Atom Atom %Undefined%))
(= (mm0:rows-view $valueInput $target $all)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons $entry $rest)
        (let $checkRowResult (mm0:check-row $target $all $entry)
          (mm0:rows-next $checkRowResult $target $all $rest)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:rows-next (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:rows-next $conditionInput $target $all $rest)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:check-rows $target $all $rest))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-admissible (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:check-admissible $table $formal $target $expressions)
  (let $argumentsFit (mm0:check-arguments $table $target $expressions $formal)
    (mm0:admissible-typed $argumentsFit $target $formal $expressions)))

(: mm0:admissible-typed (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:admissible-typed $conditionInput $target $formal $expressions)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $entriesResult (mm0:entries $formal $expressions 0)
          (mm0:admissible-entries $target $entriesResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:admissible-entries (-> Atom Atom %Undefined%))
(= (mm0:admissible-entries $target $entries)
  (mm0:check-rows $target $entries $entries))

(: mm0:subst (-> Atom Atom %Undefined%))
(= (mm0:subst $expression $values)
  (case $expression
    (
      ((MM0:Var $i)
        (mm0:lookup $values $i))
      ((MM0:Term $i)
        (let $term (MM0:Term $i) (Some $term)))
      ((MM0:App $f $x)
        (let $substituted (mm0:subst $f $values) (mm0:subst-function $substituted $x $values)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:subst-function (-> Atom Atom Atom %Undefined%))
(= (mm0:subst-function $valueInput $x $values)
  (case $valueInput
    (
      (None
        None)
      ((Some $f)
        (let $substituted (mm0:subst $x $values) (mm0:subst-argument $f $substituted)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:subst-argument (-> Atom Atom %Undefined%))
(= (mm0:subst-argument $f $valueInput)
  (case $valueInput
    (
      (None
        None)
      ((Some $x)
        (let $app (MM0:App $f $x) (Some $app)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:lookup (-> Atom Atom %Undefined%))
(= (mm0:lookup $valueInput $i)
  (case $valueInput
    (
      (LNil
        None)
      ((LCons $h $t)
        (let $isZero (mm0:nat-zero $i) (mm0:lookup-zero $isZero $h $t $i)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:lookup-zero (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:lookup-zero $conditionInput $h $t $i)
  (case $conditionInput
    (
      (True
        (Some $h))
      (False
        (let $previous (mm0:nat-pred $i) (mm0:lookup $t $previous)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:substitution-values (-> Atom %Undefined%))
(= (mm0:substitution-values $values)
  (let $view (mm0:list-view $values) (mm0:substitution-values-view $view)))

(: mm0:substitution-values-view (-> Atom %Undefined%))
(= (mm0:substitution-values-view $valueInput)
  (case ($valueInput)
    (
      ((List:Nil)
        LNil)
      (((List:Cons $first $rest))
        (let $substitutionValuesResult (mm0:substitution-values $rest)
          (LCons $first $substitutionValuesResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:fresh-for (-> Atom Atom Atom %Undefined%))
(= (mm0:fresh-for $target $image $expression)
  (let $items (let $items2 (MM0:L ()) (MM0:L (MM0:Regular 0 $items2)))
    (mm0:check-pair $target 0 $image $items 0 $expression)))

(: mm0:fresh-all (-> Atom Atom Atom %Undefined%))
(= (mm0:fresh-all $target $image $arguments)
  (let $view (mm0:list-view $arguments) (mm0:fresh-all-view $view $target $image)))

(: mm0:fresh-all-view (-> Atom Atom Atom %Undefined%))
(= (mm0:fresh-all-view $valueInput $target $image)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons $expression $arguments)
        (let $freshForResult (mm0:fresh-for $target $image $expression)
          (mm0:fresh-all-next $freshForResult $target $image $arguments)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:fresh-all-next (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:fresh-all-next $conditionInput $target $image $arguments)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:fresh-all $target $image $arguments))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:check-dummies (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:check-dummies $target $arguments $sorts $images)
  (let $view (mm0:list-view $sorts)
    (let $view2 (mm0:list-view $images) (mm0:dummies-view $view $view2 $target $arguments))))

(: mm0:dummies-view (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:dummies-view $valueInput $valueInputValue $target $arguments)
  (case ($valueInput $valueInputValue)
    (
      ((List:Nil List:Nil)
        True)
      (((List:Cons $sort $sorts) List:Nil)
        False)
      ((List:Nil (List:Cons $image $images))
        False)
      (((List:Cons $sort $sorts) (List:Cons $image $images))
        (let $binderFits (let $items (MM0:L ())
            (let $var (MM0:Var $image)
              (let $items2 (MM0:L (MM0:Bound $sort))
                (mm0:check-binder $items $target $var $items2))))
          (mm0:dummy-sort $binderFits $target $arguments $sorts $images $image)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:dummy-sort (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:dummy-sort $conditionInput $target $arguments $sorts $images $image)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $freshAllResult (mm0:fresh-all $target $image $arguments)
          (mm0:dummy-fresh $freshAllResult $target $arguments $sorts $images $image)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:dummy-fresh (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:dummy-fresh $conditionInput $target $arguments $sorts $images $image)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $combined (let $extended (let $var (MM0:Var $image) (let $items (MM0:L ()) (mm0:list-cons $var $items)))
            (mm0:list-append $arguments $extended))
          (mm0:check-dummies $target $combined $sorts $images)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:variable-images (-> Atom %Undefined%))
(= (mm0:variable-images $images)
  (let $view (mm0:list-view $images) (mm0:variable-images-view $view)))

(: mm0:variable-images-view (-> Atom %Undefined%))
(= (mm0:variable-images-view $valueInput)
  (case ($valueInput)
    (
      ((List:Nil)
        (MM0:L ()))
      (((List:Cons $first $rest))
        (let $var (MM0:Var $first)
          (let $variableImagesResult (mm0:variable-images $rest)
            (mm0:list-cons $var $variableImagesResult))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:subst-list (-> Atom Atom %Undefined%))
(= (mm0:subst-list $sources $values)
  (let $view (mm0:list-view $sources) (mm0:subst-list-view $view $values)))

(: mm0:subst-list-view (-> Atom Atom %Undefined%))
(= (mm0:subst-list-view $valueInput $values)
  (case $valueInput
    (
      (List:Nil
        (let $items (MM0:L ()) (MM0:Expressions $items)))
      ((List:Cons $first $rest)
        (let $substituted (mm0:subst $first $values)
          (mm0:subst-list-head $substituted $rest $values)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:subst-list-head (-> Atom Atom Atom %Undefined%))
(= (mm0:subst-list-head $valueInput $rest $values)
  (case $valueInput
    (
      (None
        None)
      ((Some $first)
        (let $substListResult (mm0:subst-list $rest $values)
          (mm0:subst-list-tail $substListResult $first)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:subst-list-tail (-> Atom Atom %Undefined%))
(= (mm0:subst-list-tail $valueInput $first)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Expressions $rest)
        (let $extended (mm0:list-cons $first $rest) (MM0:Expressions $extended)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:dummy-context (-> Atom %Undefined%))
(= (mm0:dummy-context $sorts)
  (let $view (mm0:list-view $sorts) (mm0:dummy-context-view $view)))

(: mm0:dummy-context-view (-> Atom %Undefined%))
(= (mm0:dummy-context-view $valueInput)
  (case ($valueInput)
    (
      ((List:Nil)
        (MM0:L ()))
      (((List:Cons $sort $rest))
        (let $items (MM0:L (MM0:Bound $sort))
          (let $dummyContextResult (mm0:dummy-context $rest)
            (mm0:list-cons $items $dummyContextResult))))
      ($mm0Malformed
        MM0:Malformed))))

; Formation and specification-authorized admission

(: mm0:theorem-admissible (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:theorem-admissible $conditionInput $hypotheses $conclusion $arguments)
  (case $conditionInput
    (
      (False
        None)
      (True
        (let $substitutionValuesResult (mm0:substitution-values $arguments)
          (mm0:theorem-prepared $hypotheses $conclusion $substitutionValuesResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:theorem-prepared (-> Atom Atom Atom %Undefined%))
(= (mm0:theorem-prepared $hypotheses $conclusion $values)
  (let $substListResult (mm0:subst-list $hypotheses $values)
    (mm0:theorem-hypotheses $substListResult $conclusion $values)))

(: mm0:theorem-hypotheses (-> Atom Atom Atom %Undefined%))
(= (mm0:theorem-hypotheses $valueInput $conclusion $values)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Expressions $hypotheses)
        (let $substituted (mm0:subst $conclusion $values)
          (mm0:theorem-conclusion $substituted $hypotheses)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:theorem-conclusion (-> Atom Atom %Undefined%))
(= (mm0:theorem-conclusion $valueInput $hypotheses)
  (case $valueInput
    (
      (None
        None)
      ((Some $conclusion)
        (MM0:Instance $hypotheses $conclusion))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-not (-> Atom %Undefined%))
(= (mm0:form-not $conditionInput)
  (case ($conditionInput) (((True) False) ((False) True) ($mm0Malformed MM0:Malformed))))

(: mm0:form-and (-> Atom Atom %Undefined%))
(= (mm0:form-and $conditionInput $right)
  (case $conditionInput ((True $right) (False False) ($mm0Malformed MM0:Malformed))))

(: mm0:form-bound-index (-> Atom Atom %Undefined%))
(= (mm0:form-bound-index $context $index)
  (let $entry (mm0:data-at $context $index) (mm0:form-bound-item $entry)))

(: mm0:form-bound-item (-> Atom %Undefined%))
(= (mm0:form-bound-item $valueInput)
  (case ($valueInput)
    (
      ((None)
        False)
      (((Some (MM0:L (MM0:Bound $sort))))
        True)
      (((Some (MM0:L (MM0:Regular $sort $deps))))
        False)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-bound-indices (-> Atom Atom %Undefined%))
(= (mm0:form-bound-indices $context $indices)
  (let $view (mm0:list-view $indices) (mm0:form-bound-view $view $context)))

(: mm0:form-bound-view (-> Atom Atom %Undefined%))
(= (mm0:form-bound-view $valueInput $context)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons $index $indices)
        (let $formBoundIndexResult (mm0:form-bound-index $context $index)
          (mm0:form-bound-next $formBoundIndexResult $context $indices)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-bound-next (-> Atom Atom Atom %Undefined%))
(= (mm0:form-bound-next $conditionInput $context $indices)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:form-bound-indices $context $indices))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-sort (-> Atom Atom Atom %Undefined%))
(= (mm0:form-sort $sorts $sort $use)
  (let $declaration (mm0:nat-table-get $sorts $sort) (mm0:form-sort-info $declaration $use)))

(: mm0:form-sort-info (-> Atom Atom %Undefined%))
(= (mm0:form-sort-info $valueInput $useInput)
  (case ($valueInput $useInput)
    (
      ((None $use)
        False)
      (((Some (MM0:L (MM0:Sort $pure $strict $provable $free))) Bound)
        (mm0:form-not $strict))
      (((Some (MM0:L (MM0:Sort $pure $strict $provable $free))) Regular)
        True)
      (((Some (MM0:L (MM0:Sort $pure $strict $provable $free))) Result)
        (mm0:form-not $pure))
      (((Some (MM0:L (MM0:Sort $pure $strict $provable $free))) Statement)
        $provable)
      (((Some (MM0:L (MM0:Sort $pure $strict $provable $free))) Dummy)
        (let $formNotResult (mm0:form-not $strict)
          (let $formNotResult2 (mm0:form-not $free)
            (mm0:form-and $formNotResult $formNotResult2))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-binder (-> Atom Atom Atom %Undefined%))
(= (mm0:form-binder $sorts $context $valueInput)
  (case $valueInput
    (
      ((MM0:L (MM0:Bound $sort))
        (mm0:form-sort $sorts $sort Bound))
      ((MM0:L (MM0:Regular $sort $deps))
        (let $formSortResult (mm0:form-sort $sorts $sort Regular)
          (mm0:form-binder-deps $formSortResult $context $deps)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-binder-deps (-> Atom Atom Atom %Undefined%))
(= (mm0:form-binder-deps $conditionInput $context $deps)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:form-bound-indices $context $deps))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-context-from (-> Atom Atom Atom %Undefined%))
(= (mm0:form-context-from $sorts $initial $remaining)
  (let $view (mm0:list-view $remaining) (mm0:form-context-view $view $sorts $initial)))

(: mm0:form-context-view (-> Atom Atom Atom %Undefined%))
(= (mm0:form-context-view $valueInput $sorts $initial)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons $binder $remaining)
        (let $formBinderResult (mm0:form-binder $sorts $initial $binder)
          (mm0:form-context-next $formBinderResult $sorts $initial $binder $remaining)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-context-next (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:form-context-next $conditionInput $sorts $initial $binder $remaining)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $combined (let $items (MM0:L ($binder)) (mm0:list-append $initial $items))
          (mm0:form-context-from $sorts $combined $remaining)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-context (-> Atom Atom %Undefined%))
(= (mm0:form-context $sorts $context)
  (let $items (MM0:L ()) (mm0:form-context-from $sorts $items $context)))

(: mm0:form-term (-> Atom Atom %Undefined%))
(= (mm0:form-term $sorts $valueInput)
  (case $valueInput
    (
      ((MM0:L (MM0:TermDecl $context $sort $deps))
        (let $formContextResult (mm0:form-context $sorts $context)
          (mm0:form-term-context $formContextResult $sorts $context $sort $deps)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-term-context (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:form-term-context $conditionInput $sorts $context $sort $deps)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $formSortResult (mm0:form-sort $sorts $sort Result)
          (mm0:form-term-result $formSortResult $context $deps)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-term-result (-> Atom Atom Atom %Undefined%))
(= (mm0:form-term-result $conditionInput $context $deps)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:form-bound-indices $context $deps))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-dummies (-> Atom Atom %Undefined%))
(= (mm0:form-dummies $sorts $dummies)
  (let $view (mm0:list-view $dummies) (mm0:form-dummies-view $view $sorts)))

(: mm0:form-dummies-view (-> Atom Atom %Undefined%))
(= (mm0:form-dummies-view $valueInput $sorts)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons $sort $rest)
        (let $formSortResult (mm0:form-sort $sorts $sort Dummy)
          (mm0:form-dummies-next $formSortResult $sorts $rest)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-dummies-next (-> Atom Atom Atom %Undefined%))
(= (mm0:form-dummies-next $conditionInput $sorts $rest)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:form-dummies $sorts $rest))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-statement (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:form-statement $sorts $table $context $expression)
  (let $inferred (mm0:infer $table $context $expression)
    (mm0:form-statement-type $inferred $sorts)))

(: mm0:form-statement-type (-> Atom Atom %Undefined%))
(= (mm0:form-statement-type $valueInput $sorts)
  (case $valueInput
    (
      (None
        False)
      ((MM0:Inferred $remaining $sort)
        (let $view (mm0:list-view $remaining)
          (mm0:form-statement-saturated $view $sorts $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-statement-saturated (-> Atom Atom Atom %Undefined%))
(= (mm0:form-statement-saturated $valueInput $sorts $sort)
  (case $valueInput
    (
      (List:Nil
        (mm0:form-sort $sorts $sort Statement))
      ((List:Cons $binder $remaining)
        False)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-statements (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:form-statements $sorts $table $context $expressions)
  (let $view (mm0:list-view $expressions)
    (mm0:form-statements-view $view $sorts $table $context)))

(: mm0:form-statements-view (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:form-statements-view $valueInput $sorts $table $context)
  (case $valueInput
    (
      (List:Nil
        True)
      ((List:Cons $expression $rest)
        (let $formStatementResult (mm0:form-statement $sorts $table $context $expression)
          (mm0:form-statements-next $formStatementResult $sorts $table $context $rest)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-statements-next (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:form-statements-next $conditionInput $sorts $table $context $rest)
  (case $conditionInput
    (
      (False
        False)
      (True
        (mm0:form-statements $sorts $table $context $rest))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-theorem (-> Atom Atom Atom %Undefined%))
(= (mm0:form-theorem $sorts $table $valueInput)
  (case $valueInput
    (
      ((MM0:L (MM0:Theorem $context $hypotheses $conclusion))
        (let $formContextResult (mm0:form-context $sorts $context)
          (mm0:form-theorem-context $formContextResult $sorts $table $context $hypotheses
            $conclusion)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-theorem-context (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:form-theorem-context $conditionInput $sorts $table $context $hypotheses $conclusion)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $formStatementsResult (mm0:form-statements $sorts $table $context $hypotheses)
          (let $formStatementResult (mm0:form-statement $sorts $table $context $conclusion)
            (mm0:form-and $formStatementsResult $formStatementResult))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:form-body (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:form-body $sorts $table $valueInput $valueInputValue)
  (case ($valueInput $valueInputValue)
    (
      (((MM0:L (MM0:TermDecl $context $sort $deps)) (MM0:L (MM0:Definition $dummies $expression)))
        (let $formDummiesResult (mm0:form-dummies $sorts $dummies)
          (mm0:body-dummies $formDummiesResult $table $context $sort $deps $dummies
            $expression)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:admission-fresh (-> Atom Atom %Undefined%))
(= (mm0:admission-fresh $table $index)
  (let $declaration (mm0:nat-table-get $table $index) (mm0:admission-missing $declaration)))

(: mm0:admission-missing (-> Atom %Undefined%))
(= (mm0:admission-missing $valueInput)
  (case ($valueInput) (((None) True) (((Some $entry)) False) ($mm0Malformed MM0:Malformed))))

(: mm0:admission-check (-> Atom Atom %Undefined%))
(= (mm0:admission-check $valueInput $valueInputValue)
  (case ($valueInput $valueInputValue)
    (
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitSort $index $info)))
        (mm0:admission-fresh $sorts $index))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitTerm $index $declaration)))
        (let $admissionFreshResult (mm0:admission-fresh $terms $index)
          (let $formTermResult (mm0:form-term $sorts $declaration)
            (mm0:form-and $admissionFreshResult $formTermResult))))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitDefinition $index $declaration $body)))
        (let $formAndResult (let $formAndResult2 (let $admissionFreshResult2 (mm0:admission-fresh $terms $index)
              (let $admissionFreshResult3 (mm0:admission-fresh $definitions $index)
                (mm0:form-and $admissionFreshResult2 $admissionFreshResult3)))
            (let $formTermResult2 (mm0:form-term $sorts $declaration)
              (mm0:form-and $formAndResult2 $formTermResult2)))
          (let $formBodyResult (mm0:form-body $sorts $terms $declaration $body)
            (mm0:form-and $formAndResult $formBodyResult))))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitAxiom $index $declaration)))
        (let $admissionFreshResult4 (mm0:admission-fresh $theorems $index)
          (let $formTheoremResult (mm0:form-theorem $sorts $terms $declaration)
            (mm0:form-and $admissionFreshResult4 $formTheoremResult))))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitTheorem $index $declaration $dummies $proof)))
        (let $formAndResult3 (let $formAndResult4 (let $admissionFreshResult5 (mm0:admission-fresh $theorems $index)
              (let $formTheoremResult2 (mm0:form-theorem $sorts $terms $declaration)
                (mm0:form-and $admissionFreshResult5 $formTheoremResult2)))
            (let $formDummiesResult (mm0:form-dummies $sorts $dummies)
              (mm0:form-and $formAndResult4 $formDummiesResult)))
          (let $admissionProofResult (mm0:admission-proof $terms $definitions $theorems $declaration $dummies $proof)
            (mm0:form-and $formAndResult3 $admissionProofResult))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:admission-proof (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:admission-proof $terms $definitions $theorems $valueInput $dummies $proof)
  (case $valueInput
    (
      ((MM0:L (MM0:Theorem $context $hypotheses $conclusion))
        (let $combined (let $dummyContextResult (mm0:dummy-context $dummies)
            (mm0:list-append $context $dummyContextResult))
          (mm0:check-proof $terms $definitions $theorems $combined $hypotheses $proof
            $conclusion)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:admission-step (-> Atom Atom %Undefined%))
(= (mm0:admission-step $theory $admission)
  (let $admissionCheckResult (mm0:admission-check $theory $admission)
    (mm0:admission-checked $admissionCheckResult $theory $admission)))

(: mm0:admission-checked (-> Atom Atom Atom %Undefined%))
(= (mm0:admission-checked $conditionInput $theory $admission)
  (case $conditionInput
    (
      (False
        None)
      (True
        (mm0:admission-publish $theory $admission))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:admission-publish (-> Atom Atom %Undefined%))
(= (mm0:admission-publish $valueInput $valueInputValue)
  (case ($valueInput $valueInputValue)
    (
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitSort $index $info)))
        (let $items (let $extended (let $items2 (MM0:L ($index $info)) (mm0:list-cons $items2 $sorts))
            (MM0:L (MM0:Theory $extended $terms $definitions $theorems)))
          (Some $items)))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitTerm $index $declaration)))
        (let $items3 (let $extended2 (let $items4 (MM0:L ($index $declaration)) (mm0:list-cons $items4 $terms))
            (MM0:L (MM0:Theory $sorts $extended2 $definitions $theorems)))
          (Some $items3)))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitDefinition $index $declaration $body)))
        (let $items5 (let $extended3 (let $items6 (MM0:L ($index $declaration)) (mm0:list-cons $items6 $terms))
            (let $extended4 (let $items7 (MM0:L ($index $body)) (mm0:list-cons $items7 $definitions))
              (MM0:L (MM0:Theory $sorts $extended3 $extended4 $theorems))))
          (Some $items5)))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitAxiom $index $declaration)))
        (let $items8 (let $extended5 (let $items9 (MM0:L ($index $declaration)) (mm0:list-cons $items9 $theorems))
            (MM0:L (MM0:Theory $sorts $terms $definitions $extended5)))
          (Some $items8)))
      (((MM0:L (MM0:Theory $sorts $terms $definitions $theorems)) (MM0:L (MM0:AdmitTheorem $index $declaration $dummies $proof)))
        (let $items10 (let $extended6 (let $items11 (MM0:L ($index $declaration)) (mm0:list-cons $items11 $theorems))
            (MM0:L (MM0:Theory $sorts $terms $definitions $extended6)))
          (Some $items10)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-match (-> Atom Atom %Undefined%))
(= (mm0:spec-match $entryInput $admissionInput)
  (case ($entryInput $admissionInput)
    (
      (((MM0:L (MM0:SpecSort $index $payload)) (MM0:L (MM0:AdmitSort $actual $stored)))
        (let $items (MM0:L ($index $payload))
          (let $items2 (MM0:L ($actual $stored)) (mm0:data-eq $items $items2))))
      (((MM0:L (MM0:SpecTerm $index $payload)) (MM0:L (MM0:AdmitTerm $actual $stored)))
        (let $items3 (MM0:L ($index $payload))
          (let $items4 (MM0:L ($actual $stored)) (mm0:data-eq $items3 $items4))))
      (((MM0:L (MM0:SpecDefinition $index $payload $expected)) (MM0:L (MM0:AdmitDefinition $actual $stored $body)))
        (let $equal (let $items5 (MM0:L ($index $payload))
            (let $items6 (MM0:L ($actual $stored)) (mm0:data-eq $items5 $items6)))
          (let $specBodyResult (mm0:spec-body $expected $body)
            (mm0:form-and $equal $specBodyResult))))
      (((MM0:L (MM0:SpecAxiom $index $payload)) (MM0:L (MM0:AdmitAxiom $actual $stored)))
        (let $items7 (MM0:L ($index $payload))
          (let $items8 (MM0:L ($actual $stored)) (mm0:data-eq $items7 $items8))))
      (((MM0:L (MM0:SpecTheorem $index $payload)) (MM0:L (MM0:AdmitTheorem $actual $stored $dummies $proof)))
        (let $items9 (MM0:L ($index $payload))
          (let $items10 (MM0:L ($actual $stored)) (mm0:data-eq $items9 $items10))))
      (($entry $admission)
        False)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-body (-> Atom Atom %Undefined%))
(= (mm0:spec-body $valueInput $body)
  (case $valueInput
    (
      (None
        True)
      ((Some $expected)
        (mm0:data-eq $expected $body))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-auxiliary (-> Atom %Undefined%))
(= (mm0:spec-auxiliary $admissionInput)
  (case ($admissionInput)
    (
      (((MM0:L (MM0:AdmitDefinition $index $payload $body)))
        True)
      (((MM0:L (MM0:AdmitTheorem $index $payload $dummies $proof)))
        True)
      (($admission)
        False)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-pending (-> Atom Atom Atom %Undefined%))
(= (mm0:spec-pending $conditionInput $pending $admission)
  (case $conditionInput
    (
      (True
        (let $specAuxiliaryResult (mm0:spec-auxiliary $admission)
          (mm0:spec-guard $specAuxiliaryResult $pending)))
      (False
        (let $view (mm0:list-view $pending) (mm0:spec-public $view $admission)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-guard (-> Atom Atom %Undefined%))
(= (mm0:spec-guard $conditionInput $pending)
  (case $conditionInput ((False None) (True (Some $pending)) ($mm0Malformed MM0:Malformed))))

(: mm0:spec-public (-> Atom Atom %Undefined%))
(= (mm0:spec-public $valueInput $admission)
  (case $valueInput
    (
      (List:Nil
        None)
      ((List:Cons $entry $pending)
        (let $specMatchResult (mm0:spec-match $entry $admission)
          (mm0:spec-guard $specMatchResult $pending)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-step (-> Atom Atom %Undefined%))
(= (mm0:spec-step $valueInput $valueInputValue)
  (case ($valueInput $valueInputValue)
    (
      (((MM0:L (MM0:SpecificationState $theory $pending)) (MM0:L (MM0:ProofDeclaration $local $admission)))
        (let $specPendingResult (mm0:spec-pending $local $pending $admission)
          (mm0:spec-permitted $specPendingResult $theory $admission)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-permitted (-> Atom Atom Atom %Undefined%))
(= (mm0:spec-permitted $valueInput $theory $admission)
  (case $valueInput
    (
      (None
        None)
      ((Some $pending)
        (let $admissionStepResult (mm0:admission-step $theory $admission)
          (mm0:spec-admitted $admissionStepResult $pending)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-admitted (-> Atom Atom %Undefined%))
(= (mm0:spec-admitted $valueInput $pending)
  (case $valueInput
    (
      (None
        None)
      ((Some $theory)
        (let $items (MM0:L (MM0:SpecificationState $theory $pending)) (Some $items)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-finish (-> Atom %Undefined%))
(= (mm0:spec-finish $valueInput)
  (case ($valueInput)
    (
      ((None)
        None)
      (((Some (MM0:L (MM0:SpecificationState $theory $pending))))
        (let $view (mm0:list-view $pending) (mm0:spec-finished $view $theory)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:spec-finished (-> Atom Atom %Undefined%))
(= (mm0:spec-finished $valueInput $theory)
  (case $valueInput
    (
      (List:Nil
        (Some $theory))
      ((List:Cons $entry $rest)
        None)
      ($mm0Malformed
        MM0:Malformed))))

; Term typing, free variables and finite data

(: mm0:infer-uncached (-> Atom Atom Atom %Undefined%))
(= (mm0:infer-uncached $table $context $expression)
  (case $expression
    (
      ((MM0:Var $index)
        (let $entry (mm0:data-at $context $index) (mm0:infer-binder $entry)))
      ((MM0:Term $index)
        (let $declaration (mm0:declaration $table $index)
          (mm0:infer-declaration $declaration)))
      ((MM0:App $function $argument)
        (let $inferred (mm0:infer $table $context $function)
          (mm0:infer-function $inferred $table $context $argument)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-binder (-> Atom %Undefined%))
(= (mm0:infer-binder $valueInput)
  (case ($valueInput)
    (
      ((None)
        None)
      (((Some (MM0:L (MM0:Bound $sort))))
        (let $items (MM0:L ()) (MM0:Inferred $items $sort)))
      (((Some (MM0:L (MM0:Regular $sort $dependencies))))
        (let $items2 (MM0:L ()) (MM0:Inferred $items2 $sort)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-declaration (-> Atom %Undefined%))
(= (mm0:infer-declaration $valueInput)
  (case ($valueInput)
    (
      ((None)
        None)
      (((Some (MM0:L (MM0:TermDecl $arguments $sort $dependencies))))
        (MM0:Inferred $arguments $sort))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-function (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:infer-function $valueInput $table $context $argument)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Inferred $arguments $result)
        (let $view (mm0:list-view $arguments)
          (mm0:infer-arguments $view $result $table $context $argument)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-arguments (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:infer-arguments $valueInput $result $table $context $argument)
  (case $valueInput
    (
      (List:Nil
        None)
      ((List:Cons (MM0:L (MM0:Bound $sort)) $rest)
        (let $boundSortResult (mm0:bound-sort $context $argument)
          (mm0:infer-bound-sort $boundSortResult $sort $rest $result)))
      ((List:Cons (MM0:L (MM0:Regular $sort $dependencies)) $rest)
        (let $inferred (mm0:infer $table $context $argument)
          (mm0:infer-regular-type $inferred $sort $rest $result)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:bound-sort (-> Atom Atom %Undefined%))
(= (mm0:bound-sort $context $valueInput)
  (case $valueInput
    (
      ((MM0:Var $index)
        (let $entry (mm0:data-at $context $index) (mm0:bound-binder $entry)))
      ((MM0:Term $index)
        None)
      ((MM0:App $function $argument)
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:bound-binder (-> Atom %Undefined%))
(= (mm0:bound-binder $valueInput)
  (case ($valueInput)
    (
      ((None)
        None)
      (((Some (MM0:L (MM0:Bound $sort))))
        (Some $sort))
      (((Some (MM0:L (MM0:Regular $sort $dependencies))))
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-bound-sort (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:infer-bound-sort $valueInput $expected $rest $result)
  (case $valueInput
    (
      (None
        None)
      ((Some $sort)
        (let $equal (mm0:nat-eq $sort $expected) (mm0:infer-sort-equal $equal $rest $result)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-regular-type (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:infer-regular-type $valueInput $expected $rest $result)
  (case $valueInput
    (
      (None
        None)
      ((MM0:Inferred $remaining $sort)
        (let $view (mm0:list-view $remaining)
          (mm0:infer-saturated $view $sort $expected $rest $result)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-saturated (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:infer-saturated $valueInput $sort $expected $rest $result)
  (case $valueInput
    (
      (List:Nil
        (let $equal (mm0:nat-eq $sort $expected) (mm0:infer-sort-equal $equal $rest $result)))
      ((List:Cons $first $tail)
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:infer-sort-equal (-> Atom Atom Atom %Undefined%))
(= (mm0:infer-sort-equal $conditionInput $rest $result)
  (case $conditionInput
    (
      (True
        (MM0:Inferred $rest $result))
      (False
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:list-append (-> Atom Atom %Undefined%))
(= (mm0:list-append $left $right)
  (let $view (mm0:list-view $left) (mm0:append-view $view $right)))

(: mm0:append-view (-> Atom Atom %Undefined%))
(= (mm0:append-view $valueInput $right)
  (case $valueInput
    (
      (List:Nil
        $right)
      ((List:Cons $first $rest)
        (let $combined (mm0:list-append $rest $right) (mm0:list-cons $first $combined)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:support (-> Atom Atom %Undefined%))
(= (mm0:support $context $expression)
  (case $expression
    (
      ((MM0:Var $index)
        (let $entry (mm0:data-at $context $index) (mm0:support-binder $entry $index)))
      ((MM0:Term $index)
        (let $items (MM0:L ()) (Some $items)))
      ((MM0:App $function $argument)
        (let $supportResult (mm0:support $context $function)
          (mm0:support-function $supportResult $context $argument)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:support-binder (-> Atom Atom %Undefined%))
(= (mm0:support-binder $valueInput $index)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:Bound $sort)))
        (let $items (MM0:L ($index)) (Some $items)))
      ((Some (MM0:L (MM0:Regular $sort $dependencies)))
        (Some $dependencies))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:support-function (-> Atom Atom Atom %Undefined%))
(= (mm0:support-function $valueInput $context $argument)
  (case $valueInput
    (
      (None
        None)
      ((Some $left)
        (let $supportResult (mm0:support $context $argument)
          (mm0:support-argument $left $supportResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:support-argument (-> Atom Atom %Undefined%))
(= (mm0:support-argument $left $valueInput)
  (case $valueInput
    (
      (None
        None)
      ((Some $right)
        (let $combined (mm0:list-append $left $right) (Some $combined)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:nat-member (-> Atom Atom %Undefined%))
(= (mm0:nat-member $index $values)
  (let $view (mm0:list-view $values) (mm0:member-view $index $view)))

(: mm0:member-view (-> Atom Atom %Undefined%))
(= (mm0:member-view $index $valueInput)
  (case $valueInput
    (
      (List:Nil
        False)
      ((List:Cons $first $rest)
        (let $equal (mm0:nat-eq $index $first) (mm0:member-equal $equal $index $rest)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:member-equal (-> Atom Atom Atom %Undefined%))
(= (mm0:member-equal $conditionInput $index $rest)
  (case $conditionInput
    (
      (True
        True)
      (False
        (mm0:nat-member $index $rest))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:depends (-> Atom Atom Atom %Undefined%))
(= (mm0:depends $valueInput $position $index)
  (case $valueInput
    (
      ((MM0:L (MM0:Bound $sort))
        (mm0:nat-eq $index $position))
      ((MM0:L (MM0:Regular $sort $dependencies))
        (mm0:nat-member $index $dependencies))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:support-disjoint (-> Atom Atom %Undefined%))
(= (mm0:support-disjoint $valueInput $target-bound)
  (case $valueInput
    (
      (None
        False)
      ((Some $indices)
        (let $natMemberResult (mm0:nat-member $target-bound $indices)
          (mm0:dependency-not $natMemberResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:dependency-not (-> Atom %Undefined%))
(= (mm0:dependency-not $conditionInput)
  (case ($conditionInput) (((True) False) ((False) True) ($mm0Malformed MM0:Malformed))))

(: mm0:apply-args (-> Atom Atom %Undefined%))
(= (mm0:apply-args $function $arguments)
  (let $view (mm0:list-view $arguments) (mm0:apply-args-view $function $view)))

(: mm0:apply-args-view (-> Atom Atom %Undefined%))
(= (mm0:apply-args-view $function $valueInput)
  (case $valueInput
    (
      (List:Nil
        $function)
      ((List:Cons $argument $arguments)
        (let $app (MM0:App $function $argument) (mm0:apply-args $app $arguments)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:instantiate-theorem (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:instantiate-theorem $table $context $valueInput $arguments)
  (case $valueInput
    (
      ((MM0:L (MM0:Theorem $formal $hypotheses $conclusion))
        (let $admissible (mm0:check-admissible $table $formal $context $arguments)
          (mm0:theorem-admissible $admissible $hypotheses $conclusion $arguments)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:nat-difference (-> Atom Atom %Undefined%))
(= (mm0:nat-difference $source $removed)
  (let $view (mm0:list-view $source) (mm0:difference-view $view $removed)))

(: mm0:difference-view (-> Atom Atom %Undefined%))
(= (mm0:difference-view $valueInput $removed)
  (case $valueInput
    (
      (List:Nil
        (MM0:L ()))
      ((List:Cons $first $rest)
        (let $natMemberResult (mm0:nat-member $first $removed)
          (let $natDifferenceResult (mm0:nat-difference $rest $removed)
            (mm0:difference-keep $natMemberResult $first $natDifferenceResult))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:difference-keep (-> Atom Atom Atom %Undefined%))
(= (mm0:difference-keep $conditionInput $first $rest)
  (case $conditionInput
    (
      (True
        $rest)
      (False
        (mm0:list-cons $first $rest))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-image (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:free-image $target $formal $arguments $position)
  (let $entry (mm0:data-at $formal $position)
    (mm0:free-image-formal $entry $target $arguments $position)))

(: mm0:free-image-formal (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:free-image-formal $valueInput $target $arguments $position)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:Bound $sort)))
        (let $entry (mm0:data-at $arguments $position)
          (mm0:free-image-argument $entry $target $sort)))
      ((Some (MM0:L (MM0:Regular $sort $dependencies)))
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-image-argument (-> Atom Atom Atom %Undefined%))
(= (mm0:free-image-argument $valueInput $target $sort)
  (case $valueInput
    (
      ((Some (MM0:Var $image))
        (let $entry (mm0:data-at $target $image) (mm0:free-image-target $entry $sort $image)))
      (None
        None)
      ((Some (MM0:Term $symbol))
        None)
      ((Some (MM0:App $function $argument))
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-image-target (-> Atom Atom Atom %Undefined%))
(= (mm0:free-image-target $valueInput $expected $image)
  (case $valueInput
    (
      ((Some (MM0:L (MM0:Bound $actual)))
        (let $equal (mm0:nat-eq $actual $expected) (mm0:free-image-equal $equal $image)))
      ((Some (MM0:L (MM0:Regular $sort $dependencies)))
        None)
      (None
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-image-equal (-> Atom Atom %Undefined%))
(= (mm0:free-image-equal $conditionInput $image)
  (case $conditionInput ((True (Some $image)) (False None) ($mm0Malformed MM0:Malformed))))

(: mm0:free-images (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:free-images $target $formal $arguments $positions)
  (let $view (mm0:list-view $positions)
    (mm0:free-images-view $view $target $formal $arguments)))

(: mm0:free-images-view (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:free-images-view $valueInput $target $formal $arguments)
  (case $valueInput
    (
      (List:Nil
        (let $items (MM0:L ()) (Some $items)))
      ((List:Cons $position $positions)
        (let $freeImageResult (mm0:free-image $target $formal $arguments $position)
          (mm0:free-images-first $freeImageResult $target $formal $arguments $positions)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-images-first (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-images-first $valueInput $target $formal $arguments $positions)
  (case $valueInput
    (
      (None
        None)
      ((Some $image)
        (let $freeImagesResult (mm0:free-images $target $formal $arguments $positions)
          (mm0:free-images-tail $image $freeImagesResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-images-tail (-> Atom Atom %Undefined%))
(= (mm0:free-images-tail $image $valueInput)
  (case $valueInput
    (
      (None
        None)
      ((Some $images)
        (let $extended (mm0:list-cons $image $images) (Some $extended)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-contributions (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-contributions $target $full $arguments $formal $free-lists)
  (let $view (mm0:list-view $formal)
    (let $view2 (mm0:list-view $free-lists)
      (mm0:free-contributions-view $view $view2 $target $full $arguments))))

(: mm0:free-contributions-view (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-contributions-view $valueInput $valueInputValue $target $full $arguments)
  (case ($valueInput $valueInputValue)
    (
      ((List:Nil List:Nil)
        (let $items (MM0:L ()) (Some $items)))
      ((List:Nil (List:Cons $free $free-lists))
        None)
      (((List:Cons $binder $formal) List:Nil)
        None)
      (((List:Cons (MM0:L (MM0:Bound $sort)) $formal) (List:Cons $free $free-lists))
        (mm0:free-contributions $target $full $arguments $formal $free-lists))
      (((List:Cons (MM0:L (MM0:Regular $sort $dependencies)) $formal) (List:Cons $free $free-lists))
        (let $freeImagesResult (mm0:free-images $target $full $arguments $dependencies)
          (mm0:free-contribution-bound $freeImagesResult $target $full $arguments $formal
            $free $free-lists)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-contribution-bound (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-contribution-bound $valueInput $target $full $arguments $formal $free $free-lists)
  (case $valueInput
    (
      (None
        None)
      ((Some $bound)
        (let $natDifferenceResult (mm0:nat-difference $free $bound)
          (let $freeContributionsResult (mm0:free-contributions $target $full $arguments $formal $free-lists)
            (mm0:free-contribution-tail $natDifferenceResult $freeContributionsResult))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-contribution-tail (-> Atom Atom %Undefined%))
(= (mm0:free-contribution-tail $free $valueInput)
  (case $valueInput
    (
      (None
        None)
      ((Some $rest)
        (let $combined (mm0:list-append $free $rest) (Some $combined)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-spine (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-spine $table $context $valueInput $arguments $free-lists)
  (case $valueInput
    (
      ((MM0:Var $index)
        (let $view (mm0:list-view $arguments)
          (let $view2 (mm0:list-view $free-lists)
            (mm0:free-variable-spine $view $view2 $context $index))))
      ((MM0:Term $symbol)
        (let $declaration (mm0:declaration $table $symbol)
          (mm0:free-head $declaration $table $context $arguments $free-lists)))
      ((MM0:App $function $argument)
        (let $freeSpineResult (let $items (MM0:L ())
            (let $items2 (MM0:L ()) (mm0:free-spine $table $context $argument $items $items2)))
          (mm0:free-argument $freeSpineResult $table $context $function $argument $arguments
            $free-lists)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-variable-spine (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:free-variable-spine $valueInput $free-listsInput $context $index)
  (case ($valueInput $free-listsInput)
    (
      ((List:Nil List:Nil)
        (let $var (MM0:Var $index) (mm0:support $context $var)))
      ((List:Nil (List:Cons $free $rest))
        None)
      (((List:Cons $argument $rest) $free-lists)
        None)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-head (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-head $valueInput $table $context $arguments $free-lists)
  (case $valueInput
    (
      (None
        None)
      ((Some (MM0:L (MM0:TermDecl $formal $sort $dependencies)))
        (let $argumentsFit (mm0:check-arguments $table $context $arguments $formal)
          (mm0:free-typed $argumentsFit $context $formal $arguments $free-lists $dependencies)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-typed (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-typed $conditionInput $context $formal $arguments $free-lists $dependencies)
  (case $conditionInput
    (
      (False
        None)
      (True
        (let $freeContributionsResult (mm0:free-contributions $context $formal $arguments $formal $free-lists)
          (mm0:free-contributed $freeContributionsResult $context $formal $arguments
            $dependencies)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-contributed (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-contributed $valueInput $context $formal $arguments $dependencies)
  (case $valueInput
    (
      (None
        None)
      ((Some $free)
        (let $freeImagesResult (mm0:free-images $context $formal $arguments $dependencies)
          (mm0:free-contribution-tail $free $freeImagesResult)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-argument (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:free-argument $valueInput $table $context $function $argument $arguments $free-lists)
  (case $valueInput
    (
      (None
        None)
      ((Some $free)
        (let $extended (mm0:list-cons $argument $arguments)
          (let $extended2 (mm0:list-cons $free $free-lists)
            (mm0:free-spine $table $context $function $extended $extended2))))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:free-variables (-> Atom Atom Atom %Undefined%))
(= (mm0:free-variables $table $context $source)
  (let $items (MM0:L ())
    (let $items2 (MM0:L ()) (mm0:free-spine $table $context $source $items $items2))))

(: mm0:body-free (-> Atom Atom %Undefined%))
(= (mm0:body-free $valueInput $deps)
  (case $valueInput
    (
      (None
        False)
      ((Some $free)
        (let $view (let $natDifferenceResult (mm0:nat-difference $free $deps)
            (mm0:list-view $natDifferenceResult))
          (mm0:body-free-view $view)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:body-free-view (-> Atom %Undefined%))
(= (mm0:body-free-view $valueInput)
  (case ($valueInput)
    (
      ((List:Nil)
        True)
      (((List:Cons $first $rest))
        False)
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:body-dummies (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:body-dummies $conditionInput $table $context $sort $deps $dummies $expression)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $combined (let $dummyContextResult (mm0:dummy-context $dummies)
            (mm0:list-append $context $dummyContextResult))
          (mm0:body-context $table $combined $sort $deps $expression)))
      ($mm0Malformed
        MM0:Malformed))))

(: mm0:body-context (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:body-context $table $context $sort $deps $expression)
  (let $equal (let $inferred (mm0:infer $table $context $expression)
      (let $inferred2 (let $items (MM0:L ()) (MM0:Inferred $items $sort))
        (mm0:data-eq $inferred $inferred2)))
    (mm0:body-typed $equal $table $context $deps $expression)))

(: mm0:body-typed (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:body-typed $conditionInput $table $context $deps $expression)
  (case $conditionInput
    (
      (False
        False)
      (True
        (let $freeVariablesResult (mm0:free-variables $table $context $expression)
          (mm0:body-free $freeVariablesResult $deps)))
      ($mm0Malformed
        MM0:Malformed))))
