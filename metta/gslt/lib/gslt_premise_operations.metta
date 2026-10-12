; Shared canonical-pattern operations for authored premise execution.
; Free-variable occurrences retain their order and multiplicity. Binder display
; names and collection rest metadata do not change syntactic freshness.
(: gslt:premise:free-vars (-> Atom %Undefined%))
(= (gslt:premise:free-vars $pattern)
   (case $pattern
     (((Var $index) LNil)
      ((FVar $name) (LCons $name LNil))
      ((PApp $head $children) (gslt:premise:free-vars-list $children))
      ((PLam $binder $body) (gslt:premise:free-vars $body))
      ((PMultiLam $arity $binders $body) (gslt:premise:free-vars $body))
      ((PSubst $body $replacement)
       (let* (($left (gslt:premise:free-vars $body))
              ($right (gslt:premise:free-vars $replacement)))
         (gslt:automata:append $left $right)))
      ((PCollection $kind $elements $rest) (gslt:premise:free-vars-list $elements)))))
(: gslt:premise:free-vars-list (-> Atom %Undefined%))
(= (gslt:premise:free-vars-list $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($left (gslt:premise:free-vars $pattern))
              ($right (gslt:premise:free-vars-list $rest)))
         (gslt:automata:append $left $right))))))
(: gslt:premise:fresh (-> Atom Atom %Undefined%))
(= (gslt:premise:fresh $name $pattern)
   (let $names (gslt:premise:free-vars $pattern)
     (if (gslt:automata:member $name $names) False True)))

; A captured FVar supplies the name; an absent capture retains the literal
; authored name. A non-name capture cannot satisfy a freshness premise.
(: gslt:premise:resolve-name (-> Atom Atom %Undefined%))
(= (gslt:premise:resolve-name $name $bindings)
   (case (gslt:automata:binding $name $bindings)
     ((None (Some $name))
      ((Some $value)
       (case $value
         (((FVar $resolved) (Some $resolved))
          ($non-name None)))))))
(: gslt:premise:freshness (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:freshness $name $term $bindings)
   (case (gslt:premise:resolve-name $name $bindings)
     ((None LNil)
      ((Some $atom)
       (let $subject (gslt:rule:instantiate $term $bindings)
         (if (gslt:premise:fresh $atom $subject)
           (LCons $bindings LNil) LNil))))))

; Lexical parameter operations retain opaque contextual capture values.
(: gslt:premise:scope-remove (-> Atom Atom %Undefined%))
(= (gslt:premise:scope-remove $parameter $assignment)
   (case $assignment
     ((LNil LNil)
      ((LCons (Binding $name $value) $rest)
       (let $tail (gslt:premise:scope-remove $parameter $rest)
         (if (== $name $parameter) $tail
           (let $entry (Binding $name $value) (LCons $entry $tail))))))))

(: gslt:premise:scope-bind (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:scope-bind $parameter $value $assignment)
   (let* (($rest (gslt:premise:scope-remove $parameter $assignment))
          ($entry (Binding $parameter $value)))
     (LCons $entry $rest)))

(: gslt:premise:scope-restore (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:scope-restore $parameter $initial $final)
   (case (gslt:automata:binding $parameter $initial)
     ((None (gslt:premise:scope-remove $parameter $final))
      ((Some $value) (gslt:premise:scope-bind $parameter $value $final)))))

(: gslt:premise:scope-local-value (-> Atom Atom %Undefined%))
(= (gslt:premise:scope-local-value $ambient $pattern)
   (ContextualValue LNil $ambient $pattern))

; An absent value, wrong context, or unresolved rest is refused as None.
(: gslt:premise:scope-collection (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:scope-collection $ambient $assignment $name)
   (case (gslt:automata:binding $name $assignment)
     ((None None)
      ((Some $value)
       (case (gslt:rule:scope-instantiate-value $value $ambient 0 LNil)
         ((None None)
          ((Some $pattern)
           (case $pattern
             (((PCollection $kind $elements RNone)
               (Some (FiniteCollection $kind $elements)))
              ($non-concrete None))))))))))

; Constructor-parameter guards use the authored type and representation.
(: gslt:premise:parameter-type (-> Atom %Undefined%))
(= (gslt:premise:parameter-type $parameter)
   (case $parameter
     (((TermSimple $name $type) (Some $type))
      ((TermAbstraction $binder $name $type)
       (case $type
         (((TArrow $domain $codomain) (Some (TArrow $domain $codomain)))
          ((TBase $sort) (Some (TArrow (TBase $sort) (TBase $sort))))
          ($bad None))))
      ((TermMultiAbstraction $binders $name $type)
       (case $type
         (((TArrow (TMultiBinder $domain) $codomain)
           (Some (TArrow (TMultiBinder $domain) $codomain)))
          ((TBase $sort) (Some (TArrow (TMultiBinder (TBase $sort)) (TBase $sort))))
          ($bad None))))
      ($bad None))))

(: gslt:premise:parameter-representation (-> Atom Atom %Undefined%))
(= (gslt:premise:parameter-representation $parameter $pattern)
   (case $parameter
     (((TermSimple $name $type) True)
      ((TermAbstraction $binder $name $type)
       (case $pattern
         (((PLam BNone $body) True)
          ($bad False))))
      ((TermMultiAbstraction $binders $name $type)
       (case $pattern
         (((PMultiLam $arity LNil $body) True)
          ($bad False))))
      ($bad False))))

; Declaration-derived whole-pattern typing uses the authored declaration view.
(: gslt:premise:type-has (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-has $declarations $free $bound $pattern $expected)
   (case $pattern
     (((Var $index)
       (let* (($actual (gslt:rule:row-at $index $bound))
              ($wanted (Some $expected))) (== $actual $wanted)))
      ((FVar $name)
       (let* (($actual (gslt:automata:binding $name $free))
              ($wanted (Some $expected))) (== $actual $wanted)))
      ((PApp $label $arguments)
       (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $declarations))
      ((PLam $binder $body)
       (case $expected
         (((TArrow $domain $codomain)
           (let $inner (LCons $domain $bound)
             (gslt:premise:type-has $declarations $free $inner $body $codomain)))
          ($bad False))))
      ((PMultiLam $arity $binders $body)
       (case $expected
         (((TArrow (TMultiBinder $domain) $codomain)
           (let $inner (gslt:premise:type-extend-count $domain $arity $bound)
             (gslt:premise:type-has $declarations $free $inner $body $codomain)))
          ($bad False))))
      ((PSubst $body $replacement) False)
      ((PCollection $kind $elements $rest)
       (case $rest
         ((RNone
           (case $expected
             (((TCollection $actual $element)
               (if (== $actual $kind)
                 (gslt:premise:type-elements $declarations $free $bound $elements $element) False))
              ($base
               (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $declarations)))))
          ($bad False))))
      ($bad False))))

(: gslt:premise:type-arguments (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-arguments $declarations $free $bound $arguments $parameters)
   (case ($arguments $parameters)
     (((LNil LNil) True)
      (((LCons $argument $arguments-rest) (LCons $parameter $parameters-rest))
       (case (gslt:premise:parameter-type $parameter)
         ((None False)
          ((Some $expected)
           (if (gslt:premise:parameter-representation $parameter $argument)
             (if (gslt:premise:type-has $declarations $free $bound $argument $expected)
               (gslt:premise:type-arguments $declarations $free $bound $arguments-rest $parameters-rest)
               False) False)))))
      ($bad False))))

(: gslt:premise:type-elements (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-elements $declarations $free $bound $elements $element)
   (case $elements
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:type-has $declarations $free $bound $pattern $element)
         (gslt:premise:type-elements $declarations $free $bound $rest $element) False)))))

(: gslt:premise:type-constructors (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $remaining)
   (case $remaining
     ((LNil False)
      ((LCons (GrammarTypingV1 $actual $category $parameters) $rest)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (case $parameters
               (((LCons (TermSimple $parameter (TCollection $kind $element)) LNil)
                 (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest))
                ($ordinary
                 (if (gslt:premise:type-arguments $declarations $free $bound $arguments $parameters)
                   True
                   (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest)))))
             (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest)))
         (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest))))))

(: gslt:premise:type-collection-declarations (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $remaining)
   (case $remaining
     ((LNil False)
      ((LCons (GrammarTypingV1 $label $category $parameters) $rest)
       (case ($parameters $expected)
         ((((LCons (TermSimple $parameter (TCollection $actual $element)) LNil) (TBase $sort))
           (if (== $category $sort)
             (if (== $actual $kind)
               (if (gslt:premise:type-elements $declarations $free $bound $elements $element) True
                 (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest))
               (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest))
             (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest)))
          ($ordinary
           (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest))))))))

(: gslt:premise:type-extend-count (-> Atom Number Atom %Undefined%))
(= (gslt:premise:type-extend-count $domain $count $bound)
   (if (== $count 0) $bound
     (let* (($previous (- $count 1))
            ($tail (gslt:premise:type-extend-count $domain $previous $bound)))
       (LCons $domain $tail))))

; Open-object admission keeps typing, binder metadata, object form and scope distinct.
(: gslt:premise:object-pattern (-> Atom %Undefined%))
(= (gslt:premise:object-pattern $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $label $arguments) (gslt:premise:object-patterns $arguments))
      ((PLam $binder $body) (gslt:premise:object-pattern $body))
      ((PMultiLam $arity $binders $body) (gslt:premise:object-pattern $body))
      ((PSubst $body $replacement) False)
      ((PCollection $kind $elements RNone) (gslt:premise:object-patterns $elements))
      ($bad False))))

(: gslt:premise:object-patterns (-> Atom %Undefined%))
(= (gslt:premise:object-patterns $patterns)
   (case $patterns
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:object-pattern $pattern)
         (gslt:premise:object-patterns $rest) False))
      ($bad False))))

(: gslt:premise:canonical-binders (-> Atom %Undefined%))
(= (gslt:premise:canonical-binders $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $label $arguments) (gslt:premise:canonical-binders-list $arguments))
      ((PLam BNone $body) (gslt:premise:canonical-binders $body))
      ((PMultiLam $arity LNil $body) (gslt:premise:canonical-binders $body))
      ((PSubst $body $replacement)
       (if (gslt:premise:canonical-binders $body)
         (gslt:premise:canonical-binders $replacement) False))
      ((PCollection $kind $elements $rest) (gslt:premise:canonical-binders-list $elements))
      ($bad False))))

(: gslt:premise:canonical-binders-list (-> Atom %Undefined%))
(= (gslt:premise:canonical-binders-list $patterns)
   (case $patterns
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:canonical-binders $pattern)
         (gslt:premise:canonical-binders-list $rest) False))
      ($bad False))))

(: gslt:premise:open-well-sorted (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:open-well-sorted $declarations $free $bound $expected $pattern)
   (if (gslt:premise:type-has $declarations $free $bound $pattern $expected)
     (if (gslt:premise:canonical-binders $pattern)
       (if (gslt:premise:object-pattern $pattern)
         (let $depth (gslt:automata:length $bound)
           (gslt:rule:scope-well-scoped $depth $pattern)) False) False) False))
