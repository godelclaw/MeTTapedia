; Schema checking retains collection rests and the declared finite substitution domains.
(: gslt:premise:schema-rest (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-rest $free $kind $element $rest)
  (case $rest
    ((RNone True)
     ((RSome $name)
       (let* (($actual (gslt:automata:binding $name $free))
              ($wanted (Some (TCollection $kind $element))))
         (== $actual $wanted))))))

(: gslt:premise:schema-extend (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-extend $domain $count $bound)
  (if (== $count 0) $bound
    (let* (($previous (- $count 1))
           ($tail (gslt:premise:schema-extend $domain $previous $bound)))
      (LCons $domain $tail))))

(: gslt:premise:schema-has (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-has $sorts $declarations $free $bound $pattern $expected)
  (case $pattern
    (((Var $index)
       (let* (($actual (gslt:rule:row-at $index $bound)) ($wanted (Some $expected)))
         (== $actual $wanted)))
     ((FVar $name)
       (let* (($actual (gslt:automata:binding $name $free)) ($wanted (Some $expected)))
         (== $actual $wanted)))
     ((PApp $label $arguments)
       (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $declarations))
     ((PLam $binder $body)
       (case $expected
         (((TArrow $domain $codomain)
           (let $inner (LCons $domain $bound)
             (gslt:premise:schema-has $sorts $declarations $free $inner $body $codomain)))
          ($bad False))))
     ((PMultiLam $arity $binders $body)
       (case $expected
         (((TArrow (TMultiBinder $domain) $codomain)
           (let $inner (gslt:premise:schema-extend $domain $arity $bound)
             (gslt:premise:schema-has $sorts $declarations $free $inner $body $codomain)))
          ($bad False))))
     ((PSubst $body $replacement)
       (gslt:premise:schema-substitutions $sorts $declarations $free $bound $body $replacement $expected $sorts))
     ((PCollection $kind $elements $rest)
       (case $expected
         (((TCollection $actual $element)
           (if (== $actual $kind)
             (if (gslt:premise:schema-elements $sorts $declarations $free $bound $elements $element)
               (gslt:premise:schema-rest $free $kind $element $rest) False) False))
          ($base
           (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $rest $expected $declarations))))))))

(: gslt:premise:schema-arguments (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-arguments $sorts $declarations $free $bound $arguments $parameters)
  (case (SchemaArguments $arguments $parameters)
    (((SchemaArguments LNil LNil) True)
     ((SchemaArguments (LCons $argument $arguments-rest) (LCons $parameter $parameters-rest))
       (case (gslt:premise:parameter-type $parameter)
         ((None False)
          ((Some $expected)
           (if (gslt:premise:parameter-representation $parameter $argument)
             (if (gslt:premise:schema-has $sorts $declarations $free $bound $argument $expected)
               (gslt:premise:schema-arguments $sorts $declarations $free $bound $arguments-rest $parameters-rest)
               False) False)))))
     ($bad False))))

(: gslt:premise:schema-elements (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-elements $sorts $declarations $free $bound $elements $element)
  (case $elements
    ((LNil True)
     ((LCons $pattern $rest)
       (if (gslt:premise:schema-has $sorts $declarations $free $bound $pattern $element)
         (gslt:premise:schema-elements $sorts $declarations $free $bound $rest $element) False)))))

(: gslt:premise:schema-constructors (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $remaining)
  (case $remaining
    ((LNil False)
     ((LCons (GrammarTypingV1 $actual $category $parameters) $rest)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (case $parameters
               (((LCons (TermSimple $parameter (TCollection $kind $element)) LNil)
                 (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest))
                ($ordinary
                 (if (gslt:premise:schema-arguments $sorts $declarations $free $bound $arguments $parameters) True
                   (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest)))))
             (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest)))
         (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest)))
     ((LCons (GrammarTypingWrappedV1 $actual $category $parameters) $rest)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (if (gslt:premise:schema-arguments $sorts $declarations $free $bound $arguments $parameters) True
               (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest))
             (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest)))
         (gslt:premise:schema-constructors $sorts $declarations $free $bound $label $arguments $expected $rest))))))

(: gslt:premise:schema-collections (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $remaining)
  (case $remaining
    ((LNil False)
     ((LCons (GrammarTypingV1 $label $category $parameters) $rest)
       (case (SchemaCollectionDeclaration $parameters $expected)
         (((SchemaCollectionDeclaration (LCons (TermSimple $parameter (TCollection $actual $element)) LNil) (TBase $sort))
           (if (== $category $sort)
             (if (== $actual $kind)
               (if (gslt:premise:schema-elements $sorts $declarations $free $bound $elements $element)
                 (if (gslt:premise:schema-rest $free $kind $element $capture) True
                   (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $rest))
                 (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $rest))
               (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $rest))
             (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $rest)))
          ($ordinary
           (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $rest)))))
     ((LCons (GrammarTypingWrappedV1 $label $category $parameters) $rest)
       (gslt:premise:schema-collections $sorts $declarations $free $bound $kind $elements $capture $expected $rest)))))

(: gslt:premise:schema-substitutions (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:schema-substitutions $sorts $declarations $free $bound $body $replacement $expected $remaining)
  (case $remaining
    ((LNil False)
     ((LCons $sort $later)
       (let* (($domain (TBase $sort)) ($inner (LCons $domain $bound)))
         (if (gslt:premise:schema-has $sorts $declarations $free $inner $body $expected)
           (if (gslt:premise:schema-has $sorts $declarations $free $bound $replacement $domain) True
             (gslt:premise:schema-substitutions $sorts $declarations $free $bound $body $replacement $expected $later))
           (gslt:premise:schema-substitutions $sorts $declarations $free $bound $body $replacement $expected $later)))))))
