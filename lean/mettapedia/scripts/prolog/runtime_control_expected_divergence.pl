:- initialization(main, main).

main(_) :-
    catch(throw(_), error(instantiation_error, _),
        writeln('throw_variable=instantiation_error')).
