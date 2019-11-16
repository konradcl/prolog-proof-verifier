verify(InputFileName) :-
  see(InputFileName),
  read(Premises), read(Goal), read(Proof),
  seen,
  valid_proof(Premises, Goal, Proof).

%% part of premises and goal

% The proof is valid if the proof ends with the sequent's
% conclusion.
valid_proof(Premises, Goal, Proof) :- 
   writeln(Premises),
   writeln(Goal),
   writeln(Proof),
   verify_end(Goal, Proof),
   verify_proof(Premises, Proof).

% Verifies that proof ends with the sequent's conclusion 
% (goal).
verify_end(Goal, Proof) :-
    last(Proof, Line),
    nth0(1, Line, ProofConclusion),
    Goal = ProofConclusion.

% Proof = [H|T]
verify_proof(_, []) :- !.
verify_proof(Premises, [H|T]) :-
   premise(Premises, H),
   verify_proof(Premises, T).

premise(_, []) :- !.
premise(Premises, [1, Formula, premise]) :-
   member(Formula, Premises).


