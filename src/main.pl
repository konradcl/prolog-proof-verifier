verify(InputFileName) :-
  see(InputFileName),
  read(Premises), read(Conclusion), read(Proof),
  seen,
  valid_proof(Premises, Conclusion, Proof).

% The proof is valid if the proof ends with the sequent's
% conclusion.
valid_proof(Premises, Conclusion, Proof) :- 
   verify_end(Conclusion, Proof),
   verify_proof(Premises, Proof, []).

% Verifies that proof ends with the sequent's conclusion.
verify_end(Conclusion, Proof) :-
    last(Proof, Line),              % line := last proof line
    nth0(1, Line, ProofConclusion), % select ProofConclusion
    Conclusion = ProofConclusion.

% HELLO!!!:
% Recursively verifies the proof line by line.
%
% [H|T] = Proof
% Verified:    previously verified proof lines
% VerifiedNew: previously and newly verified proof lines
verify_proof(_, []) :- !.
verify_proof(Premises, [H|T], Verified) :-
   premise(Premises, H);
   rule(H, Verified);
   assumption(
      Premises, 
      [[_R, _Formula, assumption] | T], 
      Verified
   ),
   append(Verified, H, VerifiedNew),
   verify_proof(Premises, T, VerifiedNew).

premise(_, []) :- !.
premise(Premises, [_, Formula, premise]) :-
   member(Formula, Premises).

% LAW OF EXCLUDED MIDDLE
% NOT WORKING!!!
rule([_, or(X, neg(X)), lem], _Verified).

% COPY
rule([_, X, copy(R)], Verified) :-
   member([R, X, _], Verified).

% DOUBLE NEGATION INTRODUCTION
rule([_, neg(neg(X)), negnegint(R)], Verified) :-
   member([R, X, _], Verified).

% DOUBLE NEGATION ELIMINATION
rule([_, X, negnegel(R)], Verified) :-
   member([R, neg(neg(X)), _], Verified).

% AND INTRODUCTION
%
% R1:       row number of formula X
% R2:       row number of formula Y
% Verified: currently verified proof lines
rule([_, and(X, Y), andint(R1, R2)], Verified) :-
   member([R1, X, _], Verified),
   member([R2, Y, _], Verified).

% 1st AND ELIMINATION
rule([_, X, andel1(R)], Verified) :-
   member([R, and(X, _), _], Verified).

% 2nd AND ELIMINATION
rule([_, Y, andel2(R)], Verified) :-
   member([R, and(_, Y), _], Verified).

% 1st OR INTRODUCTION
rule([_, or(X, _), orint1(R)], Verified) :-
   member([R, X, _], Verified).

% 2nd OR INTRODUCTION
rule([_, or(_, X), orint2(R)], Verified) :-
   member([R, X, _], Verified).

% OR ELIMINATION (requires assumptions)
% rule([_, X, orel(R, S1, S2, T1, T2)], Verified) :-
%    member([R, or(A, B), _], Verified),
%    member([])

% IMPLICATION INTRODUCTION

% IMPLICATION ELIMINATION
rule([_, Y, impel(R1, R2)], Verified) :-
   member([R1, X, _], Verified),
   member([R2, imp(X, Y), _], Verified).

% NEGATION INTRODUCTION
rule([_, neg(X), negint(R1, R2)], Verified) :-
   member([[R1, X, assumption] | T], Verified),
   last(T, BoxConclusion),
   [R2, cont, _] = BoxConclusion.

% NEGATION ELIMINATION
rule([_, cont, negel(R1, R2)], Verified) :-
   member([R1, X, _], Verified),
   member([R2, neg(X), _], Verified).

% CONTRADICTION ELIMINATION
rule([_, _X, contel(R)], Verified) :-
   member([R, cont, _], Verified).

% MODUS TOLLENS
rule([_, neg(X), mt(R1, R2)]) :-
   member([R1, imp(X, Y), _], Verified),
   member([R2, neg(Y), _], Verified).

