:- discontiguous(rule/3).

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

% Recursively verifies the proof line by line.
%
% [H|T] = Proof
% Verified:    previously verified proof lines
% VerifiedNew: previously and newly verified proof lines
verify_proof(_, [], _) :- !.
verify_proof(Premises, [H|T], Verified) :-
   rule(Premises, H, Verified),
   append(Verified, [H], VerifiedNew),
   verify_proof(Premises, T, VerifiedNew).

% PREMISE
rule(Premises, [_, Formula, premise], _) :-
   member(Formula, Premises).

% ----------
% ASSUMPTION
% ----------

% [H|T] = Verified
% append_premises(_, [], _) :- !.
% append_premises(Premises, [H|VerifiedLines], PremisesNew) :-
%    nth0(1, H, Premise),
%    append(Premises, [Premise], PremisesNew),
%    append_premises(PremisesNew, VerifiedLines, _).

% rule(Premises, [[R, Formula, assumption] | T], Verified) :-
%    append_premises(Premises, Verified, TempPremises),
%    append(TempPremises, [Formula], BoxPremises),
%    % Writing '_' instead of '[]' in the below "verify_proof"
%    % statement makes "negint.txt" evaluate to true.
%    % WHY ???
%    verify_proof(
%       BoxPremises, [[R, Formula, premise] | T], _
%    ).

% [Assumption | T] = Box Proof,
%     Assumption = [R, Formula, assumption]
rule(Premises, [[R, Formula, assumption] | T], Verified) :-
   append(Verified, [[R, Formula, assumption]], VerifiedNew),
   verify_proof(
      Premises, 
      T, 
      VerifiedNew
   ).

%LAW OF EXCLUDED MIDDLE
rule(_, [_, or(X, neg(X)), lem], _Verified).

% COPY
rule(_, [_, X, copy(R)], Verified) :-
   member([R, X, _], Verified).

% DOUBLE NEGATION INTRODUCTION
rule(_, [_, neg(neg(X)), negnegint(R)], Verified) :-
   member([R, X, _], Verified).

% DOUBLE NEGATION ELIMINATION
rule(_, [_, X, negnegel(R)], Verified) :-
   member([R, neg(neg(X)), _], Verified).

% AND INTRODUCTION
%
% R1:       row number of formula X
% R2:       row number of formula Y
% Verified: currently verified proof lines
rule(_, [_, and(X, Y), andint(R1, R2)], Verified) :-
   member([R1, X, _], Verified),
   member([R2, Y, _], Verified).

% 1st AND ELIMINATION
rule(_, [_, X, andel1(R)], Verified) :-
   member([R, and(X, _), _], Verified).

% 2nd AND ELIMINATION
rule(_, [_, Y, andel2(R)], Verified) :-
   member([R, and(_, Y), _], Verified).

% 1st OR INTRODUCTION
rule(_, [_, or(X, _), orint1(R)], Verified) :-
   member([R, X, _], Verified).

% 2nd OR INTRODUCTION
rule(_, [_, or(_, X), orint2(R)], Verified) :-
   member([R, X, _], Verified).

% OR ELIMINATION (requires assumptions)
rule(_, [_, X, orel(R, S1, S2, T1, T2)], Verified) :-
   member([R, or(A, B), _], Verified),
   
   member([[S1, A, assumption] | TailS], Verified),
   last(TailS, BoxConclusionS),
   [S2, X, _] = BoxConclusionS,

   member([[T1, B, assumption] | TailT], Verified),
   last(TailT, BoxConclusionT),
   [T2, X, _] = BoxConclusionT.

% IMPLICATION INTRODUCTION
rule(_, [_, imp(X, Y), impint(R1, R2)], Verified) :-
   member([[R1, X, assumption] | T], Verified),
   last(T, BoxConclusion),
   [R2, Y, _] = BoxConclusion.

% IMPLICATION ELIMINATION
rule(_, [_, Y, impel(R1, R2)], Verified) :-
   member([R1, X, _], Verified),
   member([R2, imp(X, Y), _], Verified).

% NEGATION INTRODUCTION
rule(_, [_, neg(X), negint(R1, R2)], Verified) :-
   member([[R1, X, assumption] | T], Verified),
   last(T, BoxConclusion),
   [R2, cont, _] = BoxConclusion.

% NEGATION ELIMINATION
rule(_, [_, cont, negel(R1, R2)], Verified) :-
   member([R1, X, _], Verified),
   member([R2, neg(X), _], Verified).

% CONTRADICTION ELIMINATION
rule(_, [_, _X, contel(R)], Verified) :-
   member([R, cont, _], Verified).

% MODUS TOLLENS
rule(_, [_, neg(X), mt(R1, R2)], Verified) :-
   member([R1, imp(X, Y), _], Verified),
   member([R2, neg(Y), _], Verified).

% PROOF BY CONTRADICTION
rule(_, [_, X, pbc(R1, R2)], Verified) :-
   member([[R1, neg(X), assumption] | T], Verified),
   last(T, BoxConclusion),
   [R2, cont, _] = BoxConclusion.

