/*---------------------------------------------------------------
   Maze Solver and SAT in Prolog
   NAME: Deepak Luitel 

*/


%%%%%%%%%%%%%%%%%%%%%%
% Part 1 - Recursion %
%%%%%%%%%%%%%%%%%%%%%%

% prod - R is product of entries in list L


prod([],1). 
prod([H|T],R) :- 
	prod(T,R1), 
	R is R1*H.
% fill - R is list of N copies of X
fill(0,_,[]).
fill(N,X,[X|R]) :- 
	N>0,
	N1 is N-1,
	fill(N1,X,R).

% genN - R is value between 0 and N-1, in order

gen(N,M,M).
gen(N,M,R):-
	N>0,
	N1 is N-1,
	M1 is M+1,
	gen(N1,M1,R).
genN(N,R) :-
	N>0,
	N1 is N-1,
	gen(N1,0,R).
% genXY - R is pair of values [X,Y] between 0 and N-1, in lexicographic order

genZ(N,X,Y,[X,Y]).
genZ(N,Re,Z,R):-
	Z<N-1,
	Z1 is Z+1,
	genZ(N,Re,Z1,R).

genXY(N,R) :-
	genN(N,Re),			
	genZ(N,Re,0,R).		

% flat(L,R) - R is elements of L concatentated together, in order
flath([],[]).
flath([H|T],[H|L1]):-
	flath(T,L1).
flath(H,[H]).
flat([],[]) :-!.
flat([H|T],R) :-
	!,
	flath(H,L1),!,
	flat(T,L2),
	append(L1,L2,R).

%%%%%%%%%%%%%%%%%%%%%%%%
% Part 2 - Maze Solver %
%%%%%%%%%%%%%%%%%%%%%%%%

% stats(U,D,L,R) - number of cells w/ openings up, down, left, right
 
stats(U,D,L,R) :-
  maze(N,_,_,_,_),
  N1 is N-1,
  stats(N1,N1,U,D,L,R).
stats(0,-1,0,0,0,0).
% Y out of boundry
stats(X,-1,U,D,L,R) :- 
  maze(N,_,_,_,_),
  N1 is N-1, X1 is X-1,
  stats(X1,N1,U,D,L,R).
stats(X,Y,U,D,L,R) :-
  cell(X,Y,Dir_List,_),
  openings(Dir_List,U1,D1,L1,R1),
  Y1 is Y-1,
  stats(X,Y1,U2,D2,L2,R2),
  U is U1+U2, D is D1+D2, L is L1+L2, R is R1+R2.

% get openings on the cell from Dir_List
openings(Dir_List,U,D,L,R) :- 
  has(u,Dir_List,U),
  has(d,Dir_List,D),
  has(l,Dir_List,L),
  has(r,Dir_List,R).

% X = dir and L is list of dir on the cell
has(X,L,1) :- member(X,L),!.
has(_,_,0).

% validPath(N,W) - W is weight of valid path N rounded to 4 decimal places

validPath(N,W) :- 
  maze(_,SX,SY,_,_),
  path(N,SX,SY,Dir_List),  
  moveinPath(SX,SY,Dir_List,Weit),
  round4(Weit,W).
% moving the path.
moveinPath(EX,EY,[],0) :- maze(_,_,_,EX,EY).
moveinPath(X,Y,[D|T],W) :-
  cell(X,Y,Dir_List,Weits), 
  member(D,Dir_List),      
  weit(D,Dir_List,Weits,M1),
  shift(D,X,Y,X1,Y1),
  moveinPath(X1,Y1,T,M2),
  W is M1+M2.

% changes the coordinates of moving path
shift(l,X,Y,X1,Y) :- X1 is X-1.
shift(r,X,Y,X1,Y) :- X1 is X+1.
shift(u,X,Y,X,Y1) :- Y1 is Y-1.
shift(d,X,Y,X,Y1) :- Y1 is Y+1.
% weight of the each shift
weit(D,[D|_],[W|_],W).
weit(D,[_|TD],[_|TW],W) :- weit(D,TD,TW,W).

round4(X,Y) :- T1 is X*10000, T2 is round(T1), Y is T2/10000.

% findDistance(L) - L is list of coordinates of cells at distance D from start


findDistance(L) :- 
	maze(_,SX,SY,_,_),
	findDistance([SX,SY],L).

findDistance(C,L):-findDistance([C],0,[],[],[],[],L).  % visited = accumulator = next cells = empty
% Base case if Z = 0 then put it in List.

findDistance([],Z,Visited,Acc,AF,NextCells,L):-
	sort(Acc,ACC),
	append(Z,ACC,L1),
	append(AF,L1,Lz),
	Z1 is Z+1,
	findDistance([],Z1,Visited,[],Lz,[],L),
	L = Lz,!.

findDistance([],_,_,_,AF,[],AF):- !.

findDistance([H|T],Z,Visited,ACC,AF,NextCells,L) :-
  append([H],ACC,Acc),
  append([H],Visited,Visited1),    		% Add current node to visited
  neighbors(H,Neb),        				% Neb is a list of neighbors of C (or [] if none).
  subtract(Neb,Visited,L1),    			% L1 are unvisited neighbors
  append(L1,NextCells,N),!,				% N = Next level of cells
  findDistance(T,Z,Visited1,Acc,AF,N,L),!, l = Acc.

  

% L is a list of adjacent cells (ie, open wall) of [X,Y]
neighbors([X,Y],L) :-
  cell(X,Y,Dirs,_),
  neighbors([X,Y],Dirs,L).
neighbors(_,[],[]).
neighbors([X,Y],[H|T],[[X1,Y1]|L]) :- 
  move(H,X,Y,X1,Y1),  % X1,Y1 is cell in direction H from X,Y
  neighbors([X,Y],T,L).

move(u,X,Y,X,Y1) :- Y1 is Y-1.
move(d,X,Y,X,Y1) :- Y1 is Y+1.
move(l,X,Y,X1,Y) :- X1 is X-1.
move(r,X,Y,X1,Y) :- X1 is X+1.
 

% solve - True if maze is solvable, fails otherwise.
solve :-
	validPath(N,W),!.
/*
solve:-
	maze(_,SX,SY,EX,EY), solvable([SX,SY],Fs), member([EX,EY],Fs).
*/

%%%%%%%%%%%%%%%%
% Part 3 - SAT %
%%%%%%%%%%%%%%%%
/*
let rec eval f e = match f with 
    False -> false
  | True -> true
  | Var x -> (match e with 
			[] -> false
			|h::t -> if (fst h = x) then snd h else eval f t)
  | And (f1,f2) -> (eval f1 e) && (eval f2 e)
  | Or (f1,f2) -> eval f1 e || eval f2 e
  | Not f1 -> if eval f1 e = false then true else true
  | Forall (x,f1) -> eval f1((x, true)::e) && eval f1((x, false)::e)
  | Exists (x,f1) -> eval f1((x, true)::e) || eval f1((x, false)::e)
*/
% eval(F,A,R) - R is t if formula F evaluated with list of 
%                 true variables A is true, false otherwise


ret(H,[],[]).
ret(H,[H|T],T1) :-ret(H,T,T1).
ret(H,[H1|T],[H1|T1]) :-
	H \= H1,ret(H,T,T1).

eval(t,_,t):-!.
eval(f,_,f):-!.

eval([and,X,Y],A,t):-
	eval(X,A,R1),R1 = t,
	eval(Y,A,R2),R2 = t,!.
eval([and,X,Y],A,f):-!.

% if eval x returns true then stop and return true
eval([or,X,Y],A,t):-
	eval(X,A,t),!.
% if above or fails eval y and return whatever y evals.
eval([or,X,Y],A,R):-
	eval(Y,A,R),!.

eval([no,X],A,t):-
	eval(X,A,f),!.
eval([no,X],A,f):- 
	eval(X,A,t),!.

eval([every,V,F],A,R):-
	ret(V,A,R1),
	eval(F,[V|R1],t),
	eval(F,R1,R),!.

eval([exists,V,F],A,R) :-
	eval(F,A,Z),Z = t, R = t,!.
eval([exists,V,F],A,R) :-
	append([V],A,R1),
	eval(F,R1,R2),R2 = t,R = t,!.
eval(H,A,t):-
	member(H,A),!.
eval(H,A,f):-
	\+(member(H,A)),!.

% varsOf(F,R) - R is list of free variables in formula F
% true base case return empty
varsOf(t,[]):-!.
% false base case  return empty
varsOf(f,[]):-!.
% no case
varsOf([no,X],R):-
	varsOf(X,L1), sort(L1,R),!.
% and case 
varsOf([and,X,Y],R):-
	varsOf(X,L1), varsOf(Y,L2),
	append(L1,L2,R1),
	sort(R1,R),!.
% or case
varsOf([or,X,Y],R):-
	varsOf(X,L1),varsOf(Y,L2),
	append(L1,L2,R1),
	sort(R1,R),!.
% every case
varsOf([every,X,Y],R):-
	varsOf(Y,L1), ret(X,L1,L2),
	sort(L2,R),!.
% exists case
varsOf([exists,V,F],A,R) :-
	varsOf(F,[V|A],L1),sort(L1,R),!.
% exists case
varsOf([exists,V,F],R) :-
	varsOf(F,[V],L1),
	sort(L1,R),!.
% single variables
varsOf(X,[X]):-!.
varsOf(V,A,[]) :-
	member(V,A),!.
varsOf(V,A,[V]):-!.

% sat(F,R) - R is a list of true variables that satisfies F
sat(F,R) :- 
	varsOf(F,L1),subset(L1,R),eval(F,R,t).

% Helper Function
% subset(L, R) - R is a subset of list L, with relative order preserved

subset([], []).
subset([H|T], [H|NewT]) :- subset(T, NewT).
subset([_|T], NewT) :- subset(T, NewT).

m(X,Y) :- a(X),b(Y),!.
a(X):-a(X),!.
a(those):-!.
a(that).
b(not).
b(no).

n(X):-l(X),!.
l([[0,[[0,3]]],[1,[[1,2],[2,1]]]]).
