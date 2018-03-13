-module (g4).
-compile({parse_transform, etc}).

% "Erlangy" arithmetic

foo1() -> 1 + 1.5.

foo2() -> 1 + 2.

foo3() -> 1.5 + 4.5.

foo4() -> 1.5;
foo4() -> 3.

add (A,B) -> A + B.

addTestII() -> add(1,2).

addTestIF() -> add(1,3.5).

addTestFF() -> add(4.5,3.5).

getInt() -> 1.

getFloat() -> 1.5.

addTestVars() ->
    X = getInt(),
    Y = getFloat(),
    add(X,Y).

divTest() ->
    X = getInt(),
    X div X.

% use nums with integer operator
foo5(X,Y) -> add(X,Y) div X.

% use integer with num operator 
foo6() -> X = 6, add(X, X).

bar(Y) -> Y + 1.

foo(X,Y) -> X = bar(1.0), Y = bar(1) div 1, Y.
