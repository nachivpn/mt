-module(b17).
-compile({parse_transform, etc}).

% bad function clause unification - 1

extract (1.0) -> 1.0;
extract (2.0) -> 1.0;
extract (true) -> true;
extract (false) -> false.