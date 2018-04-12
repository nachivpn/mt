-module(b18).
-compile({parse_transform, etc}).

% bad function clause unification - 2

extract (1.0) -> 1.0;
extract (2.0) -> 1.0;
extract (true) -> true;
extract (true) -> true;
extract (false) -> false.