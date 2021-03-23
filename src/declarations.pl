
:- op(1110, xfx, [::]).
:- op(1030, fx,  [caused,
                  default,
                  exogenous,
                  inertial,
                  nonexecutable,
                  constraint,
                  always,
                  rigid]).
:- op(1030, xfx, [causes,
                  maycause]).
:- op(1020, xfx, [if]).
:- op(1010, xfx, [after,
                  unless]).
:- op(770,  xfy, [iff]).
:- op(765,  xfy, [++]).
:- op(760,  xfy, [&]).
:- op(710,  xfy, [:]).                  % overrides Prolog precedence 550
:- op(540,  xfx, [..]).
:- op(200,  fy,  [-]).