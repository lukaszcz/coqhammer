From Hammer Require Import Hammer.











Set Implicit Arguments.

Declare ML Module "z_syntax_plugin".



Inductive positive : Set :=
| xI : positive -> positive
| xO : positive -> positive
| xH : positive.

Delimit Scope positive_scope with positive.
Bind Scope positive_scope with positive.
Arguments xO _%positive.
Arguments xI _%positive.



Inductive N : Set :=
| N0 : N
| Npos : positive -> N.

Delimit Scope N_scope with N.
Bind Scope N_scope with N.
Arguments Npos _%positive.



Inductive Z : Set :=
| Z0 : Z
| Zpos : positive -> Z
| Zneg : positive -> Z.

Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.
Arguments Zpos _%positive.
Arguments Zneg _%positive.
