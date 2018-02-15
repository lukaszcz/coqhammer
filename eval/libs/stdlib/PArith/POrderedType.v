From Hammer Require Import Hammer.









Require Import BinPos Equalities Orders OrdersTac.

Local Open Scope positive_scope.



Module Positive_as_DT <: UsualDecidableTypeFull := Pos.






Module Positive_as_OT <: OrderedTypeFull := Pos.







Module PositiveOrder := OTF_to_OrderTac Positive_as_OT.
Ltac p_order := PositiveOrder.order.


