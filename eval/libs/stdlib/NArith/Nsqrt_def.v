From Hammer Require Import Hammer.









Require Import BinNat.



Notation Nsqrtrem := N.sqrtrem (compat "8.3").
Notation Nsqrt := N.sqrt (compat "8.3").
Notation Nsqrtrem_spec := N.sqrtrem_spec (compat "8.3").
Notation Nsqrt_spec := (fun n => N.sqrt_spec n (N.le_0_l n)) (compat "8.3").
Notation Nsqrtrem_sqrt := N.sqrtrem_sqrt (compat "8.3").
