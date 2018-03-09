From Hammer Require Import Hammer.













Lemma equal_f : forall {A B : Type} {f g : A -> B},
f = g -> forall x, f x = g x.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.equal_f". Restart. 
intros.
rewrite H.
auto.
Qed.

Lemma equal_f_dep : forall {A B} {f g : forall (x : A), B x},
f = g -> forall x, f x = g x.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.equal_f_dep". Restart. 
intros A B f g <- H; reflexivity.
Qed.



Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
forall (f g : forall x : A, B x),
(forall x, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) :
(forall x, f x = g x) -> f = g.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.functional_extensionality". Restart. 
intros ; eauto using @functional_extensionality_dep.
Qed.


Lemma forall_extensionality {A} {B C : A -> Type} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.forall_extensionality". Restart. 
apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma forall_extensionalityP {A} {B C : A -> Prop} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.forall_extensionalityP". Restart. 
apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma forall_extensionalityS {A} {B C : A -> Set} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.forall_extensionalityS". Restart. 
apply functional_extensionality in H. destruct H. reflexivity.
Defined.


Definition functional_extensionality_dep_good
{A} {B : A -> Type}
(f g : forall x : A, B x)
(H : forall x, f x = g x)
: f = g
:= eq_trans (eq_sym (functional_extensionality_dep f f (fun _ => eq_refl)))
(functional_extensionality_dep f g H).

Lemma functional_extensionality_dep_good_refl {A B} f
: @functional_extensionality_dep_good A B f f (fun _ => eq_refl) = eq_refl.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.functional_extensionality_dep_good_refl". Restart. 
unfold functional_extensionality_dep_good; edestruct functional_extensionality_dep; reflexivity.
Defined.

Opaque functional_extensionality_dep_good.

Lemma forall_sig_eq_rect
{A B} (f : forall a : A, B a)
(P : { g : _ | (forall a, f a = g a) } -> Type)
(k : P (exist (fun g => forall a, f a = g a) f (fun a => eq_refl)))
g
: P g.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.forall_sig_eq_rect". Restart. 
destruct g as [g1 g2].
set (g' := fun x => (exist _ (g1 x) (g2 x))).
change g2 with (fun x => proj2_sig (g' x)).
change g1 with (fun x => proj1_sig (g' x)).
clearbody g'; clear g1 g2.
cut (forall x, (exist _ (f x) eq_refl) = g' x).
{ intro H'.
apply functional_extensionality_dep_good in H'.
destruct H'.
exact k. }
{ intro x.
destruct (g' x) as [g'x1 g'x2].
destruct g'x2.
reflexivity. }
Defined.

Definition forall_eq_rect
{A B} (f : forall a : A, B a)
(P : forall g, (forall a, f a = g a) -> Type)
(k : P f (fun a => eq_refl))
g H
: P g H
:= @forall_sig_eq_rect A B f (fun g => P (proj1_sig g) (proj2_sig g)) k (exist _ g H).

Definition forall_eq_rect_comp {A B} f P k
: @forall_eq_rect A B f P k f (fun _ => eq_refl) = k.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.forall_eq_rect_comp". Restart. 
unfold forall_eq_rect, forall_sig_eq_rect; simpl.
rewrite functional_extensionality_dep_good_refl; reflexivity.
Qed.

Definition f_equal__functional_extensionality_dep_good
{A B f g} H a
: f_equal (fun h => h a) (@functional_extensionality_dep_good A B f g H) = H a.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.f_equal__functional_extensionality_dep_good". Restart. 
apply forall_eq_rect with (H := H); clear H g.
change (eq_refl (f a)) with (f_equal (fun h => h a) (eq_refl f)).
apply f_equal, functional_extensionality_dep_good_refl.
Defined.

Definition f_equal__functional_extensionality_dep_good__fun
{A B f g} H
: (fun a => f_equal (fun h => h a) (@functional_extensionality_dep_good A B f g H)) = H.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun". Restart. 
apply functional_extensionality_dep_good; intro a; apply f_equal__functional_extensionality_dep_good.
Defined.



Tactic Notation "extensionality" ident(x) :=
match goal with
[ |- ?X = ?Y ] =>
(apply (@functional_extensionality _ _ X Y) ||
apply (@functional_extensionality_dep _ _ X Y) ||
apply forall_extensionalityP ||
apply forall_extensionalityS ||
apply forall_extensionality) ; intro x
end.



Ltac extensionality_in_checker tac :=
first [ tac tt | fail 1 "Anomaly: Unexpected error in extensionality tactic.  Please report." ].
Tactic Notation "extensionality" "in" hyp(H) :=
let rec check_is_extensional_equality H :=
lazymatch type of H with
| _ = _ => constr:(Prop)
| forall a : ?A, ?T
=> let Ha := fresh in
constr:(forall a : A, match H a with Ha => ltac:(let v := check_is_extensional_equality Ha in exact v) end)
end in
let assert_is_extensional_equality H :=
first [ let dummy := check_is_extensional_equality H in idtac
| fail 1 "Not an extensional equality" ] in
let assert_not_intensional_equality H :=
lazymatch type of H with
| _ = _ => fail "Already an intensional equality"
| _ => idtac
end in
let enforce_no_body H :=
(tryif (let dummy := (eval unfold H in H) in idtac)
then clearbody H
else idtac) in
let rec extensionality_step_make_type H :=
lazymatch type of H with
| forall a : ?A, ?f = ?g
=> constr:({ H' | (fun a => f_equal (fun h => h a) H') = H })
| forall a : ?A, _
=> let H' := fresh in
constr:(forall a : A, match H a with H' => ltac:(let ret := extensionality_step_make_type H' in exact ret) end)
end in
let rec eta_contract T :=
lazymatch (eval cbv beta in T) with
| context T'[fun a : ?A => ?f a]
=> let T'' := context T'[f] in
eta_contract T''
| ?T => T
end in
let rec lift_sig_extensionality H :=
lazymatch type of H with
| sig _ => H
| forall a : ?A, _
=> let Ha := fresh in
let ret := constr:(fun a : A => match H a with Ha => ltac:(let v := lift_sig_extensionality Ha in exact v) end) in
lazymatch type of ret with
| forall a : ?A, sig (fun b : ?B => @?f a b = @?g a b)
=> eta_contract (exist (fun b : (forall a : A, B) => (fun a : A => f a (b a)) = (fun a : A => g a (b a)))
(fun a : A => proj1_sig (ret a))
(@functional_extensionality_dep_good _ _ _ _ (fun a : A => proj2_sig (ret a))))
end
end in
let extensionality_pre_step H H_out Heq :=
let T := extensionality_step_make_type H in
let H' := fresh in
assert (H' : T) by (intros; eexists; apply f_equal__functional_extensionality_dep_good__fun);
let H''b := lift_sig_extensionality H' in
case H''b; clear H';
intros H_out Heq in
let rec extensionality_rec H H_out Heq :=
lazymatch type of H with
| forall a, _ = _
=> extensionality_pre_step H H_out Heq
| _
=> let pre_H_out' := fresh H_out in
let H_out' := fresh pre_H_out' in
extensionality_pre_step H H_out' Heq;
let Heq' := fresh Heq in
extensionality_rec H_out' H_out Heq';
subst H_out'
end in
first [ assert_is_extensional_equality H | fail 1 "Not an extensional equality" ];
first [ assert_not_intensional_equality H | fail 1 "Already an intensional equality" ];
(tryif enforce_no_body H then idtac else clearbody H);
let H_out := fresh in
let Heq := fresh "Heq" in
extensionality_in_checker ltac:(fun tt => extensionality_rec H H_out Heq);

destruct Heq; rename H_out into H.



Lemma eta_expansion_dep {A} {B : A -> Type} (f : forall x : A, B x) :
f = fun x => f x.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.eta_expansion_dep". Restart. 
intros.
extensionality x.
reflexivity.
Qed.

Lemma eta_expansion {A B} (f : A -> B) : f = fun x => f x.
Proof. hammer_hook "FunctionalExtensionality" "FunctionalExtensionality.eta_expansion". Restart. 
apply (eta_expansion_dep f).
Qed.
