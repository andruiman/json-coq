Require Import Lists.List.

Import ListNotations.
Local Open Scope list_scope.

Fixpoint firstSome {X} (l: list (option X)): option X :=
match l with
| [] => None
| (Some x):: _ => Some x
| None :: l => firstSome l
end.

Fixpoint firstSome_ind' {X} (n:nat) (l: list (option X)): option (nat*X) :=
match l with
| [] => None
| (Some x):: _ => Some (n, x)
| None :: l => firstSome_ind' (S n) l
end.

Definition firstSome_ind {X} := @firstSome_ind' X 0.

Fixpoint flatten {X} (ll: list (list X)) : list X :=
match ll with
| [] => []
| l::ls => app l (flatten ls)
end.

Fixpoint indexate_with' {X Y} (n:nat) (f: nat -> Y) (l: list X) :=
match l with
| [] => []
| x::xs => (f n,x)::(indexate_with' (S n) f xs)
end.

Definition indexate {X} := @indexate_with' X nat 0 (@id nat).
Definition indexate_with {X Y} := @indexate_with' X Y 0.

Fixpoint replace {X} (n: nat) (l: list X) (x: X) :=
match l, n with
| [], _ => []
| a::l', 0 => x::l'
| a::l', S n' => a::(replace n' l' x)
end.

Fixpoint take {X} (n: nat) (l: list X): list X :=
match n, l with
| O, _ => []
| S n', [] => []
| S n', x::l' => x::(take n'  l')
end.

Fixpoint drop {X} (n: nat) (l: list X): list X :=
match n, l with
| O, _ => l
| S n', [] => []
| S n', x::l' => drop n' l'
end.

Definition droplast {X} (n: nat) (l: list X): list X :=
rev (drop n (rev l)).

Eval compute in (droplast 2 [1;2;3]). 


Lemma replace_replaced: forall X n l (x: X), nth n (replace n l x) x = x.
Proof.
 intros. generalize dependent n. induction l; intros; destruct n; auto.
 simpl. apply IHl.
Qed.

Definition mnth_error {X} (ll: list (list (option X))) m n : option X :=
let ml := nth_error ll m in
match ml with 
| None => None
| Some l => let mk := nth_error l n in
            match mk with
            | Some None => None
            | Some x => x
            | None => None
            end
end. 

Fixpoint replaceSome {X} (l: list (option X)) x :=
match l with 
| [] => []
| a::l' => if a then x::(replaceSome l' x)
                else a::(replaceSome l' x)
end.

Fixpoint filterSome {X} (l: list (option X)) : list X :=
match l with
| [] => []
| None::xs => filterSome xs
| (Some x) :: xs => x::(filterSome xs)
end.

Fixpoint bany (l: list bool): bool :=
match l with
| [] => false
| true::_ => true
| _::l' => bany l'
end.


Fixpoint zip_first_with {X Y T} (ks: list X) (lxy: list (T*Y)) d (f: T->X): list (X*Y) :=
match ks, lxy with
| [], _ => map (fun (ky:T*Y) => let (k,y):= ky in (f k,y)) lxy
| _, [] => map (fun k => (k,d)) ks
| k::kss, (x,y)::lxys => (k,y)::(zip_first_with kss lxys d  f)
end.

Fixpoint ziplists' {X} (ll : list (list X))  (l: list X) :=
match ll, l with
| _, [] => ll
| [], x::xs => map (fun x => [x]) l
| lx::lxs, x::xs => (app lx [x])::(ziplists' lxs xs)
end.

Eval compute in (ziplists' [[1;2]; [3;4]] [5;6;7;8]).
Eval compute in (ziplists' [] [5;6;7;8]).

Definition ziplists {X} (ll : list (list X)) :=
 fold_left ziplists' ll [].

Eval compute in (ziplists [[1;2]; [3;4]; [5;6;7;8]]).

Inductive ablist (X: Type) :=
|alist: list (ablist X) -> ablist X
|blist: list (ablist X) -> ablist X.








