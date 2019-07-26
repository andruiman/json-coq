Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics. 
Require Import CommonHelpers.

Import ListNotations.
Local Open Scope list_scope.

Module Type KeySig.
Parameter key : Set.
Parameter eqKey : key -> key -> bool.
Axiom eqKey_refl : forall k1 k2, eqKey k1 k2 = true <-> k1 = k2.
End KeySig.

Module KeyMap (ks: KeySig).
Import ks.

Hint Resolve eqKey_refl.

Inductive key_map {X:Set} := 
| empty: key_map
| mapkv: key -> X -> key_map -> key_map.

Fixpoint mapmap {X:Set} {Y:Set} (f: X -> Y) (m: @key_map X) :=
match m with
| empty => empty
| mapkv k v kvs => mapkv k (f v) (mapmap f kvs)
end. 

Fixpoint mapkeymap {X:Set} {Y:Set} (f: key -> X -> Y) (m: @key_map X) : list Y :=
match m with
| empty => []
| mapkv k v kvs => (f k v) :: (mapkeymap f kvs)
end.

Fixpoint mapkeymap' {X:Set} {Y:Set} (f: X -> Y) (m: @key_map X) : list Y :=
match m with
| empty => []
| mapkv k v kvs => (f v) :: (mapkeymap' f kvs)
end. 

Definition mapkeymap'' {X:Set} {Y:Set} (f: X -> Y) (m: @key_map X) : list Y:=
mapkeymap (fun _ v => f v) m.

Lemma mapkeymap''equal: forall (X Y:Set) (f: X -> Y) m,
                 mapkeymap'' f m = mapkeymap' f m.
Proof.
 intros. unfold mapkeymap''.
 induction m. simpl. auto.
 simpl. rewrite IHm. auto.
Qed.

Fixpoint merge_maps {X:Set} (m1 m2: @key_map X) :=
match m1 with
| empty => m2
| mapkv k v m1' => merge_maps m1' (mapkv k v m2)
end.

Definition valuelist {X:Set} := mapkeymap' (@id X).

Definition mlookup {X:Set} (m: @key_map X) (k: key) :=
    firstSome (mapkeymap (fun k' v => if (eqKey k k') then Some v else None) m).

End KeyMap.
