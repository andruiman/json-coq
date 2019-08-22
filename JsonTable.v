Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.

Require Export Json.
Require Export JsonTree.

Import ListNotations.
Import JsonNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope json_scope.


Definition jtable := list (list (option jpoint)). 

Fixpoint list_fill {X} (n: nat) (x:X): list X :=
match n with
| O => []
| S n' => x::(list_fill n' x)
end.

Definition jtable_fill (n: nat) (a: option jpoint): jtable:=
list_fill n (list_fill n None).

Definition jtable_set (jt: jtable) (m n: nat) (a: option jpoint) : jtable :=
let ml := nth_error jt m in
match ml with
| Some l => replace m jt (replace n l a)
| None => jt
end.

Inductive indjnode := 
| ind_data_node: nat -> JsonData -> indjnode
| ind_root_node: nat -> nat -> indjnode.

Definition nlj_type := (nat*(list indjnode)*jtable)%type.

Check fold_left.
(*fold_left
     : forall A B : Type,
       (A -> B -> A) ->
       list B -> A -> A*)

(*fold_right (B -> A -> A) ->
       A -> list B -> A*)

Print fold_right.

(*Lemma fst_fold_assoc: forall A1 A2 B (f:A1*A2->B->A1*A2) a l, fst (fold_left f l a) = fold_left (fun a b => fst (f a b)) l (fst a).*)

Fixpoint jtree_table' (m: nat) (k: option jpoint) (jt: jtree)  
                      (nlj: nlj_type) {struct jt}: nlj_type :=
let (nl, jtb) := nlj in
let (n, jr) := nl in
match jt with
| tleaf s => let newtb := jtable_set jtb m n k in
             (S n, app jr [ind_data_node n s] , newtb)
| tlbranch tl => fold_left (fun nlj kt => jtree_table' n (Some (inr (fst kt))) (snd kt) nlj) 
                            tl (S n, app jr [ind_root_node m n], jtable_set jtb m n k)
| tmbranch tm => fold_left (fun nlj kt => jtree_table' n (Some (inl (fst kt))) (snd kt) nlj) 
                            tm (S n, app jr [ind_root_node m n], jtable_set jtb m n k)
end.

Definition jtree_table jt := let tb3 := jtree_table' 0 None jt (0, [],  
                             (jtable_fill (length (jtree_nodes jt)) None)) in
                             (snd (fst tb3), snd tb3).

Definition clear_node_index (l: list indjnode) : jtable_row :=
map (fun n => match n with
| ind_data_node _ s => data_node s
| ind_root_node _ _ => root_node
end) l.

Lemma clear_node_index_cons: forall a l, clear_node_index (a::l) = app (clear_node_index [a]) (clear_node_index l).
Proof.
 intros. generalize dependent a. induction l; intros.
 simpl. destruct a; auto.
 simpl. destruct a; destruct a0; auto.
Qed.

Lemma clear_node_index_app: forall a l, clear_node_index (app a l) = app (clear_node_index a) (clear_node_index l).
Proof.
 intros. generalize dependent l. induction a; intros.
 simpl. auto.
 simpl. destruct a. rewrite IHa. auto.
 rewrite IHa. auto.
Qed.

Lemma one_tree_row: forall m m' n n' jtb jtb' k t jr jr' jr'', 
clear_node_index (app jr jr') = clear_node_index jr'' ->
app (clear_node_index jr) (clear_node_index (snd (fst (jtree_table' m' k t (n', jr', jtb'))))) =
clear_node_index (snd (fst (jtree_table' m k t (n, jr'', jtb)))).
Proof.
 intros.  generalize dependent jr. generalize dependent jr'. 
 generalize dependent jr''. generalize dependent jtb.
 generalize dependent jtb'. generalize dependent n. generalize dependent n'.
 generalize dependent m. generalize dependent m'.
 generalize dependent k.
 induction t using tree_ind'; intros.
 simpl. rewrite 2 clear_node_index_app. simpl.
 rewrite clear_node_index_app in H.
 rewrite <- H. apply app_assoc.
 
 simpl.
 remember (S n') as n'1. remember (app jr' [ind_root_node m' n']) as jr'1.
 remember (jtable_set jtb' m' n' k) as jtb'1.
 remember (S n) as n1. remember (app jr'' [ind_root_node m n]) as jr''1.
 remember (jtable_set jtb m n k) as jtb1. 
 assert (clear_node_index (jr ++ jr'1) = clear_node_index jr''1).
 subst. rewrite 3 clear_node_index_app. simpl. 
 rewrite <- H0. rewrite clear_node_index_app. apply app_assoc.
 generalize H1.
 generalize jr'1.
 generalize jr''1. generalize jtb1.
 generalize jtb'1. generalize n'1. 
 generalize n1. generalize n'. generalize n.
 induction lj; intros. simpl.
 rewrite <- clear_node_index_app. auto. simpl.
 destruct a. replace (map snd ((n3, t) :: lj)) with
 (t :: map snd lj) in H; auto. inversion H. clear H.
 simpl. 
 remember (jtree_table' n'0 (Some (inr n3)) t (n'2, jr'0, jtb'0)).
 remember (jtree_table' n0 (Some (inr n3)) t (n2, jr''0, jtb0)).
 destruct n4. destruct p.
 destruct n5. destruct p.
 apply IHlj with (n:=n0) (n':=n'0) (n1:=n5) (n'1:=n4) (jtb'1:=j) (jtb1:=j0)
 (jr''1:=l1) (jr'1:=l0) in H6.
 apply H6. rewrite clear_node_index_app.
 replace l0 with (snd (fst (jtree_table' n'0 (Some (inr n3)) t (n'2, jr'0, jtb'0)))).
 replace l1 with (snd (fst (jtree_table' n0 (Some (inr n3)) t (n2, jr''0, jtb0)))).
 clear IHlj. apply H5. auto. rewrite <- Heqn5. auto.
 rewrite <- Heqn4. auto.

 simpl.
 remember (S n') as n'1. remember (app jr' [ind_root_node m' n']) as jr'1.
 remember (jtable_set jtb' m' n' k) as jtb'1.
 remember (S n) as n1. remember (app jr'' [ind_root_node m n]) as jr''1.
 remember (jtable_set jtb m n k) as jtb1. 
 assert (clear_node_index (jr ++ jr'1) = clear_node_index jr''1).
 subst. rewrite 3 clear_node_index_app. simpl. 
 rewrite <- H0. rewrite clear_node_index_app. apply app_assoc.
 generalize H1.
 generalize jr'1.
 generalize jr''1. generalize jtb1.
 generalize jtb'1. generalize n'1. 
 generalize n1. generalize n'. generalize n.
 induction mj; intros. simpl.
 rewrite <- clear_node_index_app. auto. simpl.
 destruct a. replace (map snd ((k0, t) :: mj)) with
 (t :: map snd mj) in H; auto. inversion H. clear H.
 simpl. 
 remember (jtree_table' n'0 (Some (inl k0)) t (n'2, jr'0, jtb'0)).
 remember (jtree_table' n0 (Some (inl k0)) t (n2, jr''0, jtb0)).
 destruct n3. destruct p.
 destruct n4. destruct p.
 apply IHmj with (n:=n0) (n':=n'0) (n1:=n4) (n'1:=n3) (jtb'1:=j)
 (jtb1:=j0) (jr''1:=l1) (jr'1:=l0) in H6.
 apply H6. rewrite clear_node_index_app.
 replace l0 with (snd (fst (jtree_table' n'0 (Some (inl k0)) t (n'2, jr'0, jtb'0)))).
 replace l1 with (snd (fst (jtree_table' n0 (Some (inl k0)) t (n2, jr''0, jtb0)))).
 clear IHmj. apply H5. auto. rewrite <- Heqn4. auto.
 rewrite <- Heqn3. auto.
Qed.


Lemma jtable_nodes_equal': forall jt m k n jr jtb, app (clear_node_index jr) (jtree_nodes jt) = 
                                     clear_node_index (snd (fst (jtree_table' m k jt (n, jr, jtb)))).
Proof.
 intros jt.
 induction jt using tree_ind'; intros.
 simpl. rewrite clear_node_index_app. simpl. auto.

 simpl.
 remember (S n) as n1.
 remember (jtable_set jtb m n k) as jtb1.
 replace (clear_node_index jr ++
 root_node :: flatten (map (compose jtree_nodes snd) lj))%list with
 ((clear_node_index (jr ++ [ind_root_node m n]) ++ 
  flatten (map (compose jtree_nodes snd) lj)))%list.
 remember (app jr  [ind_root_node m n]) as jr1.
 generalize n1 jr1 jtb1 n. 
 induction lj; intros.
 simpl. apply app_nil_r. 
 destruct a.
 replace (map snd ((n3, t) :: lj)) with (t::map snd lj) in H; auto.
 inversion_clear H. simpl.
 remember (jtree_table' n2 (Some (inr n3)) t (n0, jr0, jtb0)).
 destruct n4. destruct p.
 replace (clear_node_index jr0 ++
  compose jtree_nodes snd (n3, t) ++
    flatten (map (compose jtree_nodes snd) lj))%list with 
 ((clear_node_index jr0 ++ jtree_nodes t) ++
    flatten (map (compose jtree_nodes snd) lj))%list.
 rewrite <- IHlj with (jr1:=l).
 rewrite H0 with (m:=n2) (k:=Some (inr n3)) (n:=n0) (jtb:=jtb0).
 replace l with (snd (fst (jtree_table' n2 (Some (inr n3)) t (n0, jr0, jtb0)))).
 auto. rewrite <- Heqn4. auto. auto. rewrite app_assoc.
 unfold compose. simpl. auto. rewrite clear_node_index_app.
 simpl. rewrite <- app_assoc. simpl. auto.

 simpl.
 remember (S n) as n1.
 remember (jtable_set jtb m n k) as jtb1.
 replace (clear_node_index jr ++
 root_node :: flatten (map (compose jtree_nodes snd) mj))%list with
 ((clear_node_index (jr ++ [ind_root_node m n]) ++ 
  flatten (map (compose jtree_nodes snd) mj)))%list.
 remember (app jr  [ind_root_node m n]) as jr1.
 generalize n1 jr1 jtb1 n. 
 induction mj; intros.
 simpl. apply app_nil_r. 
 destruct a.
 replace (map snd ((k0, t) :: mj)) with (t::map snd mj) in H; auto.
 inversion_clear H. simpl.
 remember (jtree_table' n2 (Some (inl k0)) t (n0, jr0, jtb0)).
 destruct n3. destruct p.
 replace (clear_node_index jr0 ++
  compose jtree_nodes snd (k0, t) ++
    flatten (map (compose jtree_nodes snd) mj))%list with 
 ((clear_node_index jr0 ++ jtree_nodes t) ++
    flatten (map (compose jtree_nodes snd) mj))%list.
 rewrite <- IHmj with (jr1:=l).
 rewrite H0 with (m:=n2) (k:=Some (inl k0)) (n:=n0) (jtb:=jtb0).
 replace l with (snd (fst (jtree_table' n2 (Some (inl k0)) t (n0, jr0, jtb0)))).
 auto. rewrite <- Heqn3. auto. auto. rewrite app_assoc.
 unfold compose. simpl. auto. rewrite clear_node_index_app.
 simpl. rewrite <- app_assoc. simpl. auto.
Qed.


Lemma jtable_nodes_equal: forall jt, jtree_nodes jt = 
                                     clear_node_index (fst (jtree_table jt)).
Proof.
 intros. unfold jtree_table. simpl. rewrite <- jtable_nodes_equal'.
 simpl. auto.
Qed.

Fixpoint jtable_tree' (n: nat) (m: nat) 
                      (jr: jtable_row) (jtb: jtable) {struct n}: option jtree :=
match n with
| O => None
| S n' => 
let mr := nth_error jtb m in
match mr with
| Some r => let r' := indexate r in 
            let fix iter_row r jt :=
            match r with
            | [] => jt
            | (_, None)::rs => iter_row rs jt
            | (n, Some (inr k))::rs => 
                                   let md := nth_error jr n in
                                   iter_row rs match md with
                                   | Some (data_node s) => 
                                               match jt with
                                               | None => Some (tlbranch [(k, tleaf s)])
                                               | Some (tlbranch tl) => Some (tlbranch (app tl [(k, tleaf s)]))
                                               | _ => jt
                                               end
                                   | Some root_node => let mt' := jtable_tree' n' n jr jtb in
                                               match mt' with
                                               | None => jt
                                               | Some t' => 
                                                 match jt with
                                                 | None => Some (tlbranch [(k, t')])
                                                 | Some (tlbranch tl) => Some (tlbranch (app tl [(k, t')]))
                                                 | _ => jt
                                                 end
                                               end
                                   | None => None
                                   end
            | (n, Some (inl k))::rs => 
                                   let md := nth_error jr n in
                                   iter_row rs match md with
                                   | Some (data_node s) => 
                                               match jt with
                                               | None => Some (tmbranch [(k, tleaf s)])
                                               | Some (tmbranch tm) => Some (tmbranch (app tm [(k, tleaf s)]))
                                               | _ => jt
                                               end
                                   | Some root_node => let mt' := jtable_tree' n' n jr jtb in
                                               match mt' with
                                               | None => jt
                                               | Some t' => 
                                                 match jt with
                                                 | None => Some (tmbranch [(k, t')])
                                                 | Some (tmbranch tm) => Some (tmbranch (app tm [(k, t')]))
                                                 | _ => jt
                                                 end
                                               end
                                   | None => None
                                   end
            end in
            let mjt' := iter_row r' None in
            match mjt' with
            | None => Some (tlbranch [])
            | _ => mjt' 
            end
| None => None
end
end.

Definition jtable_tree jr jtb := jtable_tree' ((length jr)*(length jr)) 0 jr jtb.

Fixpoint path_ind' (n:nat) (lk: jpath) (jr: list indjnode) (jtb: jtable) : 
                                                  option (nat + nat*nat) :=
match lk with
| [] => let mv := nth_error jr n in
        match mv with
        | None => None
        | Some (ind_data_node n _) => Some (inl n)
        | Some (ind_root_node m n) => Some (inr (m, n))
        end
| k::ks => let mr := nth_error jtb n in
           match mr with
           | None => None
           | Some r => let mn := find k r in
                       match mn with
                       | None => None
                       | Some n => path_ind' n ks jr jtb
                       end
           end
end.

Definition tree_path_ind lk jt := let (jr, tb) := jtree_table jt in
                                  path_ind' 0 lk jr tb.


Definition table_json_default jr tb j :=
let mtr := jtable_tree jr tb in
match mtr with
| None => j
| Some tr => let mj' := tree_json  tr in
                         match mj' with
                         | None => j
                         | Some j' => j'
                         end
end.

(* Haskell extraction directives *)

Require Extraction.
Extraction Language Haskell.
Extraction "coq-hs/JsonTable.hs" jtable_tree.



Eval compute in (tree_path_ind [inr 2; inl "baz"; inl "x"]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))).
                    
Eval compute in (tree_path_ind [inr 1; inl "bar"]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))).

                    
Eval compute in  (nth_error (snd (jtree_table
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])))) 8).


(*tests*)

Let json1 := '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Let jtree1 := json_tree json1.
Let tn1 := jtree_nodes jtree1.
Let jtb10 := jtable_fill (length tn1) None.
Let jtb1 := jtree_table jtree1.
Eval compute in jtb1.
Let jtree1':= jtable_tree tn1 (snd jtb1).

Example jtt_eq1: Some jtree1 = jtree1'.
Proof. compute. auto. Qed.

Example jtt_eq2: tn1 = clear_node_index (fst jtb1).
Proof. auto. Qed.

