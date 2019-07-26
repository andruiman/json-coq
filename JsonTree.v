Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.

Require Export Json. 
Require Export CommonHelpers.
Require Export StringHelpers.

Import ListNotations.
Import JsonNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope json_scope.

Inductive tree (X Y: Set) : Set :=
| tleaf : X -> @tree X Y
| tlbranch : list (nat*tree X Y) -> tree X Y
| tmbranch : list (Y*tree X Y) -> tree X Y.
(*the empty tree can be written as "tlbranch []"*)

Arguments tleaf [X] [Y].
Arguments tlbranch [X] [Y].
Arguments tmbranch [X] [Y].

Section tree_ind'.

Variable X Y: Set.
Variable P: tree X Y -> Prop.

Hypothesis tree_leaf_case : forall (x : X),
    P (tleaf x).

Hypothesis tree_list_case : forall (lj : list (nat*tree X Y)),
    Forall P (map snd lj) -> P (tlbranch lj).

Hypothesis tree_map_case : forall (mj : list (Y*tree X Y)),
    Forall P (map snd mj) -> P (tmbranch mj).

Fixpoint tree_ind' (t : tree X Y) : P t :=
match t return (P t) with
| tleaf x => tree_leaf_case x
| tlbranch lt => tree_list_case lt
        ((fix tree_list_ind (lt : list (nat*tree X Y)) : Forall P (map snd lt) :=
          match lt with
            | [] => Forall_nil P
            | (k,t)::ltx => @Forall_cons (tree X Y) P t (map snd ltx) (tree_ind' t) (tree_list_ind ltx)
          end) lt)
| tmbranch lt => tree_map_case lt
        ((fix tree_list_ind (lt : list (Y*tree X Y)) : Forall P (map snd lt) :=
          match lt with
            | [] => Forall_nil P
            | (k,t)::ltx => @Forall_cons (tree X Y) P t (map snd ltx) (tree_ind' t) (tree_list_ind ltx)
          end) lt)
end.

End tree_ind'.

Definition jtree := tree JsonData key.

Fixpoint json_tree (j: json): jtree :=
match j with
| $s => tleaf s
| 'l => tlbranch (indexate (map json_tree l))
| &m => let fix map_tree (mm: @key_map json) :=
            match mm with
            | empty => []
            | mapkv k v kvs => (k, json_tree v)::map_tree kvs 
            end in
        tmbranch (map_tree m)
end.

Fixpoint tree_json (jt: jtree): option json :=
match jt with
| tleaf s => Some $s
| tlbranch lt => let l := fold_right (fun (kt:nat*jtree) l =>
                                    match l with
                                    | Some l => let mj := tree_json (snd kt) in
                                                       match mj with
                                                       | Some j => Some (cons j l)
                                                       | None => None
                                                       end
                                    | _ => None
                                    end) (Some []) lt in
                           match l with
                           | None => None
                           | Some l => Some 'l
                           end
| tmbranch mt => let m := fold_right (fun (kt: key*jtree) m =>  
                                        let (k, t) := kt in
                                        match k, m with 
                                        | k, Some m => let mj := tree_json t in
                                                           match mj with
                                                           | Some j => Some (mapkv k j m)
                                                           | None => None
                                                           end
                                        | _, _ => None 
                                        end) (Some empty) mt in
                                  match m with
                                  | None => None
                                  | Some m => Some &m
                                  end
end.

Check json_ind'.

Lemma tree_json_ind_ign: forall lj m n, fold_right
  (fun (kt : nat * jtree) (l : option (list json)) =>
   match l with
   | Some l0 =>
       match tree_json (snd kt) with
       | Some j => Some (j :: l0)
       | None => None
       end
   | None => None
   end) (Some []) (indexate_with' m id (map json_tree lj)) =
fold_right
  (fun (kt : nat * jtree) (l : option (list json)) =>
   match l with
   | Some l0 =>
       match tree_json (snd kt) with
       | Some j => Some (j :: l0)
       | None => None
       end
   | None => None
   end) (Some []) (indexate_with' n id (map json_tree lj)).
Proof.
 intros lj. induction lj; intros. auto.
 simpl. rewrite IHlj with (n:= S n).
 auto.
Qed.

Lemma tree_json_inv: forall j, tree_json (json_tree j) = Some j.
Proof.
 intros. induction j using json_ind'.
 simpl. auto.
 induction lj. auto.
 inversion_clear H. apply IHlj in H1.
 simpl. rewrite H0. simpl in H1.
 remember (fold_right
         (fun (kt : nat * jtree) (l : option (list json)) =>
          match l with
          | Some l0 =>
              match tree_json (snd kt) with
              | Some j => Some (j :: l0)
              | None => None
              end
          | None => None
          end) (Some []) (indexate (map json_tree lj))).
 replace (fold_right
      (fun (kt : nat * jtree) (l : option (list json)) =>
       match l with
       | Some l0 =>
           match tree_json (snd kt) with
           | Some j => Some (j :: l0)
           | None => None
           end
       | None => None
       end) (Some []) (indexate_with' 1 id (map json_tree lj))) with o.
 destruct o; inversion H1; auto. rewrite Heqo.
 unfold indexate.
 apply tree_json_ind_ign. 
 induction mj. auto.
 inversion_clear H. apply IHmj in H1.
 simpl. rewrite H0. simpl in H1.
 remember (fold_right
         (fun (kt : key * jtree) (m : option key_map) =>
          let (k, t) := kt in
          match m with
          | Some m0 => match tree_json t with
                       | Some j => Some ((k) # (j) m0)
                       | None => None
                       end
          | None => None
          end) (Some empty)
         ((fix map_tree (mm : key_map) : list (key * jtree) :=
             match mm with
             | empty => []
             | (k) # (v) kvs => (k, json_tree v) :: map_tree kvs
             end) mj)).
 destruct o; inversion H1; auto. 
Qed. 

Inductive MergeStrategyIn := SMergeRight | SReplace | SMergeLeft | SExchange. 
Inductive MergeStrategyOut := SRemoveOrigin | SLeaveOrigin.
Inductive NameStrategy := 
| SRenameNode: key -> NameStrategy
| SLeaveNodeName: NameStrategy.

Inductive MergeStrategyT := 
| MergeStrategy: MergeStrategyIn -> MergeStrategyOut ->
                 NameStrategy -> NameStrategy -> MergeStrategyT.

Definition MergeStrategy0 := MergeStrategy SMergeRight SLeaveOrigin 
                             SLeaveNodeName SLeaveNodeName.

Definition merge_trees (t1 t2: jtree) (s: MergeStrategyT) : jtree :=
match t1,t2 with
| tleaf s1, tleaf s2 => tlbranch (indexate [t1; t2])

| tleaf s1, tlbranch tl2 => tlbranch (indexate (t1::(map snd tl2)))
| tlbranch tl1, tleaf s2 => tlbranch (indexate (app (map snd tl1) [t2]))
| tlbranch tl1, tlbranch tl2 => tlbranch (indexate (app (map snd tl1) (map snd tl2)))

| tleaf s1, tmbranch tm2 => tmbranch ((indexNat 0, t1)::tm2)
| tmbranch tm1, tleaf s2 =>  tmbranch (app tm1 [(indexNat 0, t2)])
| tmbranch tm1, tmbranch tm2 => tmbranch (app tm1 tm2)

| tlbranch tl1, tmbranch tm2 => tmbranch (app (indexate_with indexNat (map snd tl1)) tm2)
| tmbranch tm1, tlbranch tl2 => tmbranch (app tm1 (indexate_with indexNat (map snd tl2)))
end.


Definition tlookup {X} (tm: list (key*(tree X key))) (k: key) :=
firstSome (map (fun (k'v: key*(tree X key)) => let (k', v) := k'v in
                           if (string_dec k k') then Some v else None) tm).

Definition tlookup_ind {X} (tm: list (key*(tree X key))) (k: key) :=
firstSome_ind (map (fun (k'v: key*(tree X key)) => let (k', v) := k'v in
                           if (string_dec k k') then Some v else None) tm).

Fixpoint tree_get (kk: jpoint) (jt: jtree) {struct jt}: option (nat*jtree) :=
match kk with
| inl k => match jt with
              | tmbranch tm => tlookup_ind tm k
              | _ => None
           end
| inr k => match jt with
              | tlbranch tl  => nth_error tl k
              | _ => None
           end
end.

Fixpoint tree_getin (lk: jpath) (jt: jtree): option jtree :=
match lk with
| [] => Some jt
| k::ks => let mjt' := tree_get k jt in
           match mjt' with
           | None => None
           | Some (_,jt') => tree_getin ks jt'
           end 
end.

Fixpoint tree_setin (lk: jpath) (to_jt jt: jtree): jtree :=
match lk with
| [] => jt
| k::ks => let mjt' := tree_get k to_jt in
           match mjt' with
           | None => to_jt
           | Some (n, to_jt') => let nt := tree_setin ks to_jt' jt in
                                 match k, to_jt with
                                 | inr k, tlbranch tl => (tlbranch (replace n tl (k, nt)))
                                 | inl k, tmbranch tm => (tmbranch (replace n tm (k, nt)))
                                 | _,_ => to_jt
                                 end
           end 
end.

Definition tree_mergein (lk: jpath) (to_jt jt: jtree) s: jtree :=
let mjt':= tree_getin lk to_jt in
match mjt' with
| None => to_jt
| Some to_jt' => tree_setin lk to_jt (merge_trees to_jt' jt s)
end.

Definition tree_submerge_with (lk_to lk_from: jpath) 
                              (f: jpath -> jtree -> jtree) (jt: jtree) (s: MergeStrategyT): jtree :=
let mjt_from' := tree_getin lk_from jt in
match mjt_from' with
| Some jt_from' => tree_mergein lk_to jt (f lk_from jt_from') s
| None => jt
end.

Definition tree_submerge (lk_to lk_from: jpath) 
                         (jt: jtree) (s: MergeStrategyT): jtree :=
tree_submerge_with lk_to lk_from (fun _ jt => jt) jt s.

Definition tree_modify (lk_in: jpath) (jt: jtree) (f: jtree -> jtree) : jtree :=
let mjt' := tree_getin lk_in jt in
match mjt' with
| Some jt' => tree_setin lk_in jt (f jt')
| None => jt
end.

Definition concat_tree_with (d: JsonData) (jt: jtree): jtree :=
match jt with
| tleaf s => tleaf s
| tlbranch tl => tleaf (fold_right (fun i r => match i with
                                        | (_, tleaf s) => if (string_dec r "") then s 
                                                          else (s ++ d ++ r)
                                        | _ => r
                                        end) ""  tl)
| tmbranch tm => tleaf (fold_right (fun i r => match i with
                                        | (_, tleaf s) => if (string_dec r "") then s 
                                                          else (s ++ d ++ r)
                                        | _ => r
                                        end) ""  tm)
end.

Inductive jnode := 
| data_node: JsonData -> jnode
| root_node: jnode.

Definition jtable_row := list jnode.

Fixpoint json_nodes (j: json): jtable_row :=
match j with
| $s => [data_node s]
| 'l => root_node::flatten (map json_nodes l)
| &m => let fix map_nodes (mm: @key_map json): jtable_row :=
            match mm with
            | empty => []
            | mapkv k v kvs => app (json_nodes v) (map_nodes kvs)
            end in
        root_node::map_nodes m
end.

Fixpoint jtree_nodes (jt: jtree): jtable_row :=
match jt with
| tleaf s => [data_node s]
| tlbranch tl => root_node::flatten (map (compose jtree_nodes snd) tl)
| tmbranch tm => root_node::flatten (map (compose jtree_nodes snd) tm)
end.

Lemma jtree_nodes_ind_ign: forall X Y T (f:Y->T) m n ind1 ind2 l,
            map (fun xy : X * Y => f (snd xy)) (indexate_with' m ind1 l) = 
            map (fun xy : X * Y => f (snd xy)) (indexate_with' n ind2 l).
Proof.
 intros. generalize dependent m. generalize dependent n. 
 induction l; intros; auto. simpl. rewrite IHl with (n:= S n).
 auto.
Qed.


Lemma jtree_nodes_equal: forall j, json_nodes j = jtree_nodes (json_tree j).
Proof.
 intros. induction j using json_ind'.
 simpl. auto. induction lj. simpl. auto.
 inversion_clear H. apply IHlj in H1. 
 simpl. unfold compose. simpl. rewrite <- H0.
 simpl in H1. inversion H1. clear H1.
 rewrite H2. unfold compose. unfold indexate.
 rewrite jtree_nodes_ind_ign with (n:=1) (ind2:=id). auto.
 induction mj. simpl. auto.
 inversion_clear H. apply IHmj in H1. 
 simpl. unfold compose. simpl. rewrite <- H0.
 simpl in H1. inversion H1. clear H1.
 rewrite H2. unfold compose. auto.
Qed.


Definition split_tree_with (d: JsonData) (jt: jtree): jtree :=
match jt with
| tleaf s => let ss := split_string s d in
             tlbranch (indexate (map (@tleaf JsonData key) ss))
| _ => jt (* FIXME *)
end.

Definition tree_wild_get (p: jpoint) (jpt: jpath*jtree): list (jpath*jtree) :=
let (p0, jt) := jpt in
match p with
| inr k => let mt := tree_get p jt in
           match mt with
           | None => []
           | Some (_, t) => [(app p0 [p], t)]
           end
| inl k => match jt with
           | tleaf s => []
           | tlbranch tl => map (fun kt => (app p0 [inr (fst kt)], snd kt))
                            (filter (fun (kt:nat*jtree) => let (k', t) := kt in
                                     match_string k (indexNat k')) tl)
           | tmbranch tm => map (fun kt => (app p0 [inl (fst kt)], snd kt))
                            (filter (fun (kt:key*jtree) => let (k', t) := kt in
                                     match_string k k') tm)
           end
end.

Definition zip_tree_with (ks: list key) (jt: jtree) : jtree :=
match jt with
| tleaf _ => jt
| tlbranch tl => tmbranch (zip_first_with ks tl (tlbranch []) indexNat)
| tmbranch tm => tmbranch (zip_first_with ks tm (tlbranch []) (@id key))
end.

Definition map_tree_with (ks: list key) (jt: jtree) : jtree :=
match jt with
| tleaf _ => jt
| tlbranch tl => tlbranch (map (fun (kt:nat*jtree) => let (k,t) := kt in  
                                          (k, zip_tree_with ks t)) tl)
| tmbranch tm => tmbranch (map (fun (kt:key*jtree) => let (k,t) := kt in  
                                          (k, zip_tree_with ks t)) tm)
end.

Definition map_tree_with_old (ks: list key) (jt: jtree) : jtree :=
match jt with
| tleaf _ => jt
| tlbranch tl => tlbranch (indexate (map (fun (ks:nat*key) => let (k,s):=ks in 
                                let txs := filterSome (map (tree_get (inr k)) (map snd tl)) in
                                tmbranch [(s, tlbranch txs)] ) (indexate ks)))
| _ => jt
end.

Fixpoint ziptrees' (ll : list jtree)  (l: jtree) :=
match ll, l with
| _, tlbranch [] => ll
| [], tlbranch ((_::_) as l) => map (fun x => tlbranch [x]) l
| (tlbranch lx)::lxs, tlbranch (x::xs) => (tlbranch (app lx [x]))::(ziptrees' lxs (tlbranch xs))
| _,_ => ll
end.

(*tests*)

Let json1 := '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Let jtree1 := json_tree json1.

Example tree_json1 : tree_json jtree1 = Some json1.
Proof. auto. Qed.

Example tree_setin1 : tree_json 
                  (tree_setin [inr 2; inl "baz"; inl "x"; inr 1] jtree1 (tleaf "e")) = 
                  Some '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"e"]}}].
Proof. auto. Qed.


Example json_tree1 : jtree1 =
        tlbranch [(0,
          tmbranch
            [("foo",
             tlbranch
               [(0, tleaf "Andy"); (1, tleaf "Peter")])]);
         (1, tmbranch [("bar", tleaf "Good")]);
         (2,
         tmbranch
           [("baz",
            tmbranch
              [("x",
               tlbranch [(0, tleaf "d"); (1, tleaf "f")])])])].
Proof. auto. Qed.

Example tree_modify1: tree_json (tree_modify [inr 0; inl "foo"] jtree1 (concat_tree_with " ")) = 
                  Some '[{"foo" # $"Andy Peter"}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Proof. auto. Qed.

Example tree_setin2: tree_json (tree_setin [inr 2; inl "baz"; inl "x"; inr 0] jtree1 (tleaf "e")) =
                 Some '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"e"; $"f"]}}].
Proof. auto. Qed.

Example tree_mergein1: tree_json (tree_mergein [inr 2; inl "baz"; inl "x"] jtree1 (tleaf "j") MergeStrategy0) =
                    Some '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"; $"j"]}}].
Proof. auto. Qed.

Example tree_submerge1: tree_json (tree_submerge [inr 0] [inr 2; inl "baz"; inl "x"] jtree1 MergeStrategy0) = 
                   Some '[{"foo" # '[$"Andy"; $"Peter"], "#0" # $"d", "#1" # $"f"}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Proof. compute. auto. Qed.

Let json2 := {"menu" # {"header" # $"SVG Viewer",
    "items" # '[
        {"id"# $"Open"};
        {"id"# $"OpenNew", "label"# $"Open New"};
        {"id"# $"ZoomIn", "label"# $"Zoom In"};
        {"id"# $"ZoomOut", "label"# $"Zoom Out"};
        {"id"# $"OriginalView", "label"# $"Original View"};
        {"id"# $"Quality"};
        {"id"# $"Pause"};
        {"id"# $"Mute"};
        {"id"# $"Find", "label"# $"Find..."};
        {"id"# $"FindAgain", "label"# $"Find Again"};
        {"id"# $"Copy"};
        {"id"# $"CopyAgain", "label"# $"Copy Again"};
        {"id"# $"CopySVG", "label"# $"Copy SVG"};
        {"id"# $"ViewSVG", "label"# $"View SVG"};
        {"id"# $"ViewSource", "label"# $"View Source"};
        {"id"# $"SaveAs", "label"# $"Save As"};
        {"id"# $"Help"};
        {"id"# $"About", "label"# $"About Adobe CVG Viewer..."}]}}.

Let tree2 := json_tree json2.
Let json2' := tree_json tree2.

Example tree_json2: Some json2 = json2'.
Proof. auto. Qed.

Example json_nodes1: json_nodes json1 = 
                     [root_node; root_node; root_node; data_node "Andy";
       data_node "Peter"; root_node; data_node "Good"; root_node;
       root_node; root_node; data_node "d"; data_node "f"].
Proof. auto. Qed.
