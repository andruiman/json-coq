Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.

Definition natToDigit (n : nat) : string :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := (natToDigit (n mod 10)) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Example writeNat174: writeNat 174 = "174".
Proof.
 auto.
Qed. 

Example writeNat10: writeNat 10 = "10".
Proof.
 auto.
Qed. 

Example writeNat0: writeNat 0 = "0".
Proof.
 auto.
Qed. 

Definition key := string.
Definition data := string.

Inductive key_map {X} := 
| empty: key_map
| mapkv: key -> X -> key_map -> key_map.

Inductive json :=
| json_data: data -> json
| json_list : list json  -> json
| json_map: @key_map json -> json.

Module JsonNotations.
Notation "{ }" := (json_map empty): json_scope.
Infix "#" := mapkv (at level 0): json_scope.
Notation "{ k # v }" := (json_map (mapkv k v empty))
                                 (right associativity): json_scope.
Notation "{ kv1 , .. , kv2 }" := (json_map (kv1 .. (kv2 empty) ..))
                                 (right associativity): json_scope.
Notation "$ s" := (json_data s)
                       (at level 0, right associativity): json_scope.
Notation "' l" := (json_list l)
                  (at level 0, right associativity): json_scope.
Notation "& m" := (json_map m)
                  (at level 0, right associativity): json_scope.
End JsonNotations.

Import JsonNotations.
Local Open Scope json_scope.
Delimit Scope json_scope with json.

Check ($"foo").
Check { "foo" # $"bar" }.
Check ('([$"foo"]%list)).
Check {"1" # $"Andy" , "2" # $"Peter"}.

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

Fixpoint mapmap {X Y} (f: X -> Y) (m: @key_map X) :=
match m with
| empty => empty
| mapkv k v kvs => mapkv k (f v) (mapmap f kvs)
end. 

Fixpoint mapkeymap {X Y} (f: key -> X -> Y) (m: @key_map X) : list Y :=
match m with
| empty => []
| mapkv k v kvs => (f k v) :: (mapkeymap f kvs)
end.

Fixpoint mapkeymap' {X Y} (f: X -> Y) (m: @key_map X) : list Y :=
match m with
| empty => []
| mapkv k v kvs => (f v) :: (mapkeymap' f kvs)
end. 

Definition mapkeymap'' {X Y} (f: X -> Y) (m: @key_map X) : list Y:=
mapkeymap (fun _ v => f v) m.

Lemma mapkeymap''equal: forall X Y (f: X -> Y) m,
                 mapkeymap'' f m = mapkeymap' f m.
Proof.
 intros. unfold mapkeymap''.
 induction m. simpl. auto.
 simpl. rewrite IHm. auto.
Qed.

Fixpoint merge_maps {X} (m1 m2: @key_map X) :=
match m1 with
| empty => m2
| mapkv k v m1' => merge_maps m1' (mapkv k v m2)
end.

Definition valuelist {X} := mapkeymap' (@id X).

Definition jsonmap (f: json -> json) (j: json) :=
match j with
| $ _ => f j
| 'l => ' (map f l)
| & m => & (mapmap f m)
end.

Eval compute in (jsonmap (fun x => {}) {"foo" # $"foo", "bar" # $"bar"}).

Definition mlookup {X} (m: @key_map X) (k: key) :=
firstSome (mapkeymap (fun k' v => if (string_dec k k') then Some v else None) m).

Fixpoint json_get (kk: key + nat) (j: json) {struct j}: option json :=
match kk with
| inl k => match j with
              | & m  => mlookup m k
              | _ => None
           end
| inr k => match j with
              | ' l  => nth_error l k
              | _ => None
           end
end.

Eval compute in (json_get (inl "foo") {"foo" # $"Andy", "bar" #  $"Peter"}).
Eval compute in (json_get (inl "bar") {"foo" # $"Andy", "bar" #  $"Peter"}).
Eval compute in (json_get (inl "baz") {"foo" # $"Andy", "bar" #  $"Peter"}).

Eval compute in (json_get (inr 0) '[$"Andy"; $"Peter"]).
Eval compute in (json_get (inr 1) '[$"Andy"; $"Peter"]).
Eval compute in (json_get (inr 2) '[$"Andy"; $"Peter"]).

Eval compute in (json_get (inr 0) $"Andy").
Eval compute in (json_get (inl "foo") $"Andy").

Fixpoint json_getin (lk: list (key + nat)) (j: json): option json :=
match lk with
| [] => Some j
| k::ks => let mj' := json_get k j in
           match mj' with
           | None => None
           | Some j' => json_getin ks j'
           end 
end.

Eval compute in (json_getin [inl "foo"; inr 1] 
                 {"foo" # '[$"Andy"; $"Peter"]}).

Fixpoint flatten {X} (ll: list (list X)) : list X :=
match ll with
| [] => []
| l::ls => app l (flatten ls)
end.

Fixpoint map2list (m: key_map) : list json :=
match m with
| empty => []
| mapkv k v kvs => v::(map2list kvs)
end.

Inductive tree (X Y: Type) : Type :=
| tleaf : X -> @tree X Y
| tlbranch : list (nat*tree X Y) -> tree X Y
| tmbranch : list (Y*tree X Y) -> tree X Y.

(*the empty tree can be written as "tlbranch []"*)

Arguments tleaf [X] [Y].
Arguments tlbranch [X] [Y].
Arguments tmbranch [X] [Y].

Definition jtree := tree data key.

Fixpoint indexate_with' {X Y} (n:nat) (f: nat -> Y) (l: list X) :=
match l with
| [] => []
| x::xs => (f n,x)::(indexate_with' (S n) f xs)
end.

Definition indexate {X} := @indexate_with' X nat 0 (@id nat).
Definition indexate_with {X Y} := @indexate_with' X Y 0.

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


Eval compute in (json_tree 
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])).

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


Eval compute in (tree_json (json_tree 
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))).

Example eqtree1 : (tree_json (json_tree 
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))) =
                    Some '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Proof.
 auto.
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

Eval compute in ("d" ++ "b").

Definition indexNat (n: nat):  string :=
"#" ++ (writeNat n).

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


Fixpoint tree_get (kk: key + nat) (jt: jtree) {struct jt}: option (nat*jtree) :=
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

Fixpoint tree_getin (lk: list (key + nat)) (jt: jtree): option jtree :=
match lk with
| [] => Some jt
| k::ks => let mjt' := tree_get k jt in
           match mjt' with
           | None => None
           | Some (_,jt') => tree_getin ks jt'
           end 
end.

Fixpoint replace {X} (n: nat) (l: list X) (x: X) :=
match n,l with
| _, [] => []
| 0, (a::l') => x::l'
| S n', (a::l') => a::(replace n' l' x)
end.

Eval compute in (replace 0 [1;2] 0).
Eval compute in (replace 1 [1;2] 0).
Eval compute in (replace 2 [1;2] 0).
Eval compute in (replace 0 [] 0).
Eval compute in (replace 0 [1] 0).


Fixpoint tree_setin (lk: list (key + nat)) (to_jt jt: jtree): option jtree :=
match lk with
| [] => Some jt
| k::ks => let mjt' := tree_get k to_jt in
           match mjt' with
           | None => None
           | Some (n, to_jt') => let mnt := tree_setin ks to_jt' jt in
                                 match k, to_jt, mnt with
                                 | _,_,None => None
                                 | inr k, tlbranch tl, Some nt => Some (tlbranch (replace n tl (k, nt)))
                                 | inl k, tmbranch tm, Some nt => Some (tmbranch (replace n tm (k, nt)))
                                 | _,_,_ => None
                                 end
           end 
end.


Eval compute in (tree_setin [inr 2; inl "baz"; inl "x"; inr 1]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])) (tleaf "e")).

Example eq2: forall a, a = (tree_setin [inr 2; inl "baz"; inl "x"; inr 0]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])) (tleaf "e")) ->
                    exists t, a = Some t /\
                    tree_json t = Some '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"e"; $"f"]}}].
Proof.
 intros. compute in H. exists (tlbranch
         [(0,
          tmbranch
            [("foo",
             tlbranch
               [(0, tleaf "Andy");
               (1, tleaf "Peter")])]);
         (1,
         tmbranch
           [("bar", tleaf "Good")]);
         (2,
         tmbranch
           [("baz",
            tmbranch
              [("x",
               tlbranch
                 [(0, tleaf "e");
                 (1, tleaf "f")])])])]).
 split. rewrite H. auto.
 compute. auto.
Qed.

Definition tree_mergein (lk: list (key + nat)) (to_jt jt: jtree) s: option jtree :=
let mjt':= tree_getin lk to_jt in
match mjt' with
| None => None
| Some to_jt' => tree_setin lk to_jt (merge_trees to_jt' jt s)
end.

Eval compute in (tree_mergein [inr 2; inl "baz"; inl "x"]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])) (tleaf "j") MergeStrategy0).


Definition tree_submerge (lk_to lk_from: list (key + nat)) 
                         (jt: jtree) (s: MergeStrategyT): option jtree :=
let mjt_from' := tree_getin lk_from jt in
match mjt_from' with
| Some jt_from' => tree_mergein lk_to jt jt_from' s
| None => None
end.

Let t0:= (tree_submerge [inr 0]
                               [inr 2; inl "baz"; inl "x"]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])) MergeStrategy0).

Eval compute in t0.

Eval compute in (option_map (tree_getin [inr 0; inl "#1"]) t0).

Inductive node := 
| data_node: data -> node
| root_node: node.

Definition jtable_row := list node.

Fixpoint json_nodes (j: json): jtable_row :=
match j return (list node) with
| $s => [data_node s]
| 'l => root_node::flatten (map json_nodes l)
| &m => let fix map_nodes (mm: @key_map json): list node :=
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

Eval compute in (json_nodes 
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])).

Eval compute in (jtree_nodes (json_tree
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))).

Example jtree_json_nodes1: (json_nodes 
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))=
                    (jtree_nodes (json_tree
                 ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))).
Proof.
 auto.
Qed.


Definition jtable := list (list (option (key+nat))). 

Fixpoint list_fill {X} (n: nat) (x:X): list X :=
match n with
| O => []
| S n' => x::(list_fill n' x)
end.

Eval compute in (list_fill 5 0). 

Definition jtable_fill (n: nat) (a: option (key+nat))
                      : jtable:=
list_fill n (list_fill n None).

Eval compute in (jtable_fill 5).

Definition jtable_set (jt: jtable) (m n: nat) (a: option (key+nat)) :=
let ml := nth_error jt m in
match ml with
| Some l => replace m jt (replace n l a)
| None => jt
end.


Eval compute in (jtable_set (jtable_fill 5 None) 2 3 (Some (inl "foo"))).
Check indexate.

Inductive indnode := 
| ind_data_node: nat -> data -> indnode
| ind_root_node: nat -> nat -> indnode.

Check (8,7,6).

Eval compute in (let (a,b):=(8,7,6) in a).

Fixpoint jtree_table' (m n: nat) (k: option (key+nat)) (jr: list indnode)
                      (jt: jtree) (jtb: jtable) {struct jt}: 
                      nat*(list indnode)*jtable :=
match jt with
| tleaf s => let newtb := jtable_set jtb m n k in
             (S n, app jr [ind_data_node n s] , newtb)
| tlbranch tl => let newtb':= jtable_set jtb m n k in
                 let jr' := app jr [ind_root_node m n] in
                 let fix iter_tree m n k tl jr jtb {struct tl}:=
                 match tl with
                 | [] => (n, jr, jtb)
                 | (a,t)::ts => let (jn'', newtb'') := 
                                       jtree_table' m n (Some (inr a)) jr t jtb in
                                let (n', jr'') := jn'' in 
                                iter_tree m n' None ts jr'' newtb''
                 end in
                 iter_tree n (S n) k tl jr' newtb'
| tmbranch tm => let newtb':= jtable_set jtb m n k in
                 let jr' := app jr [ind_root_node m n] in
                 let fix iter_tree m n k tm jr jtb {struct tm}:=
                 match tm with
                 | [] => (n, jr, jtb)
                 | (a,t)::ts => let (jn'', newtb'') := 
                                       jtree_table' m n (Some (inl a)) jr t jtb in
                                let (n', jr'') := jn'' in
                                iter_tree m n' None ts jr'' newtb''
                 end in
                 iter_tree n (S n) k tm jr' newtb'
end.

Definition jtree_table jt := jtree_table' 0 0 None [] jt 
                             (jtable_fill (length (jtree_nodes jt)) None).

Let j1 := '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Let t1 := json_tree j1.
Eval compute in t1.
Let tn1 := jtree_nodes t1.
Eval compute in tn1.
Let jtb10 := jtable_fill (length tn1) None.
Eval compute in jtb10.
Let jtb1 := jtree_table t1.
Eval compute in (jtb1, tn1).

Check nth_error.

Fixpoint jtable_tree' (n: nat) (m: nat) (jr: jtable_row) (jtb: jtable) {struct n}: option jtree :=
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
            iter_row r' None
| None => None
end
end.

Definition jtable_tree jr jtb := jtable_tree' ((length jr)*(length jr)) 0 jr jtb.

Let t2:=(jtable_tree tn1 (snd jtb1)).

Example jtt_eq1: Some t1 = t2.
Proof.
 auto.
Qed.

Definition clear_node_index (l: list indnode) : jtable_row :=
map (fun n => match n with
| ind_data_node _ s => data_node s
| ind_root_node _ _ => root_node
end) l.

Eval compute in (tn1, snd (fst jtb1)).

Example jtt_eq2: tn1 = clear_node_index (snd (fst jtb1)).
Proof.
 auto.
Qed.

Let json1 := {"menu" # {"header" # $"SVG Viewer",
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

Let tree1 := json_tree json1.
Let json11 := tree_json tree1.

Example test1 : Some json1 = json11.
Proof. auto. Qed.

Let row1 := jtree_nodes tree1.
Let table10 := jtable_fill (length row1) None.
Let table1 := jtree_table tree1.
Let tree11 := jtable_tree row1 (snd table1).

Example test2 : Some tree1 = tree11.
Proof. auto. Qed.

Fixpoint find' (k: key + nat) (l: list (nat*option (key + nat))) : option nat :=
match l with
| [] => None
| (n,k')::ks => match k, k' with
          | inl a, Some (inl b) => if (string_dec a b) then Some n else (find' k ks)
          | inr a, Some (inr b) => if (eqb a b) then Some n else (find' k ks)
          | _, _ => find' k ks
          end
end.

Definition find k l := find' k (indexate l).

Eval compute in (find (inr 4) [None; None; Some (inl "foo"); Some (inr 4)]).
Eval compute in (find (inl "foo") [None; None; Some (inl "foo"); Some (inr 4)]).
Eval compute in (find (inr 14) [None; None; Some (inl "foo"); Some (inr 4)]).


Fixpoint path_pair' (n:nat) (lk: list (key + nat)) 
                     (jr: list indnode) (jtb: jtable) : option (nat + nat*nat) :=
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
                       | Some n => path_pair' n ks jr jtb
                       end
           end
end.


Definition tree_path_pair lk jt :=
let tb3 := jtree_table jt in
let (njr, tb) := tb3 in
let (_, jr) := njr in
path_pair' 0 lk jr tb.

Eval compute in (tree_path_pair [inr 2; inl "baz"; inl "x"]
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]))).
                    
Eval compute in  (nth_error (snd (jtree_table
                 (json_tree ('[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}])))) 8).

Check replace.

Check jtable_set.
(*jtable ->
       nat ->
       nat ->
       option
         (key + nat)*)

Check data.
Definition json_rename lk j (newv: data + key) :=
let tr := json_tree j in
let tb3 := jtree_table tr in
let (njr, tb) := tb3 in
let (_, jr) := njr in
let minds := tree_path_pair lk tr in
match minds, newv with
| None, _  => j
| Some (inl k), inl newv => let jr' := replace k (clear_node_index jr) (data_node newv) in
                  let mtr' := jtable_tree jr' tb in
                  match mtr' with
                  | None => j
                  | Some tr' => let mj' := tree_json  tr' in
                                match mj' with
                                | None => j
                                | Some j' => j'
                                end
                  end
| Some (inr (m, n)), inr newv => 
                  let tb' := jtable_set tb m n (Some (inl newv)) in
                  let mtr' := jtable_tree (clear_node_index jr) tb' in
                  match mtr' with
                  | None => j
                  | Some tr' => let mj' := tree_json  tr' in
                                match mj' with
                                | None => j
                                | Some j' => j'
                                end
                  end
| _, _ =>  j
end.


Example rename1: (json_rename [inr 2; inl "baz"; inl "x"]
                  '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}] (inr "y") = 
                   '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"y" # '[$"d"; $"f"]}}]).
Proof. auto. Qed.

Example rename2: (json_rename [inr 0; inl "foo"; inr 0]
                  '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}] (inl "Mike") = 
                   '[{"foo" # '[$"Mike"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]).
Proof. auto. Qed.


Let json2 := '[{"type" # $"person",
                "name" # '[{"given" # '[$"Andy"; $"Michael"], "family" # $"Watson"};
                            {"given" # '[$"Andrey"], "family" # $"Watsonov"}],
                "telecom" # '[{"system" # $"phone", "value" # $"1234"};
                              {"system" # $"phone", "value" # $"5678"};
                              {"system" # $"mail", "value" # $"andy@watson.me"};
                              {"system" # $"mail", "value" # $"andrey@mail.ru"}]};
                {"type" # $"person",
                "name" # '[{"given" # '[$"John"; $"Israel"], "family" # $"Koen"};
                            {"given" # '[$"Ivan"], "family" # $"Koinov"}],
                "telecom" # '[{"system" # $"phone", "value" # $"4321"};
                              {"system" # $"phone", "value" # $"8765"};
                              {"system" # $"mail", "value" # $"john@koen.me"}]}].
                              
Let json3 := '[{"given1" # $"Andy Michael", "family1" # $"Watson",
                "given2" # $"Andrey", "family2" #  $"Watsonov",
                "phone1" # $"1234", "phone2" # $"5678",
                "mail1" # $"andy@watson.me",
                "mail2" # $"andrey@mail.ru"};
                {"given1" # $"John Israel", "family1" # $"Koen",
                "given2" # $"Ivan", "family2" #  $"Koinov",
                "phone1" # $"4321", "phone2" # $"8765",
                "mail1" # $"john@koen.me"}].


(*
DO_SMTH BY_METHOD WITH_PARAM AT_PATH
json2 -> json3

REMOVE (by purge) "type" AT ".*" -- all rooted collection
-- {"name" # '[{"given" # '[$"Andy"; $"Michael"], "family" # $"Watson"};
               {"given" # '[$"Andrey"], "family" # $"Watsonov"}]}

DESTRUCT (by disjoin, indexate) AT ".*.name"  -- on lists
-- "name1" # {"given" # '[$"Andy"; $"Michael"], "family" # $"Watson"}
-- "name2" # {"given" # '[$"Andrey"], "family" # $"Watsonov"}

DESTRUCT (by renaming, indexate key???) AT ".*.name*" -- on maps
-- {"given1" # '[$"Andy"; $"Michael"], "family1" # $"Watson",
--  "given2" # '[$"Andrey"], "family2" # $"Watsonov"}

DESTRUCT (by concat, with delimiter " ") AT ".*.given*" -- on  lists
-- {"given1" # $"Andy Michael"], "family1" # $"Watson",
--  "given2" # $"Andrey", "family2" # $"Watsonov"}

-- {"telecom" # '[{"system" # $"phone", "value" # $"1234"};
--                {"system" # $"phone", "value" # $"5678"};
--                {"system" # $"mail", "value" # $"andy@watson.me"};
--                {"system" # $"mail", "value" # $"andrey@mail.ru"}]}

DESTRUCT (by disjoin, indexate) AT ".*.telecom" -- on lists
-- {"telecom1" # {"system" # $"phone", "value" # $"1234"},
--  "telecom2" # {"system" # $"phone", "value" # $"5678"},
--  "telecom3" # {"system" # $"mail", "value" # $"andy@watson.me"},
--  "telecom4" # {"system" # $"mail", "value" # $"andrey@mail.ru"}}

SET (by replace with map {@"system" # @"value"}) AT ".*.telecom*" -- on maps
-- {"telecom1" # {"phone" # $"1234"},
--  "telecom2" # {"phone" # $"5678"},
--  "telecom3" # {"mail"  # $"andy@watson.me"},
--  "telecom4" # {"mail"  # $"andrey@mail.ru"}}

DESTRUCT (by renaming, indexate key???) AT ".*.telecom*" -- on maps
-- {"phone1" # $"1234",
--  "phone2" # $"5678",
--  "mail1"  # $"andy@watson.me",
--  "mail2"  # $"andrey@mail.ru"}

*)

(*
json3 -> json2
-- {"phone1" # $"1234", "phone2" # $"5678",
--  "mail1" # $"andy@watson.me",
--  "mail2" # $"andrey@mail.ru"}

SET (by destruct_insert of values ".*.phone*") AT ".*.phones"
SET (by destruct_insert of values ".*.mail*") AT ".*.mails"
-- {"phones" # '[$"1234"; $"5678"],
--  "mails"  # '[$"andy@watson.me"; $"andrey@mail.ru"]}

SET (by replace with map {"system" # $"phone", "value" # @id}) AT ".*.phones.*"
SET (by replace with map {"system" # $"mail", "value" # @id}) AT ".*.mails.*"
-- {"phones" # '[{"system" # $"phone", "value" # $"1234"}; 
--               {"system" # $"phone", "value" # $"5678"}],
--  "mails"  # '[{"system" # $"mail", "value"$"andy@watson.me"}; 
--               {"system" # $"mail", "value"$"andrey@mail.ru"}]}

SET (by destruct_insert of values [".*.mails", ".*.phones"]) AT ".*.telecom"
-- {"telecom" # '['[{"system" # $"phone", "value" # $"1234"}; 
--               {"system" # $"phone", "value" # $"5678"}];
--              '[{"system" # $"mail", "value"$"andy@watson.me"}; 
--               {"system" # $"mail", "value"$"andrey@mail.ru"}]]}

SET (by replace with map flatten) AT ".*.telecom"
-- {"telecom" # '[{"system" # $"phone", "value" # $"1234"}; 
--               {"system" # $"phone", "value" # $"5678"};
--               {"system" # $"mail", "value"$"andy@watson.me"}; 
--               {"system" # $"mail", "value"$"andrey@mail.ru"}]}
*)










