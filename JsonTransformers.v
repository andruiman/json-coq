Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.

Require Export Json.
Require Export JsonTree.
Require Export JsonTable.

Import ListNotations.
Import JsonNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope json_scope.

Definition path_tree (ls: list string) root jt : list jpath :=
let mt := tree_getin root jt in 
match mt with 
| None => []
| Some jt => let jts := fold_right (fun s jts => let mts := map (tree_wild_get (from_string s)) jts in
                                    let ts := flatten mts in
                                    ts) [([],jt)] ls in
                        map (fun p => app root (fst p)) jts
end.

Definition path_parse (s: string) (root: jpath) jt : list jpath :=
let ls := split_string s "." in
path_tree (rev ls) root jt.

Definition do_at_nodes (j: json) (f: jpath -> json -> json) (path: string) : json :=
let jt := json_tree j in
let llk := path_parse path [] jt in
fold_right f j llk. 

Fixpoint replicate {X} n (x:X): list X :=
match n with
| O => []
| S n' => x::(replicate n' x)
end.

Definition json_rename (newv: JsonData + key) (lk: jpath) (j: json) :=
let tr := json_tree j in
let (jr, tb) := jtree_table tr in
let minds := tree_path_ind lk tr in
match minds, newv with
| None, _  => j
| Some (inl k), inl newv => 
                  let jr' := replace k (clear_node_index jr) (data_node newv) in
                  table_json_default jr' tb j
| Some (inr (m,n)), inl newv => let jr' := replace n (clear_node_index jr) (data_node newv) in
                                let tb' := replace n tb (replicate (length jr) None) in
                                table_json_default jr' tb' j
| Some (inl k), inr newv =>  let tb' := fold_right (fun m tb => let x := mnth_error tb m k in
                                                                if x then jtable_set tb m k (Some (inl newv))
                                                                     else tb) tb (seq 0 (length jr)) in
                             table_json_default (clear_node_index jr) tb' j
| Some (inr (m, n)), inr newv => 
                  let tb' := jtable_set tb m n (Some (inl newv)) in
                  table_json_default (clear_node_index jr) tb' j 
end.


Definition json_rename_if (f: jtree -> bool) (newv: JsonData + key) (lk: jpath) (j: json) :=
let tr := json_tree j in
let mtr' := tree_getin lk tr in
match mtr' with
| None => j
| Some tr' => if (f tr') then json_rename newv lk j else j
end.

Definition json_rename_with (f: jpath -> jtree -> jtree -> JsonData + key) (lk: jpath) (j: json) :=
let tr := json_tree j in
let mtr' := tree_getin lk tr in
match mtr' with
| None => j
| Some tr' => json_rename (f lk tr tr') lk j
end.

Definition json_rename_with_if (b: jtree -> bool) (f: jpath -> jtree -> jtree -> JsonData + key) (lk: jpath) (j: json) :=
let tr := json_tree j in
let mtr' := tree_getin lk tr in
match mtr' with
| None => j
| Some tr' => if (b tr') then json_rename (f lk tr tr') lk j else j
end.

Inductive DestructStrategy := DestructStrategy0.

Inductive IndMergeStrategy := 
| IndRightMergeToNumber : IndMergeStrategy
| IndRightMergeToKey : (key -> key) -> IndMergeStrategy.

Fixpoint merge_inds (ilt ilf: list (option jpoint)) 
                    (s:IndMergeStrategy) (b: bool):=
match ilt, ilf with
| [], ilf' => ilf'
| ilt', [] => ilt'
| None::ilt', (Some x)::ilf' => let l := merge_inds ilt' ilf' s b in
                         match x, s with
                         | inl kx, IndRightMergeToNumber => (Some (inr 0))::l
                         | inr ix, IndRightMergeToNumber => (Some x)::l
                         | inl kx, IndRightMergeToKey f => (Some (inl (f kx)))::l
                         | inr ix, IndRightMergeToKey f => (Some (inl (f (writeNat ix))))::l
                         end
| x::ilt', None::ilf' => x::(merge_inds ilt' ilf' s b)
(*shouldn't happen*)
| (Some x)::ilt',(Some y)::ilf' => 
                            let z:= match x,y with
                                    | inl kx, inl ky => inl (kx ++ "." ++ ky)
                                    | inl kx, inr iy => inl (kx ++ "." ++ (indexNat iy))
                                    | inr ix, inl ky => inr ix (*FIXME:will be ignored, but...*)
                                    | inr ix, inr iy => inr ix (*FIXME:will be ignored, but...*)
                                    end in
                            if b then (Some x)::(merge_inds ilt' ilf' s b)
                                 else (Some z)::(merge_inds ilt' ilf' s b)
end.


Definition json_destruct (lk: jpath) (j: json): json :=
let tr := json_tree j in
let (jr, tb) := jtree_table tr in
let minds := tree_path_ind lk tr in
match minds with
| None => j
| Some (inl k) => let tb' := fold_right (fun m tb => jtable_set tb m k None) 
                                          tb (seq 0 (length jr)) in
                  table_json_default (clear_node_index jr) tb' j 

| Some (inr (m, n)) => let milt := nth_error tb m in
                       let milf := nth_error tb n in
                       let mtr := tree_getin (removelast lk) tr in
                       let last := last lk (inl "") in
                       let slast := match last with
                                    | inr k => writeNat k
                                    | inl k => k
                                    end in
                       match milt, milf, mtr with
                           | None, _, _ => j
                           | _, None, _ => j
                           | _, _, None => j
                           | _, _, Some (tleaf _) => j
                           | Some ilt, Some ilf, Some (tlbranch _)  => 
                                       let ilt' := merge_inds ilt ilf IndRightMergeToNumber true in
                                       let tb' := replace m tb ilt' in
                                       let tb'' := jtable_set tb' m n None in
                                       table_json_default (clear_node_index jr) tb'' j
                           | Some ilt, Some ilf, Some (tmbranch _)  => 
                                       let ilt' := merge_inds ilt ilf (IndRightMergeToKey (fun k => (append (append slast "-") k))) true in
                                       let tb' := replace m tb ilt' in
                                       let tb'' := jtable_set tb' m n None in
                                       table_json_default (clear_node_index jr) tb'' j
                       end
end.

Definition json_remove (lk: jpath) (j: json): json :=
let tr := json_tree j in
let (jr, tb) := jtree_table tr in
let minds := tree_path_ind lk tr in
match minds with
| None => j
| Some (inl k) => let tb' := fold_right (fun m tb => jtable_set tb m k None) 
                                          tb (seq 0 (length jr)) in
                  table_json_default (clear_node_index jr) tb' j 

| Some (inr (m, n)) => let tb' := jtable_set tb m n None in
                       table_json_default (clear_node_index jr) tb' j
                           
end.

Definition json_modify (f: jtree -> jtree) (lk: jpath) (j: json) : json :=
let tr := json_tree j in
let tr' := tree_modify lk tr f in
let mj' := tree_json tr' in
match mj' with
| None => j
| Some j' => j'
end.

Definition json_merge (lkfrom lkto: jpath) (j: json) : json :=
let tr := json_tree j in
let tr' := tree_submerge lkto lkfrom tr MergeStrategy0 in
let mj' := tree_json tr' in
match mj' with
| None => j
| Some j' => j'
end.

Eval compute in (json_merge [inl "b"] [inl "a"]  {"a" # '[], "b" # $"foo"}).

Definition json_merge_with (f: jpath -> jpath) (lkto: jpath) (j: json) : json :=
json_merge (f lkto) lkto j.


(*CREATE AT "*.telecom"*)
Definition json_create (s: string) (lk: jpath) (j: json) : json :=
let jt := json_tree j in
let p := from_string s in
let mjt' := tree_getin lk jt in
let jt' := match mjt' with 
| None => jt
| Some jt' => let mjt'' := tree_get p jt' in
              let pth := app lk [p] in
              match mjt'' with
              | Some _ => jt
              | None => match p with
                        | inr k => tree_mergein lk jt (tlbranch [(k, tlbranch [])]) MergeStrategy0
                        | inl k => tree_mergein lk jt (tmbranch [(k, tlbranch [])]) MergeStrategy0
                        end
              end
end in
(*let jt' := fold_right (fun p (pjt: jpath*jtree) => let (pth, jt) := pjt in
                                    let pth' := app pth [p] in
                                    let mjt' := tree_getin pth' jt in
                                    match mjt' with
                                    | Some _ => (pth', jt)
                                    | None => match p with
                                              | inr k => (pth', tree_mergein pth jt (tlbranch [(k, tlbranch [])]) MergeStrategy0)
                                              | inl k => (pth', tree_mergein pth jt (tmbranch [(k, tlbranch [])]) MergeStrategy0)
                                              end
                                    end) ([], jt) lk in*)
let mj' := tree_json jt' in
match mj' with
| None => j
| Some j' => j'
end.


(* COLLECT "telecom*" TO "telecom" AT "*" *)
Definition json_collect (what pto: string) f (root: jpath) (j: json) : json :=
let jt := json_tree j in
let llkf := path_parse what root jt in
let llkt := path_parse pto root jt in
let jt' := fold_left (fun jt lkf => 
                        fold_right (fun lkt jt => tree_submerge_with lkt lkf f jt MergeStrategy0) jt llkt) llkf jt in
let mj' := tree_json jt' in
match mj' with
| None => j
| Some j' => j'
end.

Definition json_zip_at (ks: list string) (root: jpath) (j: json) :=
let jt := json_tree j in
let llkf := flatten (map (fun s => path_parse s root jt) ks) in
let trees := filterSome (map (fun p => tree_getin p jt) llkf) in 
let jt' := tree_setin root jt (tlbranch (indexate (fold_left ziptrees' trees []))) in
let mj' := tree_json jt' in
match mj' with
| None => j
| Some j' => j'
end.

Fixpoint jtree_filter_key (f: key -> bool) (t: key-> key) (jt: jtree) : jtree :=
match jt with
| tleaf _ => jt
| tlbranch tl => let tl' := map (fun kt => jtree_filter_key f t (snd kt)) tl in
                 let tl'' := filter (fun t => match t with
                                               | tlbranch [] | tmbranch [] => false
                                               | _ => true
                                              end) tl' in
                 tlbranch (indexate tl'')
| tmbranch tm => let tm' := map (fun kt => (fst  kt, jtree_filter_key f t (snd kt))) tm in
                 let tm'' := filter (fun kt => f (fst kt)) tm' in
                 let tm''' := filter (fun kt => match (snd kt) with
                                                | tlbranch [] | tmbranch [] => false
                                                | _ => true
                                                end) tm'' in
                 let tm'''' := map (fun kt => (t (fst kt), snd kt)) tm''' in
                 tmbranch tm''''
end.

Eval compute in (jtree_filter_key (fun k => eqKey k "foo") (@id key) (tmbranch [("foo", tleaf "bar")])). 

Definition json_extract (p: key) (j: json) : json  :=
let jt := json_tree j in
let jt' := jtree_filter_key (prefix p) (remove_prefix p) jt in
let mj' := tree_json jt' in
match mj' with
| None => j
| Some j' => j'
end.

Definition tolkpath (ss: list string) : jpath :=
map (fun s =>
     let mn := num_of_string s in
     match mn with
     | None => inl s
     | Some n => inr n
     end) ss.

Fixpoint jtree_collect_all (p: key) (jt: jtree) : jtree :=
match jt with
| tleaf _ => jt
| tlbranch tl => tlbranch (map (fun kt => (fst kt, jtree_collect_all p (snd kt))) tl)
| tmbranch tm => fold_left (fun acctree kt => 
                            let ks := split_string (fst kt) p in
                            match ks with
                            | [] => tree_force_mergein [inl (fst kt)] acctree (jtree_collect_all p (snd kt)) MergeStrategy0
                            | [k'] => tree_force_mergein [inl (fst kt)] acctree (jtree_collect_all p (snd kt)) MergeStrategy0
                            | pth => tree_force_mergein (tolkpath pth) acctree (jtree_collect_all p (snd kt)) MergeStrategy0
                            end) tm (tmbranch [])
end.


Definition json_collect_all (p: key) (lk: jpath) (j: json) : json :=
let jt := json_tree j in
let m := tree_getin lk jt in
match m with
| None => j
| Some jt' => let jt'' := jtree_collect_all p jt' in
              let jt''' := tree_setin lk jt jt'' in 
              let mj' := tree_json jt''' in
match mj' with
| None => j
| Some j' => j'
end
end.

Check last.


Definition json_copy (lkto: jpath) (lkfrom: jpath) (j: json) : json :=
let jt := json_tree j in
let mjtf := tree_getin lkfrom jt in
let jt' := match mjtf with
| Some jtf => let sl := last lkfrom (inr 0) in
              let jtf' := match sl with
                          | inr k => tlbranch [(k, jtf)]
                          | inl k => tmbranch [(k, jtf)]
                          end in
              let nt := tree_mergein lkto jt jtf' MergeStrategy0 in
              nt
| None => jt
end in
let mj' := tree_json jt' in
match mj' with
| None => j
| Some j' => j'
end.

Definition json_move (lkto: jpath) (lkfrom: jpath) (j: json) : json :=
let j' := json_copy lkto lkfrom j in
json_remove lkfrom j'.

Definition json_movefrom_with (f: jpath -> jpath) (lkfrom: jpath) (j: json) : json :=
json_move (f lkfrom) lkfrom j.

Definition json_moveto_with (f: jpath -> jpath) (lkto: jpath) (j: json) : json :=
json_move lkto (f lkto) j.

Eval compute in (json_move [inl "a"] [inl "b"] {"a" # {"r" # $"v"}, "b" # $"foo"}).


(*tests*)

Example rename1: (json_rename (inr "y") [inr 2; inl "baz"; inl "x"]
                  '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]    = 
                   '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"y" # '[$"d"; $"f"]}}]).
Proof. auto. Qed.

Example rename2: (json_rename (inl "Mike") [inr 0; inl "foo"; inr 0]
                  '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}] = 
                   '[{"foo" # '[$"Mike"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}]).
Proof. auto. Qed.

Example rename3: json_rename (inr "y") [inr 1; inl "bar"]
                  '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"bar" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}] = 
                    '[{"foo" # '[$"Andy"; $"Peter"]}; 
                    {"y" # $"Good"};
                    {"baz" # {"x" # '[$"d"; $"f"]}}].
Proof. auto. Qed.

Let json2 := '[{"type" # $"person",
                "name" # '[{"given" # '[$"Andy"; $"Michael"], "family" # $"Watson"};
                            {"given" # '[$"Andrey"], "family" # $"Watsonov"}],
                "telecom" # '[{"system" # $"phone", "value" # $"1234"};
                              {"system" # $"phone", "value" # $"5678"};
                              {"system" # $"mail", "value" # $"andy@watson.me"};
                              {"system" # $"mail", "value" # $"andrey@mail.ru"}]
                 };
                {"type" # $"person",
                "name" # '[{"given" # '[$"John"; $"Israel"], "family" # $"Koen"};
                            {"given" # '[$"Ivan"], "family" # $"Koinov"}],
                "telecom" # '[{"system" # $"phone", "value" # $"4321"};
                              {"system" # $"phone", "value" # $"8765"};
                              {"system" # $"mail", "value" # $"john@koen.me"}]
                }].

Let json3 := '[{"given1" # $"Andy Michael", "family1" # $"Watson",
                "given2" # $"Andrey", "family2" #  $"Watsonov",
                "phone1" # $"1234", "phone2" # $"5678",
                "mail1" # $"andy@watson.me",
                "mail2" # $"andrey@mail.ru"};
                {"given1" # $"John Israel", "family1" # $"Koen",
                "given2" # $"Ivan", "family2" #  $"Koinov",
                "phone1" # $"4321", "phone2" # $"8765",
                "mail1" # $"john@koen.me"}].

Let tree2 := json_tree json2.
Let tb22 := jtree_table tree2.
Let tab2 := snd tb22.



Eval compute in (path_parse "*.name" [] tree2).

Let json21' := do_at_nodes json2 json_destruct "*.name".
Eval compute in json21'.
Eval compute in (json_getin [inr 0; inl "name-0"] json21').
Eval compute in (json_getin [inr 0; inl "name-1"] json21').
Let json22' := do_at_nodes json21' json_destruct "*.name*".
Eval compute in json22'.
Let json23' := do_at_nodes json22' (json_modify (concat_tree_with " ")) "*.name*given".
Eval compute in json23'.
Let json24' := do_at_nodes json23' json_destruct "*.telecom".
Eval compute in json24'.
Let json25' := do_at_nodes json24' (json_modify (fun t => let mt1 := tree_getin [inl "system"] t in
                                                             let mt2 := tree_getin [inl "value"] t in
                                                             match mt1, mt2 with
                                                             | Some (tleaf s1), Some (tleaf s2) => 
                                                                    (tmbranch [(s1, tleaf s2)])
                                                             | _, _ => t
                                                             end))  "*.telecom*".
Eval compute in json25'.
Let json26' := do_at_nodes json25' json_destruct "*.telecom*".
Eval compute in json26'.
Let json27' := do_at_nodes json26' (json_rename (inr "given1")) "*.name-0-given".
Eval compute in json27'.

Let json28' := do_at_nodes json27' (json_rename (inr "given2")) "*.name-1-given".
Let json29' := do_at_nodes json28' (json_rename (inr "family1")) "*.name-0-family".
Let json210' := do_at_nodes json29' (json_rename (inr "family2")) "*.name-1-family".
Let json211' := do_at_nodes json210' (json_rename (inr "phone1")) "*.telecom-0-phone".
Let json212' := do_at_nodes json211' (json_rename (inr "phone2")) "*.telecom-1-phone".
Let json213' := do_at_nodes json212' (json_rename (inr "mail1")) "*.telecom-2-mail".
Let json214' := do_at_nodes json213' (json_rename (inr "mail2")) "*.telecom-3-mail".
Let json215' := do_at_nodes json214' json_destruct "*.type".

Example mapping1 : json3 = json215'.
Proof. compute. auto. Qed.

Let json31' := do_at_nodes json3 (json_create "type") "*".
Let json32' := do_at_nodes json31' (json_modify (fun _ => tleaf "person")) "*.type".
Eval compute in json32'.

Let json33' := do_at_nodes json32' (json_rename (inr "name-0-given")) "*.given1".
Let json34' := do_at_nodes json33' (json_rename (inr "name-1-given")) "*.given2".
Let json35' := do_at_nodes json34' (json_rename (inr "name-0-family")) "*.family1".
Let json36' := do_at_nodes json35' (json_rename (inr "name-1-family")) "*.family2".
Let json37' := do_at_nodes json36' (json_rename (inr "telecom-0-phone")) "*.phone1".
Let json38' := do_at_nodes json37' (json_rename (inr "telecom-1-phone")) "*.phone2".
Let json39' := do_at_nodes json38' (json_rename (inr "telecom-2-mail")) "*.mail1".
Let json310' := do_at_nodes json39' (json_rename (inr "telecom-3-mail")) "*.mail2".

Let json311' := do_at_nodes json310' (json_modify (split_tree_with " ")) "*.name*given".
Eval compute in json311'.
Let json312' := do_at_nodes json311' (json_create "'name-given") "*".
Let json313' := do_at_nodes json312' (json_collect "name*given" "'name-given" (fun lk jt => tlbranch [(0, jt)])) "*".
Eval compute in json313'.
Let json314' := do_at_nodes json313' (json_create "'name-family") "*".
Let json315' := do_at_nodes json314' (json_collect "name*family" "'name-family" (fun lk jt => tlbranch [(0, jt)])) "*".
Eval compute in json315'.
Let json316' := do_at_nodes json315' json_remove "*.name*".
Eval compute in json316'.
Let json317' := do_at_nodes json316' (json_create "name") "*".
Let json318' := do_at_nodes json317' (json_collect "'name*" "name" (fun lk jt => let l := last lk (inl "error") in
                                                                                 let sl := writeJPoint l in
                                                                                 let sl' := split_string sl "-" in
                                                                                 let sl'' := nth 1 sl' "error" in
                                                                    tmbranch [(sl'', jt)])) "*".
Eval compute in json318'.
Let json319' := do_at_nodes json318' json_remove "*.'name*".
Eval compute in json311'.
Let json320' := do_at_nodes json319' (json_zip_at ["given"; "family"]) "*.name".
Eval compute in json320'.
Let json321' := do_at_nodes json320' (json_modify (map_tree_with ["given"; "family"])) "*.name".
Eval compute in json321'.

Let json322' := do_at_nodes json321' (json_create "'telecom") "*".
Let json323' := do_at_nodes json322' (json_collect "telecom*" "'telecom" (fun lk jt => let l := last lk (inl "error") in
                                                                                      let sl := writeJPoint l in
                                                                                      let sl' := split_string sl "-" in
                                                                                      let sl'' := last sl' "error" in
                                                                        tlbranch [(0, tmbranch [("system", tleaf sl''); 
                                                                                  ("value", jt)])])) "*".
Eval compute in json323'.
Let json324' := do_at_nodes json323' json_remove "*.telecom*".
Eval compute in json324'.
Let json325' := do_at_nodes json324' (json_rename (inr "telecom")) "*.'telecom".
Eval compute in json325'.

Example mapping2 : json2 = 
                   json325'.
Proof. compute. auto. Qed.
