Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.

Require Export CommonHelpers.

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

Definition indexNat (n: nat):  string :=
  "#" ++ (writeNat n).

Fixpoint split_string' (s: string) (p: string) n : list string :=
match n with
| O => []
| S n' => 
if (string_dec s "") then [] else
if (string_dec p "") then (substring 0 1 s)::
                          (split_string' (substring 1 ((String.length s) - 1) s) p n') else
let i := index 0 p s in
match i with
| None => [s]
| Some k => let ss := substring 0 k s in
            let a  := k + (String.length p) in
            let s' := substring a ((String.length s) - a) s in
            ss::(split_string' s' p n')
end
end.

Definition split_string s p := split_string' s p (String.length s). 


Eval compute in (split_string "a.b.c.*" ".").
Eval compute in (split_string "aaaa." ".").
Eval compute in (split_string "." ".").
Eval compute in (split_string "aaaa" "").
Eval compute in (split_string ".aaa.a.e." ".").

Fixpoint concat_with (p: string) (ls: list string) : string :=
match ls with
| [] => ""
| [s]  => s
| s::ls' => s++p++(concat_with p ls')
end.


Require Import String Ascii.
Definition num_of_ascii (c: ascii) : option nat :=
 match c with
(* Zero is 0011 0000 *)
   | Ascii false false false false true true false false => Some 0
(* One is 0011 0001 *)
   | Ascii true false false false true true false false => Some 1
(* Two is 0011 0010 *)
   | Ascii false true false false true true false false => Some 2
   | Ascii true true false false true true false false => Some 3
   | Ascii false false true false true true false false => Some 4
   | Ascii true false true false true true false false => Some 5
   | Ascii false true true false true true false false => Some 6
   | Ascii true true true false true true false false => Some 7
   | Ascii false false false true true true false false => Some 8
   | Ascii true false false true true true false false => Some 9
   | _ => None
end.

Fixpoint string_rev (s : string) : string :=
 match s with
 | EmptyString => EmptyString
 | String c rest => append (string_rev rest) (String c EmptyString)
end.

Fixpoint num_of_string_rec (s : string) : option nat :=
  match s with
    | EmptyString => Some 0
    | String c rest => 
       match (num_of_ascii c), (num_of_string_rec rest) with
          | Some n, Some m => Some (n + 10 * m)
          | _ , _ => None
       end
   end.

Definition num_of_string (s : string) := 
  num_of_string_rec (string_rev s).

Eval compute in num_of_string "1".
Eval compute in num_of_string "10".
Eval compute in num_of_string "174".

Definition remove_prefix (p s: string) : string :=
if (prefix p s) then substring (String.length p) ((String.length s) - (String.length p)) s
else s.

Eval compute in (remove_prefix "ddd" "dddpol").
Eval compute in (remove_prefix "" "dddpol").
Eval compute in (remove_prefix "dddr" "dddpol").

Fixpoint substrings (s: string): list string :=
match s with
| EmptyString => [EmptyString]
| String c s' => s::(substrings s')
end.

Eval compute in (substrings "abc").

Eval compute in (match "*" with
                 | String c s => Some c
                 | _ => None
                 end).

Fixpoint match_string (p s: string): bool :=
match p, s with
| EmptyString, EmptyString => true
| String ("*"%char) xp, EmptyString => match_string xp EmptyString
| String ("*"%char) xp, String cs xs => bany (map (match_string xp) (substrings s))
| String cp xp, String cs xs => if (string_dec (String cp EmptyString)
                                               (String cs EmptyString)) then 
                                match_string xp xs else false
| _, _ => false
end.

Check concat.
SearchAbout (ascii -> string).

Eval compute in ("s" ++ (String "034"%char EmptyString)).


Eval compute in (match_string "abc" "abc").
Eval compute in (match_string "abcd" "abc").
Eval compute in (match_string "abc" "abcd").
Eval compute in (match_string "abc*" "abc").
Eval compute in (match_string "abc*ijh" "abcdefijh").
Eval compute in (match_string "abc*ijh*" "abcdefijh").
Eval compute in (match_string "abc*" "abcdefijh").
Eval compute in (match_string "*" "abcdefijh").
Eval compute in (match_string "" "abcdefijh").
Eval compute in (match_string "a" "abcdefijh").

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




