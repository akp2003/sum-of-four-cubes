From Stdlib Require Import Unicode.Utf8 Lia ZArith List.
Import ListNotations.

Open Scope Z_scope.

(* I copied these from ThEdu24 *)
(* Thanks to Boldo, Clément, Hamelin, Mayero, Rousselin *)

Fixpoint range_pos (a b : Z) (n: nat) (acc: list Z) {struct n} : list Z :=
  match n with
  | O => a :: acc
  | S n' => range_pos a (b-1) n' (cons b acc)
  end.

Fixpoint range_neg (a b : Z) (n: nat) (acc: list Z) {struct n} : list Z :=
  match n with
  | O => b :: acc
  | S n' => range_neg (a+1) b n' (cons a acc)
  end.

Definition range (a b : Z) : list Z :=
  if a <=? b
  then range_pos a b (Z.to_nat (b-a)) nil
  else range_neg b a (Z.to_nat (a-b)) nil.

Infix "<=>" := (fun A B => prod (forall _ : A, B) (forall _ : B, A)) (at level 70, no associativity).

Local Notation "( x | y )" := {z | y = z*x} (at level 0).

Definition el (p : Z * Z * Z * Z) (n : Z) := 
  match p with
  (x, y, z, w) => 
    match n with
    | 1 => x
    | 2 => y
    | 3 => z
    | 4 => w
    | _ => -1
    end
  end.

(* canal is an abbreviation for CAse ANalysis! *)
Ltac canal x a H :=
  specialize (in_dec Z.eq_dec (x mod a) (range 0 (a-1))) as H;
  remember x as __x' in H;
  destruct H as [H|H];
  [ unfold In in H; simpl in H; subst __x' | simpl in H; subst __x'; pose proof Z.mod_pos_bound x a; lia ].

Theorem SumOf4Cubes_sig n : {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  canal n 6 H.
  
Admitted.


Theorem SumOf4Cubes n : ∃a b c d, n = a^3 + b^3 + c^3 + d^3.
Proof.
  pose proof (SumOf4Cubes_sig n).
  destruct H. exists (el x 1).
  exists (el x 2). exists (el x 3).
  exists (el x 4).
  exact e.
Qed.

