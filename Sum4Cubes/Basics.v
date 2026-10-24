From Stdlib Require Import Unicode.Utf8 Lia ZArith List.
Import ListNotations.

Open Scope Z_scope.

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

Lemma Z_bound_dec_inv n k : 0 <= n < k -> sum (n = k-1) (0 <= n < k-1).
Proof.
  intros.
  destruct (Z.eq_dec n (k-1)).
  - left. exact e.
  - right. lia.
Defined.

Lemma Z_bound_dec n k1 k2 : k1 <= n < k2 -> sum (n = k1) (k1+1 <= n < k2).
Proof.
  intros.
  destruct (Z.eq_dec n k1).
  - left. exact e.
  - right. lia.
Defined.

Lemma Zmod_sig {n a b} (h : n mod a = b) (hz : a ≠ 0) : {x | n = a*x+b}.
Proof.
  exists (n/a). rewrite <- h.
  exact (Z.div_mod n a hz).
Defined.

Ltac canal' k H H2:= 
  let y := eval compute in (0 <? k) in 
  tryif (constr_eq_strict true y) then
    destruct (Z_bound_dec _ _ _ H2) as [H|H];
    simpl in H; clear H2; [| rename H into H2; canal' (k-1) H H2]
  else lia.

(* Inspired by ThEdu24 *)
(* Thanks to Boldo, Clément, Hamelin, Mayero, Rousselin *)
(* canal is an abbreviation for CAse ANalysis! *)
Ltac canal n k H :=
  let H2 := ident:(__H2) in
  unshelve epose proof (Z.mod_pos_bound n k _) as H2; [lia |];
  canal' (k) H H2.

Ltac canalx n k H x := 
  assert (k ≠ 0) as Hne by easy;
  canal n k H;
  destruct (Zmod_sig H Hne) as [x Hx]; clear Hne H; rename Hx into H.

Ltac found p := exists p; simpl head el; subst; ring.

