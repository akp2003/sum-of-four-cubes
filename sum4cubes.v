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

Theorem SumOf4Cubes_sig n : {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  canalx n 6 H x.
  2,3,5,6 : canalx x 3 H3 y;
    rewrite H3 in H; ring_simplify in H; clear H3 x.
  Ltac found p := exists p; simpl head el; lia.
  - found (x+1,x-1,-x,-x).
  - found (2*y+14,-2*y-23,-3*y-26,3*y+30).
  - found (y+2,6*y-1,8*y-2,-9*y+2).
  - admit.
  - admit.
  - found (y-5,-1*y+14,-3*y+29,3*y-30).
  - admit.
  - admit.
  - found (y+6,-1*y-15,-3*y-32,3*y+33).
  - admit.
  - admit.
  - found ((y+1)-2,6*(y+1)+1,8*(y+1)+2,-9*(y+1)-2).
  - found (2*(y+1)-14,-2*(y+1)+23,-3*(y+1)+26,3*(y+1)-30).
  - found (x,-x+4,2*x-5,-2*x+4).
Admitted.


Theorem SumOf4Cubes n : ∃a b c d, n = a^3 + b^3 + c^3 + d^3.
Proof.
  pose proof (SumOf4Cubes_sig n).
  destruct H. exists (el x 1).
  exists (el x 2). exists (el x 3).
  exists (el x 4).
  exact e.
Qed.

