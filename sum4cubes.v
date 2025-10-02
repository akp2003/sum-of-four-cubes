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

Lemma Z_bound_dec n k : 0 <= n < k -> sum (n = k-1) (0 <= n < k-1).
Proof.
  intros.
  destruct (Z.eq_dec n (k-1)).
  - left. exact e.
  - right. lia.
Defined.

Lemma Zmod_sig {n a b} (h : n mod a = b) (hz : a ≠ 0) : {x | n = a*x+b}.
Proof.
  exists (n/a). rewrite <- h.
  exact (Z.div_mod n a hz).
Defined.

Ltac canal' k H H2 Hne x := 
  let y := eval compute in (0 <? k) in 
  tryif (constr_eq_strict true y) then
    destruct (Z_bound_dec _ _ H2) as [H3|H];
    clear H2; [simpl in H3; destruct (Zmod_sig H3 Hne) as [x H]; clear H3 | simpl in H; rename H into H2; canal' (k-1) H H2 Hne x]
  else lia.

(* Inspired by ThEdu24 *)
(* Thanks to Boldo, Clément, Hamelin, Mayero, Rousselin *)
(* canal is an abbreviation for CAse ANalysis! *)
Ltac canal n k H x :=
  assert (k ≠ 0) as __Hne; [lia |];
  let H2 := ident:(__H2) in
  unshelve epose proof (Z.mod_pos_bound n k _) as H2; [lia |];
  canal' (k) H H2 __Hne x;
  clear __Hne.

Theorem SumOf4Cubes_sig n : {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  canal n 6 H x.
  - canal x 3 H2 y.
    all : rewrite H2 in H; ring_simplify in H; clear H2 x.
    + admit. 
    + admit.
    + admit.
  - canal x 3 H2 y.
    all : rewrite H2 in H; ring_simplify in H; clear H2 x.
    + admit. 
    + admit.
    + admit.
  - exists (x,-x+4,2*x-5,-2*x+4).
    simpl head el. lia.
  - canal x 3 H2 y.
    all : rewrite H2 in H; ring_simplify in H; clear H2 x.
    + admit. 
    + admit.
    + admit.
  - canal x 3 H2 y.
    all : rewrite H2 in H; ring_simplify in H; clear H2 x.
    + admit. 
    + admit.
    + exists (2*y+14,-2*y-23,-3*y-26,3*y+30).
      simpl head el. lia.
  - exists (x+1,x-1,-x,-x).
    simpl head el. lia. 
Admitted.


Theorem SumOf4Cubes n : ∃a b c d, n = a^3 + b^3 + c^3 + d^3.
Proof.
  pose proof (SumOf4Cubes_sig n).
  destruct H. exists (el x 1).
  exists (el x 2). exists (el x 3).
  exists (el x 4).
  exact e.
Qed.

