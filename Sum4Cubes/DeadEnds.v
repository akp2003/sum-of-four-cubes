From Stdlib Require Import Unicode.Utf8 Lia ZArith List.
Import ListNotations.

Open Scope Z_scope.

Definition eval_poly (l : list Z) (x : Z) : Z :=
  fold_right (fun a acc => a + x * acc) 0 l.

Compute eval_poly [1; 2; 3] 2.  (* 1 + 2*2 + 3*4 = 17 *)

Lemma eval_poly_deg1 (l : list Z) :
  (length l < 3)%nat ->
  exists e d : Z, forall x : Z, eval_poly l x = e + d * x.
Proof.
  intros Hlen.
  destruct l as [| e [| d [| c l']]].
  - exists 0, 0. intros x. simpl. ring.
  - exists e, 0. intros x. simpl. ring.
  - exists e, d. intros x. simpl. ring.
  - simpl in Hlen. lia.
Qed.

Lemma mod3_cases (a : Z) :
  exists q : Z, a = 3 * q \/ a = 3 * q + 1 \/ a = 3 * q + 2.
Proof.
  exists (a / 3).
  pose proof (Z.div_mod a 3) as Hdiv.
  pose proof (Z.mod_pos_bound a 3) as Hmod.
  lia.
Qed.

Lemma cube_mod9 (a : Z) :
  exists k s : Z,
    a ^ 3 = 9 * k + s /\ -1 <= s <= 1 /\ (s = 1 -> exists q : Z, a = 3 * q + 1).
Proof.
  destruct (mod3_cases a) as [q [Ha | [Ha | Ha]]]; subst a.
  - exists (3 * q ^ 3), 0.
    split; [ring | split; [lia | intros H; discriminate]].
  - exists (3 * q ^ 3 + 3 * q ^ 2 + q), 1.
    split; [ring | split; [lia | intros _; exists q; reflexivity]].
  - exists (3 * q ^ 3 + 6 * q ^ 2 + 4 * q + 1), (-1).
    split; [ring | split; [lia | intros H; discriminate]].
Qed.

Lemma sum4cubes_mod9 (a1 a2 a3 a4 m : Z) :
  a1 ^ 3 + a2 ^ 3 + a3 ^ 3 + a4 ^ 3 = 9 * m + 4 ->
  (exists q1 : Z, a1 = 3 * q1 + 1) /\
  (exists q2 : Z, a2 = 3 * q2 + 1) /\
  (exists q3 : Z, a3 = 3 * q3 + 1) /\
  (exists q4 : Z, a4 = 3 * q4 + 1).
Proof.
  intros Hsum.
  destruct (cube_mod9 a1) as [k1 [s1 [H1 [Hb1 Hi1]]]].
  destruct (cube_mod9 a2) as [k2 [s2 [H2 [Hb2 Hi2]]]].
  destruct (cube_mod9 a3) as [k3 [s3 [H3 [Hb3 Hi3]]]].
  destruct (cube_mod9 a4) as [k4 [s4 [H4 [Hb4 Hi4]]]].
  rewrite H1, H2, H3, H4 in Hsum.
  assert (Hs : s1 = 1 /\ s2 = 1 /\ s3 = 1 /\ s4 = 1) by lia.
  destruct Hs as [Hs1 [Hs2 [Hs3 Hs4]]].
  repeat split; auto.
Qed.

Lemma linear_comb_div_486 (e d : Z) :
  (exists q : Z, e + d * 0 = 3 * q + 1) ->
  (exists p : Z, e + d * 1 = 3 * p + 1) ->
  exists m : Z,
    -4 * (e + d * 2) ^ 3 + 21 * (e + d * 1) ^ 3
    - 12 * (e + d * 0) ^ 3 - 5 * (e + d * (-1)) ^ 3 = 486 * m.
Proof.
  intros [q Hq] [p Hp].
  assert (He : e = 3 * q + 1) by lia.
  assert (Hd : d = 3 * (p - q)) by lia.
  destruct (mod3_cases (p - q)) as [k [Hk | [Hk | Hk]]];
    rewrite Hk in Hd; subst e d.
  - exists (-9 * k ^ 3 + 9 * k * q ^ 2 + 6 * k * q + k). ring.
  - exists (-9 * k ^ 3 - 9 * k ^ 2 + 9 * k * q ^ 2 + 6 * k * q - 2 * k + 3 * q ^ 2 + 2 * q). ring.
  - exists (-9 * k ^ 3 - 18 * k ^ 2 + 9 * k * q ^ 2 + 6 * k * q - 11 * k + 6 * q ^ 2 + 4 * q - 2). ring.
Qed.

Lemma rearrange_4x4
  (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 f1 f2 f3 f4
   sa sb sc sf m1 m2 m3 m4 : Z) :
  a1 + a2 + a3 + a4 = sa ->
  b1 + b2 + b3 + b4 = sb ->
  c1 + c2 + c3 + c4 = sc ->
  f1 + f2 + f3 + f4 = sf ->
  -4 * a1 + 21 * b1 - 12 * c1 - 5 * f1 = 486 * m1 ->
  -4 * a2 + 21 * b2 - 12 * c2 - 5 * f2 = 486 * m2 ->
  -4 * a3 + 21 * b3 - 12 * c3 - 5 * f3 = 486 * m3 ->
  -4 * a4 + 21 * b4 - 12 * c4 - 5 * f4 = 486 * m4 ->
  (m1 + m2 + m3 + m4) * 486 = -4 * sa + 21 * sb - 12 * sc - 5 * sf.
Proof.
  intros Ha Hb Hc Hf Hm1 Hm2 Hm3 Hm4.
  transitivity
    ((-4 * a1 + 21 * b1 - 12 * c1 - 5 * f1) +
     (-4 * a2 + 21 * b2 - 12 * c2 - 5 * f2) +
     (-4 * a3 + 21 * b3 - 12 * c3 - 5 * f3) +
     (-4 * a4 + 21 * b4 - 12 * c4 - 5 * f4)).
  - rewrite Hm1, Hm2, Hm3, Hm4. ring.
  - rewrite <- Ha, <- Hb, <- Hc, <- Hf. ring.
Qed.

Lemma no_linear_sum_of_4_cubes (e1 d1 e2 d2 e3 d3 e4 d4 : Z) :
  (forall x : Z,
    (e1 + d1 * x) ^ 3 + (e2 + d2 * x) ^ 3 +
    (e3 + d3 * x) ^ 3 + (e4 + d4 * x) ^ 3 = 9 * x + 4) ->
  False.
Proof.
  intros H.
  pose proof (H 0) as H0.
  pose proof (H 1) as H1.
  pose proof (H (-1)) as Hm1.
  pose proof (H 2) as H2.
  destruct (sum4cubes_mod9 _ _ _ _ 0 H0) as [Hq1 [Hq2 [Hq3 Hq4]]].
  destruct (sum4cubes_mod9 _ _ _ _ 1 H1) as [Hp1 [Hp2 [Hp3 Hp4]]].
  destruct (linear_comb_div_486 e1 d1 Hq1 Hp1) as [m1 Hm_1].
  destruct (linear_comb_div_486 e2 d2 Hq2 Hp2) as [m2 Hm_2].
  destruct (linear_comb_div_486 e3 d3 Hq3 Hp3) as [m3 Hm_3].
  destruct (linear_comb_div_486 e4 d4 Hq4 Hp4) as [m4 Hm_4].
  pose proof (rearrange_4x4
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ m1 m2 m3 m4
    H2 H1 H0 Hm1 Hm_1 Hm_2 Hm_3 Hm_4) as Hcomb.
  apply (f_equal (fun z => z mod 486)) in Hcomb.
  rewrite Z_mod_mult in Hcomb.
  discriminate Hcomb.
Qed.

(* Gemini 4 Argon wrote the formal proof based on the paper of SCHINZEL 1968 *)
Theorem not_SumOf4Cubes_9x_plus_4_degree_1 : 
  not (∃(l1 l2 l3 l4 : list Z), (length l1 < 3)%nat ∧ (length l2 < 3)%nat ∧ (length l3 < 3)%nat ∧ (length l4 < 3)%nat 
∧ (∀x, (eval_poly l1 x)^3 + (eval_poly l2 x)^3 + (eval_poly l3 x)^3 + (eval_poly l4 x)^3 = 9*x+4)).
Proof.
  intros [l1 [l2 [l3 [l4 [Hl1 [Hl2 [Hl3 [Hl4 H]]]]]]]].
  destruct (eval_poly_deg1 l1 Hl1) as [e1 [d1 He1]].
  destruct (eval_poly_deg1 l2 Hl2) as [e2 [d2 He2]].
  destruct (eval_poly_deg1 l3 Hl3) as [e3 [d3 He3]].
  destruct (eval_poly_deg1 l4 Hl4) as [e4 [d4 He4]].
  apply (no_linear_sum_of_4_cubes e1 d1 e2 d2 e3 d3 e4 d4).
  intros x.
  pose proof (H x) as Hx.
  rewrite He1, He2, He3, He4 in Hx.
  exact Hx.
Qed.

Print Assumptions not_SumOf4Cubes_9x_plus_4_degree_1.

(* To check that the logic is sort of correct *)

Theorem SumOf4Cubes_6x : 
   (∃(l1 l2 l3 l4 : list Z), (length l1 < 3)%nat ∧ (length l2 < 3)%nat ∧ (length l3 < 3)%nat ∧ (length l4 < 3)%nat 
∧ (∀x, (eval_poly l1 x)^3 + (eval_poly l2 x)^3 + (eval_poly l3 x)^3 + (eval_poly l4 x)^3 = 6*x)).
Proof.
  exists [1; 1].
  exists [-1; 1].
  exists [0; -1].
  exists [0; -1].
  constructor. 1:{ simpl. lia. }
  constructor. 1:{ simpl. lia. }
  constructor. 1:{ simpl. lia. }
  constructor. 1:{ simpl. lia. }
  intros. unfold eval_poly,fold_right. ring.  
Qed.


(* My next goal ... *)

Theorem not_SumOf4Cubes_9x_plus_4_degree_6 : 
  not (∃(l1 l2 l3 l4 : list Z), (length l1 < 7)%nat ∧ (length l2 < 7)%nat ∧ (length l3 < 7)%nat ∧ (length l4 < 7)%nat 
∧ (∀x, (eval_poly l1 x)^3 + (eval_poly l2 x)^3 + (eval_poly l3 x)^3 + (eval_poly l4 x)^3 = 9*x+4)).
Proof.
Admitted.

Theorem not_SumOf4Cubes_9x_plus_4_degree_8 : 
  not (∃(l1 l2 l3 l4 : list Z), (length l1 < 9)%nat ∧ (length l2 < 9)%nat ∧ (length l3 < 9)%nat ∧ (length l4 < 9)%nat 
∧ (∀x, (eval_poly l1 x)^3 + (eval_poly l2 x)^3 + (eval_poly l3 x)^3 + (eval_poly l4 x)^3 = 9*x+4)).
Proof.
Admitted.

