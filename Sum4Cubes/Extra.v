(* Most of these proofs are written by Gemini 4 Argon and some of it got corrected by Claude Sonnet 5.5 *)
From Stdlib Require Import Unicode.Utf8 Lia ZArith List.
Import ListNotations.

Open Scope Z_scope.

From Sum4Cubes Require Import Basics.

(* If -n is a sum of 4 cubes then so is n. *)
Lemma neg_sum4cubes n :
  {p : (Z * Z * Z * Z) | - n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3} ->
  {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  intros [[[[a b] c] d] Hp].
  cbn [el] in Hp.
  exists (-a, -b, -c, -d).
  cbn [el].
  assert (Hring : (-a)^3 + (-b)^3 + (-c)^3 + (-d)^3 = - (a^3 + b^3 + c^3 + d^3)) by ring.
  lia.
Defined.

(* `solve_mod w m r v p` carves out and constructively solves the infinite    *)
(* arithmetic progression `w mod m = r` (writing `w = m * v + r`) while       *)
(* leaving only ONE residual subgoal, which keeps `w mod m ≠ r` as a          *)
(* hypothesis so later steps can use it.                                      *)
Tactic Notation "solve_mod" constr(w) constr(m) constr(r) ident(v) uconstr(p) :=
  let Hm := fresh "Hm" in
  let Hne := fresh "Hne" in
  let Hv := fresh "Hv" in
  destruct (Z.eq_dec (w mod m) r) as [Hm | Hm];
  [ assert (m ≠ 0) as Hne by (intro; discriminate);
    destruct (Zmod_sig Hm Hne) as [v Hv];
    exists p; cbn [el];
    match goal with
    | Hn : ?a = _ |- ?a = _ =>
        rewrite Hv in Hn; rewrite Hn; ring
    end
  | idtac ].

(* solve_rng Hr k c p : Hr is a range hypothesis  lo <= k < hi.  If k = lo *)
(* (which must be c) use the cubes p, otherwise shrink the range by one.   *)
Ltac solve_rng Hr k c p :=
  let Hk := fresh "Hk" in
  destruct (Z_bound_dec _ _ _ Hr) as [Hk | Hk];
  [ assert (Hkc : k = c) by lia;
    subst k; found p
  | clear Hr; rename Hk into Hr ].

(* ------------------------------------------------------------------ *)
(* PART 1: n = 108*w + 38  (complete, no admit)                       *)
(*                                                                    *)
(* Lattice basis u, v, w and the Pell recurrence                      *)
(*   A_j + B_j*sqrt(3420) = (-3041 - 52*sqrt(3420))^(3j+1)            *)
(* with A_j = 18*qA_j + 1 and B_j = 6*qB_j + 2.                       *)
(* ------------------------------------------------------------------ *)

Definition demj_p (K A B : Z) : Z * Z * Z * Z :=
  (10 * K + 27 * A - 928 * B,
   -19 * K - 9 * A - 602 * B,
   -24 * K + 25 * A - 2937 * B,
   27 * K - 19 * A + 2746 * B).

Definition demj_T (A B : Z) : Z :=
  (27 * A - 928 * B)^3 + (-9 * A - 602 * B)^3 +
  (25 * A - 2937 * B)^3 + (-19 * A + 2746 * B)^3.

Lemma demj_cubic_id K A B :
  (el (demj_p K A B) 1)^3 + (el (demj_p K A B) 2)^3 +
  (el (demj_p K A B) 3)^3 + (el (demj_p K A B) 4)^3 =
  1494 * K * (A^2 - 3420 * B^2) + demj_T A B.
Proof.
  unfold demj_p, demj_T; cbn [el]; ring.
Qed.

Definition demj_T_quot (qA qB : Z) : Z :=
  8981280*qA^3 - 508548132*qA^2*qB - 168019164*qA^2
  + 9975933324*qA*qB^2 + 6594116868*qA*qB + 1089685080*qA
  - 67746719724*qB^3 - 67192501206*qB^2 - 22214330489*qB - 2448079590.

Lemma demj_T_quot_id qA qB :
  demj_T (18 * qA + 1) (6 * qB + 2) = 18 * demj_T_quot qA qB + 2.
Proof.
  unfold demj_T, demj_T_quot; ring.
Qed.

(* One step of the Pell recurrence, on the pair (qA, qB). *)
Definition pell_step (p : Z * Z) : Z * Z :=
  (-112488782561 * fst p - 2192810059440 * snd p - 737186063289,
   -5770552788 * fst p - 112488782561 * snd p - 37816847120).

Fixpoint pell83_quot (j : nat) : Z * Z :=
  match j with
  | O => (-169, -9)
  | S j' => pell_step (pell83_quot j')
  end.

(* The same recurrence reduced modulo 83. *)
Definition mod83_step (r : Z * Z) : Z * Z :=
  ((10 * fst r + 41 * snd r + 28) mod 83,
   (51 * fst r + 10 * snd r + 75) mod 83).

Fixpoint pell83_mod83 (j : nat) : Z * Z :=
  match j with
  | O => (80, 74)
  | S j' => mod83_step (pell83_mod83 j')
  end.

Definition pell_unit (p : Z * Z) : Prop :=
  (18 * fst p + 1)^2 - 3420 * (6 * snd p + 2)^2 = 1.

Lemma pell_unit_step p : pell_unit p -> pell_unit (pell_step p).
Proof.
  destruct p as [qA qB].
  unfold pell_unit, pell_step. cbn [fst snd].
  intro H.
  refine (eq_trans _ H).
  ring.
Qed.

Lemma pell83_quot_unit (j : nat) : pell_unit (pell83_quot j).
Proof.
  induction j as [| j IH].
  - unfold pell_unit. vm_compute. reflexivity.
  - change (pell_unit (pell_step (pell83_quot j))).
    apply pell_unit_step. exact IH.
Qed.

Definition pell_dec (q r : Z * Z) : Type :=
  prod {kA : Z | fst q = 83 * kA + fst r} {kB : Z | snd q = 83 * kB + snd r}.

Lemma pell_dec_step q r : pell_dec q r -> pell_dec (pell_step q) (mod83_step r).
Proof.
  destruct q as [qA qB]; destruct r as [rA rB].
  unfold pell_dec, pell_step, mod83_step. cbn [fst snd].
  intros [[kA HkA] [kB HkB]].
  pose proof (Z.div_mod (10 * rA + 41 * rB + 28) 83 ltac:(lia)) as H1.
  pose proof (Z.div_mod (51 * rA + 10 * rB + 75) 83 ltac:(lia)) as H2.
  split.
  - exists (-112488782561*kA - 2192810059440*kB - 1355286537*rA - 26419398307*rB - 8881759799
            + (10 * rA + 41 * rB + 28) / 83).
    lia.
  - exists (-5770552788*kA - 112488782561*kB - 69524733*rA - 1355286537*rB - 455624665
            + (51 * rA + 10 * rB + 75) / 83).
    lia.
Defined.

Lemma pell83_quot_dec (j : nat) : pell_dec (pell83_quot j) (pell83_mod83 j).
Proof.
  induction j as [| j IH].
  - unfold pell_dec. cbn [pell83_quot pell83_mod83 fst snd].
    split; [exists (-3) | exists (-1)]; lia.
  - change (pell_dec (pell_step (pell83_quot j)) (mod83_step (pell83_mod83 j))).
    apply pell_dec_step. exact IH.
Defined.

Definition demj_T_quot_mod83 (rA rB : Z) : Z :=
  16*rA^3 + 6*rA^2*rB + 60*rA^2 + 63*rA*rB^2 + 15*rA*rB + 75*rA
  + 13*rB^3 + 58*rB^2 + 82*rB + 15.

Definition demj_T_quot_diff83 (kA kB rA rB : Z) : Z :=
  61872037920*kA^3 - 3503388081348*kA^2*kB + 2236338720*kA^2*rA
  - 42209494956*kA^2*rB - 13945590612*kA^2 + 68724204669036*kA*kB^2
  - 84418989912*kA*kB*rA + 1656004931784*kA*kB*rB + 547311700044*kA*kB
  + 26943840*kA*rA^2 - 1017096264*kA*rA*rB - 336038328*kA*rA
  + 9975933324*kA*rB^2 + 6594116868*kA*rB + 1089685080*kA
  - 466707152178636*kB^3 + 828002465892*kB^2*rA - 16868933211276*kB^2*rB
  - 5576977600098*kB^2 - 508548132*kB*rA^2 + 19951866648*kB*rA*rB
  + 6594116868*kB*rA - 203240159172*kB*rB^2 - 134385002412*kB*rB
  - 22214330489*kB + 108208*rA^3 - 6127086*rA^2*rB - 2024328*rA^2
  + 120191967*rA*rB^2 + 79447191*rA*rB + 13128735*rA - 816225539*rB^3
  - 809548208*rB^2 - 267642537*rB - 29494935.

Lemma demj_T_quot_mod83_Cong kA kB rA rB :
  demj_T_quot (83 * kA + rA) (83 * kB + rB) =
  83 * demj_T_quot_diff83 kA kB rA rB + demj_T_quot_mod83 rA rB.
Proof.
  unfold demj_T_quot, demj_T_quot_diff83, demj_T_quot_mod83; ring.
Qed.

Definition check_pell83_rw (j : nat) (rw : Z) : Z :=
  (demj_T_quot_mod83 (fst (pell83_mod83 j)) (snd (pell83_mod83 j)) - (6 * rw + 2)) mod 83.

Lemma pell_lin_K (w v rw Tq D Tm Q : Z) :
  Tq = 83 * D + Tm -> w = 83 * v + rw -> Tm - (6 * rw + 2) = 83 * Q ->
  83 * (6 * v - (D + Q)) = 6 * w + 2 - Tq.
Proof.
  intros H1 H2 H3.
  assert (HT : Tm = 83 * Q + (6 * rw + 2)) by lia.
  rewrite H1, H2, HT. ring.
Qed.

Lemma pell_lin_fin (n w K Tq : Z) :
  n = 108 * w + 38 -> 83 * K = 6 * w + 2 - Tq ->
  n = 1494 * K * 1 + (18 * Tq + 2).
Proof.
  intros Hn HK.
  assert (E : 1494 * K * 1 = 18 * (83 * K)) by ring.
  rewrite Hn, E, HK. ring.
Qed.

Lemma pell83_solve_rw n w v rw (j : nat) :
  n = 108 * w + 38 ->
  w = 83 * v + rw ->
  check_pell83_rw j rw = 0 ->
  {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  intros Hn Hw Hchk.
  pose proof (pell83_quot_unit j) as Hunit.
  pose proof (pell83_quot_dec j) as Hdec.
  unfold check_pell83_rw in Hchk.
  revert Hunit Hdec Hchk.
  destruct (pell83_quot j) as [qA qB].
  destruct (pell83_mod83 j) as [rA rB].
  unfold pell_unit, pell_dec. cbn [fst snd].
  intros Hunit [[kA HkA] [kB HkB]] Hchk.
  pose proof (demj_T_quot_mod83_Cong kA kB rA rB) as Hc.
  rewrite <- HkA, <- HkB in Hc.
  assert (Hq0 := Z.div_mod (demj_T_quot_mod83 rA rB - (6 * rw + 2)) 83 ltac:(lia)).
  rewrite Hchk, Z.add_0_r in Hq0.
  assert (HK : {K : Z | 83 * K = 6 * w + 2 - demj_T_quot qA qB}).
  { exists (6 * v - (demj_T_quot_diff83 kA kB rA rB
                     + (demj_T_quot_mod83 rA rB - (6 * rw + 2)) / 83)).
    exact (pell_lin_K w v rw (demj_T_quot qA qB) (demj_T_quot_diff83 kA kB rA rB)
             (demj_T_quot_mod83 rA rB) ((demj_T_quot_mod83 rA rB - (6 * rw + 2)) / 83)
             Hc Hw Hq0). }
  destruct HK as [K HK].
  exists (demj_p K (18 * qA + 1) (6 * qB + 2)).
  rewrite demj_cubic_id, Hunit, demj_T_quot_id.
  exact (pell_lin_fin n w K (demj_T_quot qA qB) Hn HK).
Defined.

Lemma SumOf4Cubes_108w_plus_38 n w (H : n = 108 * w + 38) :
  {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  (* Fast closed-form progressions *)
  solve_mod w  5  0 v (3*v - 140, -3*v + 190, 5*v - 285, -5*v + 267).
  solve_mod w  5  1 v (-6*v + 13, -120*v + 91, 118*v - 89, 44*v - 37).
  solve_mod w  5  4 v (6*v + 262, -6*v - 257, 2*v + 63, -2*v - 108).
  solve_mod w  7  4 v (14*v + 555, -14*v - 546, 6*v + 211, -6*v - 260).
  solve_mod w  7  6 v (3*v + 1993, -3*v - 1979, v + 598, -v - 724).
  solve_mod w  8  4 v (3*v - 5, -3*v + 37, 4*v - 39, -4*v + 21).
  solve_mod w 11  1 v (22*v + 8206, -22*v - 8197, 6*v + 2176, -6*v - 2297).
  solve_mod w 11  8 v (v - 1531, -v + 1729, 3*v - 4904, -3*v + 4882).
  solve_mod w 11 10 v (11*v + 4115, -11*v - 4106, 3*v + 1060, -3*v - 1181).
  solve_mod w 13  5 v (18*v + 4, -36*v - 17, 30*v + 16, 24*v + 11).
  solve_mod w 13  9 v (3*v - 20453, -3*v + 20791, 13*v - 89372, -13*v + 89354).
  solve_mod w 13 10 v (2*v - 509, -2*v + 626, 6*v - 1712, -6*v + 1699).
  solve_mod w 15 12 v (9*v + 5764, -9*v - 5714, 5*v + 3107, -5*v - 3269).
  solve_mod w 16  6 v (3*v + 7, -3*v + 25, 4*v - 25, -4*v + 7).
  solve_mod w 20  3 v (6*v + 199, -6*v - 149, 5*v + 108, -5*v - 180).
  solve_mod w 21 10 v (7*v - 275, -7*v + 356, 9*v - 431, -9*v + 382).
  solve_mod w 23 12 v (6*v + 5365, -6*v - 5342, 2*v + 1680, -2*v - 1887).
  solve_mod w 23 22 v (828*v + 1333, -864*v - 1391, 426*v + 686, 6*v - 2).
  solve_mod w 24 16 v (9*v + 3685, -9*v - 3653, 4*v + 1549, -4*v - 1711).
  solve_mod w 25 13 v (3*v - 5, -3*v + 55, 5*v - 64, -5*v + 46).
  solve_mod w 25 17 v (-864*v - 1199, 900*v + 1249, -438*v - 608, 6*v - 4).
  solve_mod w 27 23 v (24*v + 25, 102*v + 79, -86*v - 67, -76*v - 59).
  solve_mod w 32 30 v (3*v + 16, -3*v + 16, 4*v - 17, -4*v - 1).
  solve_mod w 37 12 v (18*v + 7, -36*v - 11, 30*v + 5, 24*v + 13).
  solve_mod w 37 19 v (54*v + 97, -72*v - 137, 60*v + 119, -6*v - 29).
  solve_mod w 37 20 v (45*v + 28, 99*v + 76, -102*v - 77, -6*v - 13).
  solve_mod w 37 25 v (54*v + 508, -72*v - 665, 60*v + 547, -6*v - 88).
  solve_mod w 49 23 v (14*v + 92, -14*v - 83, 6*v + 10, -6*v - 59).
  solve_mod w 60  7 v (6*v + 85, -6*v - 35, 5*v + 11, -5*v - 83).
  solve_mod w 63 17 v (14*v + 73, -14*v - 64, 6*v + 1, -6*v - 50).
  solve_mod w 80 33 v (6*v + 73, -6*v - 23, 5*v, -5*v - 72).
  (* All residues modulo 83 *)
  canalx w 83 Hw v.
  - exact (pell83_solve_rw n w v _ 45%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 29%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 64%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 37%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 54%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 76%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 58%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 52%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 14%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 10%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 20%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 1%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 38%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 15%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 16%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 27%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 81%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 47%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 26%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 34%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 73%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 49%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 7%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 80%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 12%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 24%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 44%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 31%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 46%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 77%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 21%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 28%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 74%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 25%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 22%nat H Hw ltac:(vm_compute; reflexivity)).
  - (* rw = 35: 83 divides 108*w + 38, solved by a quadratic identity *)
    subst w.
    found (29484*v^2 + 25143*v + 5371,
           -29484*v^2 - 25089*v - 5348,
           9828*v^2 + 8129*v + 1682,
           -9828*v^2 - 8615*v - 1889).
  - exact (pell83_solve_rw n w v _ 63%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 66%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 33%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 69%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 62%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 36%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 5%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 72%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 3%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 65%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 53%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 39%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 48%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 8%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 32%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 75%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 67%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 6%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 40%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 68%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 57%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 56%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 79%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 42%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 61%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 51%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 55%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 11%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 17%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 35%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 13%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 78%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 23%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 70%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 4%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 9%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 41%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 43%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 18%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 71%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 19%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 60%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 30%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 59%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 2%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 0%nat H Hw ltac:(vm_compute; reflexivity)).
  - exact (pell83_solve_rw n w v _ 50%nat H Hw ltac:(vm_compute; reflexivity)).
Defined.

(* ------------------------------------------------------------------ *)
(* PART 2: n = 9*k + 4                                                *)
(* ------------------------------------------------------------------ *)

Definition P_cubic (m : Z) : Z := 3 * m^3 + 3 * m^2 + m.

Lemma Z_cube_mod9_decomp x :
  (x mod 3 = 0 /\ exists q k, x = 3 * q /\ x^3 = 9 * k) \/
  (x mod 3 = 1 /\ exists q k, x = 3 * q + 1 /\ x^3 = 9 * k + 1) \/
  (x mod 3 = 2 /\ exists q k, x = 3 * q + 2 /\ x^3 = 9 * k - 1).
Proof.
  assert (Hne : 3 ≠ 0) by lia.
  canal x 3 H; destruct (Zmod_sig H Hne) as [q Hq].
  - left. split; [exact H | exists q, (3 * q^3); split; [lia | subst; ring]].
  - right; left. split; [exact H | exists q, (3 * q^3 + 3 * q^2 + q); split; [lia | subst; ring]].
  - right; right. split; [exact H | exists q, (3 * q^3 + 6 * q^2 + 4 * q + 1); split; [lia | subst; ring]].
Qed.

Lemma Mod9_4_Bases_Mod3 a b c d k :
  9 * k + 4 = a^3 + b^3 + c^3 + d^3 ->
  a mod 3 = 1 /\ b mod 3 = 1 /\ c mod 3 = 1 /\ d mod 3 = 1.
Proof.
  intros H.
  destruct (Z_cube_mod9_decomp a) as [[Ma [qa [ka [Ea Ca]]]] | [[Ma [qa [ka [Ea Ca]]]] | [Ma [qa [ka [Ea Ca]]]]]];
  destruct (Z_cube_mod9_decomp b) as [[Mb [qb [kb [Eb Cb]]]] | [[Mb [qb [kb [Eb Cb]]]] | [Mb [qb [kb [Eb Cb]]]]]];
  destruct (Z_cube_mod9_decomp c) as [[Mc [qc [kc [Ec Cc]]]] | [[Mc [qc [kc [Ec Cc]]]] | [Mc [qc [kc [Ec Cc]]]]]];
  destruct (Z_cube_mod9_decomp d) as [[Md [qd [kd [Ed Cd]]]] | [[Md [qd [kd [Ed Cd]]]] | [Md [qd [kd [Ed Cd]]]]]];
  try lia.
Qed.

Theorem SumOf4Cubes_9k_plus_4_Equiv k :
  {p : (Z * Z * Z * Z) | 9 * k + 4 = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}
  <=>
  {m : (Z * Z * Z * Z) | k = P_cubic (el m 1) + P_cubic (el m 2) + P_cubic (el m 3) + P_cubic (el m 4)}.
Proof.
  split.
  - intros [[[[a b] c] d] Hp].
    cbn [el] in Hp.
    destruct (Mod9_4_Bases_Mod3 a b c d k Hp) as [Ha [Hb [Hc Hd]]].
    assert (Hne : 3 ≠ 0) by lia.
    destruct (Zmod_sig Ha Hne) as [m1 Hm1].
    destruct (Zmod_sig Hb Hne) as [m2 Hm2].
    destruct (Zmod_sig Hc Hne) as [m3 Hm3].
    destruct (Zmod_sig Hd Hne) as [m4 Hm4].
    subst a b c d.
    clear Ha Hb Hc Hd Hne.
    exists (m1, m2, m3, m4).
    cbn [el]; unfold P_cubic.
    assert (Hring :
      (3*m1 + 1)^3 + (3*m2 + 1)^3 + (3*m3 + 1)^3 + (3*m4 + 1)^3 =
      9 * ((3*m1^3 + 3*m1^2 + m1) + (3*m2^3 + 3*m2^2 + m2) +
           (3*m3^3 + 3*m3^2 + m3) + (3*m4^3 + 3*m4^2 + m4)) + 4) by ring.
    rewrite Hring in Hp.
    apply (proj1 (Z.mul_cancel_l _ _ 9 ltac:(discriminate))).
    apply (proj1 (Z.add_cancel_r _ _ 4)).
    exact Hp.
  - intros [[[[m1 m2] m3] m4] Hm].
    cbn [el] in Hm; unfold P_cubic in Hm.
    exists (3*m1 + 1, 3*m2 + 1, 3*m3 + 1, 3*m4 + 1).
    cbn [el]; subst k; ring.
Defined.

(* The infinite family k = P_cubic m - j, j = 0..3. *)
Lemma SumOf4Cubes_9k_plus_4_family n m j (Hj : 0 <= j <= 3) (H : n = 9 * (P_cubic m - j) + 4) :
  {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  unfold P_cubic in H.
  destruct (Z.eq_dec j 0) as [-> | N0].
  { found (1, 1, 1, 3*m + 1). }
  destruct (Z.eq_dec j 1) as [-> | N1].
  { found (1, 1, -2, 3*m + 1). }
  destruct (Z.eq_dec j 2) as [-> | N2].
  { found (1, -2, -2, 3*m + 1). }
  assert (j = 3) as -> by lia.
  found (-2, -2, -2, 3*m + 1).
Defined.

(* All k with -100 <= k <= 100, i.e. |n| <= 904. *)
Lemma SumOf4Cubes_9k_plus_4_window n k (H : n = 9 * k + 4) (Hr : -100 <= k < 101) :
  {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  solve_rng Hr k (-100) (4, 4, -8, -8).
  solve_rng Hr k (-99) (-5, -5, -5, -8).
  solve_rng Hr k (-98) (10, -11, 13, -14).
  solve_rng Hr k (-97) (-5, 10, 10, -14).
  solve_rng Hr k (-96) (4, 4, 7, -11).
  solve_rng Hr k (-95) (-2, -8, 10, -11).
  solve_rng Hr k (-94) (1, -8, 10, -11).
  solve_rng Hr k (-93) (-2, -2, 16, -17).
  solve_rng Hr k (-92) (1, -2, 16, -17).
  solve_rng Hr k (-91) (1, 1, 16, -17).
  solve_rng Hr k (-90) (-5, 7, -8, -8).
  solve_rng Hr k (-89) (-5, -5, 13, -14).
  solve_rng Hr k (-88) (-2, 13, 31, -32).
  solve_rng Hr k (-87) (4, -8, 10, -11).
  solve_rng Hr k (-86) (-2, -5, -5, -8).
  solve_rng Hr k (-85) (1, -5, -5, -8).
  solve_rng Hr k (-84) (-2, 10, 10, -14).
  solve_rng Hr k (-83) (1, 10, 10, -14).
  solve_rng Hr k (-82) (4, -14, -17, 19).
  solve_rng Hr k (-81) (43, -56, -59, 67).
  solve_rng Hr k (-80) (7, -8, 13, -14).
  solve_rng Hr k (-79) (10, 13, 16, -20).
  solve_rng Hr k (-78) (4, -5, -5, -8).
  solve_rng Hr k (-77) (-2, 7, -8, -8).
  solve_rng Hr k (-76) (1, 7, -8, -8).
  solve_rng Hr k (-75) (1, -5, 13, -14).
  solve_rng Hr k (-74) (10, 10, -11, -11).
  solve_rng Hr k (-73) (-2, -2, -5, -8).
  solve_rng Hr k (-72) (1, -2, -5, -8).
  solve_rng Hr k (-71) (1, 1, -5, -8).
  solve_rng Hr k (-70) (-14, -65, -65, 82).
  solve_rng Hr k (-69) (4, 7, -8, -8).
  solve_rng Hr k (-68) (4, -5, 13, -14).
  solve_rng Hr k (-67) (-5, 7, 16, -17).
  solve_rng Hr k (-66) (-5, -11, -11, 13).
  solve_rng Hr k (-65) (-2, 4, -5, -8).
  solve_rng Hr k (-64) (1, 4, -5, -8).
  solve_rng Hr k (-63) (-2, -2, 13, -14).
  solve_rng Hr k (-62) (1, -2, 13, -14).
  solve_rng Hr k (-61) (1, 1, 13, -14).
  solve_rng Hr k (-60) (-2, -2, -2, -8).
  solve_rng Hr k (-59) (1, -2, -2, -8).
  solve_rng Hr k (-58) (1, 1, -2, -8).
  solve_rng Hr k (-57) (1, 1, 1, -8).
  solve_rng Hr k (-56) (-5, -5, -5, -5).
  solve_rng Hr k (-55) (-2, 4, 13, -14).
  solve_rng Hr k (-54) (1, 4, 13, -14).
  solve_rng Hr k (-53) (-2, -11, -11, 13).
  solve_rng Hr k (-52) (1, -11, -11, 13).
  solve_rng Hr k (-51) (1, -2, 4, -8).
  solve_rng Hr k (-50) (1, 1, 4, -8).
  solve_rng Hr k (-49) (10, 10, 28, -29).
  solve_rng Hr k (-48) (-5, -32, -44, 49).
  solve_rng Hr k (-47) (4, 4, 13, -14).
  solve_rng Hr k (-46) (4, 7, 16, -17).
  solve_rng Hr k (-45) (4, -11, -11, 13).
  solve_rng Hr k (-44) (-2, 4, 4, -8).
  solve_rng Hr k (-43) (1, 4, 4, -8).
  solve_rng Hr k (-42) (1, -5, -5, -5).
  solve_rng Hr k (-41) (-5, 13, 28, -29).
  solve_rng Hr k (-40) (7, 22, 61, -62).
  solve_rng Hr k (-39) (-2, -2, 10, -11).
  solve_rng Hr k (-38) (1, -2, 10, -11).
  solve_rng Hr k (-37) (1, 1, 10, -11).
  solve_rng Hr k (-36) (4, 4, 4, -8).
  solve_rng Hr k (-35) (4, -5, -5, -5).
  solve_rng Hr k (-34) (-2, -5, 7, -8).
  solve_rng Hr k (-33) (1, -5, 7, -8).
  solve_rng Hr k (-32) (-5, -80, -119, 130).
  solve_rng Hr k (-31) (-2, 4, 10, -11).
  solve_rng Hr k (-30) (1, 4, 10, -11).
  solve_rng Hr k (-29) (1, -2, -5, -5).
  solve_rng Hr k (-28) (1, 1, -5, -5).
  solve_rng Hr k (-27) (1, 13, 28, -29).
  solve_rng Hr k (-26) (4, -5, 7, -8).
  solve_rng Hr k (-25) (-5, -14, -20, 22).
  solve_rng Hr k (-24) (-2, 7, 13, -14).
  solve_rng Hr k (-23) (1, 7, 13, -14).
  solve_rng Hr k (-22) (-2, 4, -5, -5).
  solve_rng Hr k (-21) (1, 4, -5, -5).
  solve_rng Hr k (-20) (1, -2, 7, -8).
  solve_rng Hr k (-19) (1, 1, 7, -8).
  solve_rng Hr k (-18) (-8, -8, -11, 13).
  solve_rng Hr k (-17) (-2, -2, -2, -5).
  solve_rng Hr k (-16) (1, -2, -2, -5).
  solve_rng Hr k (-15) (1, 1, -2, -5).
  solve_rng Hr k (-14) (1, 1, 1, -5).
  solve_rng Hr k (-13) (-2, 4, 7, -8).
  solve_rng Hr k (-12) (1, 4, 7, -8).
  solve_rng Hr k (-11) (1, -14, -20, 22).
  solve_rng Hr k (-10) (-14, -14, -29, 31).
  solve_rng Hr k (-9) (-2, -2, 4, -5).
  solve_rng Hr k (-8) (1, -2, 4, -5).
  solve_rng Hr k (-7) (1, 1, 4, -5).
  solve_rng Hr k (-6) (-29, -29, -41, 49).
  solve_rng Hr k (-5) (4, 4, 7, -8).
  solve_rng Hr k (-4) (-2, -2, -2, -2).
  solve_rng Hr k (-3) (1, -2, -2, -2).
  solve_rng Hr k (-2) (1, 1, -2, -2).
  solve_rng Hr k (-1) (1, 1, 1, -2).
  solve_rng Hr k 0 (1, 1, 1, 1).
  solve_rng Hr k 1 (1, 7, 10, -11).
  solve_rng Hr k 2 (1, -11, -14, 16).
  solve_rng Hr k 3 (31, -44, -44, 52).
  solve_rng Hr k 4 (-2, -2, -2, 4).
  solve_rng Hr k 5 (1, -2, -2, 4).
  solve_rng Hr k 6 (1, 1, -2, 4).
  solve_rng Hr k 7 (1, 1, 1, 4).
  solve_rng Hr k 8 (4, 7, 10, -11).
  solve_rng Hr k 9 (-2, -5, -5, 7).
  solve_rng Hr k 10 (1, -5, -5, 7).
  solve_rng Hr k 11 (-11, -11, -11, 16).
  solve_rng Hr k 12 (-2, -2, 4, 4).
  solve_rng Hr k 13 (1, -2, 4, 4).
  solve_rng Hr k 14 (1, 1, 4, 4).
  solve_rng Hr k 15 (7, 7, 13, -14).
  solve_rng Hr k 16 (1, -50, -56, 67).
  solve_rng Hr k 17 (4, -5, -5, 7).
  solve_rng Hr k 18 (-2, 7, 7, -8).
  solve_rng Hr k 19 (1, 7, 7, -8).
  solve_rng Hr k 20 (-2, 4, 4, 4).
  solve_rng Hr k 21 (1, 4, 4, 4).
  solve_rng Hr k 22 (-2, -2, -5, 7).
  solve_rng Hr k 23 (1, -2, -5, 7).
  solve_rng Hr k 24 (1, 1, -5, 7).
  solve_rng Hr k 25 (-5, -8, -11, 13).
  solve_rng Hr k 26 (4, 7, 7, -8).
  solve_rng Hr k 27 (4, 10, 16, -17).
  solve_rng Hr k 28 (4, 4, 4, 4).
  solve_rng Hr k 29 (7, -26, -53, 55).
  solve_rng Hr k 30 (-2, 4, -5, 7).
  solve_rng Hr k 31 (1, 4, -5, 7).
  solve_rng Hr k 32 (13, 19, 25, -29).
  solve_rng Hr k 33 (-11, -14, -26, 28).
  solve_rng Hr k 34 (-8, -17, -17, 22).
  solve_rng Hr k 35 (-2, -2, -2, 7).
  solve_rng Hr k 36 (1, -2, -2, 7).
  solve_rng Hr k 37 (1, 1, -2, 7).
  solve_rng Hr k 38 (1, 1, 1, 7).
  solve_rng Hr k 39 (1, -8, -11, 13).
  solve_rng Hr k 40 (1, -5, -8, 10).
  solve_rng Hr k 41 (22, 22, 28, -35).
  solve_rng Hr k 42 (-23, -35, -44, 52).
  solve_rng Hr k 43 (-2, -2, 4, 7).
  solve_rng Hr k 44 (1, -2, 4, 7).
  solve_rng Hr k 45 (1, 1, 4, 7).
  solve_rng Hr k 46 (4, -8, -11, 13).
  solve_rng Hr k 47 (4, -5, -8, 10).
  solve_rng Hr k 48 (-5, -5, 7, 7).
  solve_rng Hr k 49 (-2, 10, 13, -14).
  solve_rng Hr k 50 (1, 10, 13, -14).
  solve_rng Hr k 51 (-2, 4, 4, 7).
  solve_rng Hr k 52 (1, 4, 4, 7).
  solve_rng Hr k 53 (1, -2, -8, 10).
  solve_rng Hr k 54 (1, 1, -8, 10).
  solve_rng Hr k 55 (-26, -29, -38, 46).
  solve_rng Hr k 56 (10, 19, 49, -50).
  solve_rng Hr k 57 (4, 10, 13, -14).
  solve_rng Hr k 58 (7, 10, 16, -17).
  solve_rng Hr k 59 (4, 4, 4, 7).
  solve_rng Hr k 60 (-2, 4, -8, 10).
  solve_rng Hr k 61 (1, 4, -8, 10).
  solve_rng Hr k 62 (1, -5, 7, 7).
  solve_rng Hr k 63 (40, 91, 160, -170).
  solve_rng Hr k 64 (16, 40, 73, -77).
  solve_rng Hr k 65 (-5, -14, -23, 25).
  solve_rng Hr k 66 (-5, 58, 64, -77).
  solve_rng Hr k 67 (-2, -11, -17, 19).
  solve_rng Hr k 68 (4, 4, -8, 10).
  solve_rng Hr k 69 (4, -5, 7, 7).
  solve_rng Hr k 70 (19, 19, 31, -35).
  solve_rng Hr k 71 (-5, 28, 40, -44).
  solve_rng Hr k 72 (7, -26, -32, 37).
  solve_rng Hr k 73 (-2, 10, 10, -11).
  solve_rng Hr k 74 (1, 10, 10, -11).
  solve_rng Hr k 75 (1, -2, 7, 7).
  solve_rng Hr k 76 (1, 1, 7, 7).
  solve_rng Hr k 77 (7, -8, -11, 13).
  solve_rng Hr k 78 (-5, 7, -8, 10).
  solve_rng Hr k 79 (-5, -8, -14, 16).
  solve_rng Hr k 80 (7, 22, 58, -59).
  solve_rng Hr k 81 (-2, -5, -11, 13).
  solve_rng Hr k 82 (1, -5, -11, 13).
  solve_rng Hr k 83 (1, 4, 7, 7).
  solve_rng Hr k 84 (10, 13, 28, -29).
  solve_rng Hr k 85 (1, 28, 40, -44).
  solve_rng Hr k 86 (4, -14, -23, 25).
  solve_rng Hr k 87 (13, 19, 52, -53).
  solve_rng Hr k 88 (7, 10, 13, -14).
  solve_rng Hr k 89 (4, -5, -11, 13).
  solve_rng Hr k 90 (4, 4, 7, 7).
  solve_rng Hr k 91 (-2, 7, -8, 10).
  solve_rng Hr k 92 (1, 7, -8, 10).
  solve_rng Hr k 93 (1, -8, -14, 16).
  solve_rng Hr k 94 (-2, -2, -11, 13).
  solve_rng Hr k 95 (1, -2, -11, 13).
  solve_rng Hr k 96 (1, 1, -11, 13).
  solve_rng Hr k 97 (1, 1, -5, 10).
  solve_rng Hr k 98 (4, -17, -17, 22).
  solve_rng Hr k 99 (4, 7, -8, 10).
  solve_rng Hr k 100 (-5, 7, 7, 7).
  exfalso; lia.
Defined.

(* Either the window solves it, or k is outside the window. *)
Lemma SumOf4Cubes_9k_plus_4_or n k (H : n = 9 * k + 4) :
  {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}
  + {k < -100 \/ 100 < k}.
Proof.
  destruct (-100 <=? k) eqn:E1; [destruct (k <=? 100) eqn:E2 |].
  - left.
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    exact (SumOf4Cubes_9k_plus_4_window n k H ltac:(split; lia)).
  - right. apply Z.leb_gt in E2. lia.
  - right. apply Z.leb_gt in E1. lia.
Defined.

