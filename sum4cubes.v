From Sum4Cubes Require Import Basics Extra.

From Stdlib Require Import Unicode.Utf8 Lia ZArith List.
Import ListNotations.

Open Scope Z_scope.

Theorem SumOf4Cubes_sig n : {p : (Z * Z * Z * Z) | n = (el p 1)^3 + (el p 2)^3 + (el p 3)^3 + (el p 4)^3}.
Proof.
  canalx n 6 H x.
  2,3,5,6 : canalx x 3 H3 y;
    rewrite H3 in H; ring_simplify in H; clear H3 x.
  (* 1. n = 6*x *)
  - found (x+1,x-1,-x,-x).
  (* 2. n = 18*y + 1 *)
  - found (2*y+14,-2*y-23,-3*y-26,3*y+30).
  (* 3. n = 18*y + 7 *)
  - found (y+2,6*y-1,8*y-2,-9*y+2).
  (* 4. n = 18*y + 13 = 9*(2*y + 1) + 4 *)
  - destruct (SumOf4Cubes_9k_plus_4_or n (2*y+1) ltac:(lia)) as [s | _];
      [exact s | admit].
  (* 5. n = 18*y + 2 *)
  - canalx y 3 H4 z; rewrite H4 in H; ring_simplify in H; clear H4 y.
    + found (29484*z^2 + 2211*z + 43,
             -29484*z^2 - 2157*z - 41,
             9828*z^2 + 485*z + 4,
             -9828*z^2 - 971*z - 22).
    + found (3*z - 11, -3*z + 10, z + 2, -z + 7).
    + canalx z 2 H5 w; rewrite H5 in H; ring_simplify in H; clear H5 z.
      * exact (SumOf4Cubes_108w_plus_38 n w ltac:(lia)).
      * canalx w 2 H6 v; rewrite H6 in H; ring_simplify in H; clear H6 w.
        -- found (3*v - 164, -3*v + 160, v - 35, -v + 71).
        -- found (14742*(v+1)^2 - 2157*(v+1) + 82,
                  -14742*(v+1)^2 + 2211*(v+1) - 86,
                  4914*(v+1)^2 - 971*(v+1) + 44,
                  -4914*(v+1)^2 + 485*(v+1) - 8).
  (* 6. n = 18*y + 8 *)
  - found (y-5,-1*y+14,-3*y+29,3*y-30).
  (* 7. n = 18*y + 14 = -(9*(-2*y - 2) + 4) *)
  - apply neg_sum4cubes.
    destruct (SumOf4Cubes_9k_plus_4_or (-n) (-2*y-2) ltac:(lia)) as [s | _];
      [exact s | admit].
  (* 8. n = 18*y + 4 = 9*(2*y) + 4 *)
  - destruct (SumOf4Cubes_9k_plus_4_or n (2*y) ltac:(lia)) as [s | _];
      [exact s | admit].
  (* 9. n = 18*y + 10 *)
  - found (y+6,-1*y-15,-3*y-32,3*y+33).
  (* 10. n = 18*y + 16 = -(18*(-y - 1) + 2) *)
  - canalx y 3 H4 z; rewrite H4 in H; ring_simplify in H; clear H4 y.
    + canalx z 2 H5 w; rewrite H5 in H; ring_simplify in H; clear H5 z.
      * canalx w 2 H6 v; rewrite H6 in H; ring_simplify in H; clear H6 w.
        -- found (-(14742*(-v)^2 - 2157*(-v) + 82),
                  -(-14742*(-v)^2 + 2211*(-v) - 86),
                  -(4914*(-v)^2 - 971*(-v) + 44),
                  -(-4914*(-v)^2 + 485*(-v) - 8)).
        -- found (-(3*(-v-1) - 164),
                  -(-3*(-v-1) + 160),
                  -((-v-1) - 35),
                  -(-(-v-1) + 71)).
      * apply neg_sum4cubes.
        exact (SumOf4Cubes_108w_plus_38 (-n) (-w - 1) ltac:(lia)).
    + found (-(3*(-z-1) - 11),
             -(-3*(-z-1) + 10),
             -((-z-1) + 2),
             -(-(-z-1) + 7)).
    + found (-(29484*(-z-1)^2 + 2211*(-z-1) + 43),
             -(-29484*(-z-1)^2 - 2157*(-z-1) - 41),
             -(9828*(-z-1)^2 + 485*(-z-1) + 4),
             -(-9828*(-z-1)^2 - 971*(-z-1) - 22)).
  (* 11. n = 18*y + 5 = -(9*(-2*y - 1) + 4) *)
  - apply neg_sum4cubes.
    destruct (SumOf4Cubes_9k_plus_4_or (-n) (-2*y-1) ltac:(lia)) as [s | _];
      [exact s | admit].
  (* 12. n = 18*y + 11 *)
  - found ((y+1)-2,6*(y+1)+1,8*(y+1)+2,-9*(y+1)-2).
  (* 13. n = 18*y + 17 *)
  - found (2*(y+1)-14,-2*(y+1)+23,-3*(y+1)+26,3*(y+1)-30).
  (* 14. n = 6*x + 3 *)
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

