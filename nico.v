(*
  Sanjay Adhith
  <sanjay.adhith@u.nus.edu>
  Coimbatore, India
  15 December 2024
*)

(*
  "Historians consider Nicomachus a Neopythagorean based on his
  tendency to view numbers as having mystical properties rather than
  their mathematical properties."
*)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Nat Arith Bool.
    
(* *** *)

(* Properties of Sigma. *)

Fixpoint Sigma (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O =>
    f 0
  | S n' =>
    Sigma n' f + f n
  end.

Lemma fold_unfold_Sigma_O :
  forall (f : nat -> nat),
    Sigma 0 f =
      f 0.
Proof.
  fold_unfold_tactic Sigma.
Qed.

Lemma fold_unfold_Sigma_S :
  forall (n' : nat)
         (f : nat -> nat),
    Sigma (S n') f =
    Sigma n' f + f (S n').
Proof.
  fold_unfold_tactic Sigma.
Qed.

(* *** *)

(* Testing theorems *)

Compute (Sigma 9 (fun i => i * i * i) =
        (Sigma 9 (fun i => i)) *
        (Sigma 9 (fun i => i))).
(* 2025 = 2025 *)
Compute (Sigma 10 (fun i => i * i * i) =
        (Sigma 10 (fun i => i)) *
        (Sigma 10 (fun i => i))).
(* 3025 = 3025 *)
Compute (Sigma 11 (fun i => i * i * i) =
        (Sigma 11 (fun i => i)) *
        (Sigma 11 (fun i => i))).
(* 4365 = 4365 *)
Compute (Sigma 12 (fun i => i * i * i) =
        (Sigma 12 (fun i => i)) *
        (Sigma 12 (fun i => i))).
(* 6084 = 6084 *)

Lemma high_school:
  forall a b : nat,
    (a + b) * (a + b) =
    a*a + 2*a*b + b*b.

Proof.
  intros a b.
  ring.
Qed.

Lemma gauss:
  forall n : nat,
    2 * (Sigma n (fun i => i)) =
      n * (S n).

Proof.
  intros n.
  induction n as [ | n' IHn'].

  * rewrite -> fold_unfold_Sigma_O.
    rewrite -> Nat.mul_0_r.
    rewrite -> Nat.mul_0_l.
    reflexivity.

  * rewrite -> fold_unfold_Sigma_S.
    Search (_ * (_ + _)).
    rewrite -> Nat.mul_add_distr_l.
    rewrite -> IHn'.
    ring.
Qed.
    
Theorem nicomachus:
  forall n : nat,
    Sigma n (fun i => i * i * i) =
      (Sigma n (fun i => i)) *
      (Sigma n (fun i => i)).
Proof.
  intros n.
  induction n as [ | n' IHn'].

  * rewrite ->2 fold_unfold_Sigma_O.
    rewrite ->2 Nat.mul_0_r.
    reflexivity.

  * rewrite -> 2 fold_unfold_Sigma_S.
    rewrite -> high_school.
    rewrite -> IHn'.
    rewrite -> gauss.
    ring.
Qed.
