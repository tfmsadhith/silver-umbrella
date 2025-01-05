(*
  Sanjay Adhith
  tfmsadhith@gmail.com

  This .v file contains
  a formalisation of
  Dijkstra's EWD857.

  https://www.cs.utexas.edu/~EWD/ewd08xx/EWD857.PDF
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

Lemma about_Sigma_with_two_equivalent_functions :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        f i = g i) ->
    Sigma x f = Sigma x g.

Proof.
  intros x f g i.
  induction x as [ | x' IHx'].

  * rewrite ->2 fold_unfold_Sigma_O.
    rewrite -> i.
    reflexivity.

  * rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> i.
    rewrite -> IHx'.
    reflexivity.
Qed.    

Lemma about_factoring_a_multiplicative_constant_on_the_right_in_Sigma :
  forall (x c : nat)
         (f : nat -> nat),
    Sigma x (fun i => f i * c) = Sigma x f * c.

Proof.
  intros x c f.
  revert c.

  induction x as [ | x' IHx'].

  * intros c.
    rewrite ->2 fold_unfold_Sigma_O.
    reflexivity.

  * intros c.
    rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> IHx'.
    Search ((_ + _) * _ = _ * _ + _ *_).
    rewrite -> (Nat.mul_add_distr_r).
    reflexivity.
Qed.

Lemma about_factoring_a_multiplicative_constant_on_the_left_in_Sigma :
  forall (x c : nat)
         (f : nat -> nat),
    Sigma x (fun i => c * f i) = c * Sigma x f.

Proof.
  intros x c f.
  revert c.

  induction x as [ | x' IHx'].

  * intros c.
    rewrite ->2 fold_unfold_Sigma_O.
    reflexivity.

  * intros c.
    rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> IHx'.
    rewrite -> (Nat.mul_add_distr_l).
    reflexivity.
Qed.

(* *** *)

(* Assistants *)

Lemma twice :
  forall x : nat,
    x + x = 2 * x.
Proof.
  intro x.
  ring.
Qed.

(* *** *)

(*
  Begin by proving the theorem
  Dijkstra illustrated geometrically.
 *)

Lemma kolmogorov_squares:
  forall n : nat,
    Sigma n (fun i : nat => S (2*i)) = (S n) * (S n).
Proof.
  intros n.
  induction n as [ | n'].

  * rewrite -> fold_unfold_Sigma_O.
    simpl.
    reflexivity.

  * rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHn'.
    ring.
Qed.

(*
  Dijkstra then generalises this formula
  to cubes.

  "By mentally cutting 3 mutually
   orthogonal slices of thickness
   1 from a cube of n by n by n,
   one can convince oneself that...

 *)

Lemma dijkstra_pow_3:
  forall n : nat,
    Sigma n (fun i : nat => (S i)*(S i) + i*(S i) + i*i)
    = (S n) * (S n) * (S n).
Proof.
  intros n.
  induction n as [ | n'].

  * rewrite -> fold_unfold_Sigma_O.
    simpl.
    reflexivity.

  * rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHn'.
    ring.
Qed.

(*
  "and one begins to suspect
   the validity of..."
 *)

Lemma dijkstra_pow_4:
  forall n : nat,
    Sigma n (fun i : nat => (S i)*(S i)*(S i) + (S i)*(S i)*i + (S i)*i*i + i*i*i) = (S n)*(S n)*(S n)*(S n).
Proof.
  intros n.
  induction n as [ | n'].

  * rewrite -> fold_unfold_Sigma_O.
    simpl.
    reflexivity.

  * rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHn'.
    ring.
Qed.


(* 0 *)
Lemma dijkstra_pow_k:
  forall n k : nat,
      (Sigma n
           (fun i =>
              (Sigma k
                 (fun j =>
                    (S i)^(k - j) * i^j))))

     = (S n)^(S k).
Proof.
  intros n.
  induction n as [ | n']; intros k.

  * rewrite -> fold_unfold_Sigma_O.
    rewrite -> Nat.pow_1_l.
    induction k as [ | k'].

    ** simpl.
       reflexivity.

    ** rewrite -> fold_unfold_Sigma_S.
       rewrite -> Nat.mul_0_r.
       rewrite -> Nat.add_0_r.
       assert (H_eq:
                forall i : nat, 1 ^ (S k' - i) * 0 ^ i =
                                1 ^ (k' - i) * 0 ^ i).
       {
         intros i.
         rewrite ->2 Nat.pow_1_l.
         reflexivity.
       }
       rewrite -> (about_Sigma_with_two_equivalent_functions
                k'
                (fun j : nat => 1 ^ (S k' - j) * 0 ^ j)
                (fun j : nat => 1 ^ (k' - j) * 0 ^ j)
                H_eq
             ).
       rewrite -> IHk'.
       reflexivity.
       
  * rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHn'.
    (* 1 *)
    induction k as [ | k'].

    ** rewrite -> fold_unfold_Sigma_O.
       simpl.
       ring.

    ** rewrite -> fold_unfold_Sigma_S.
       Search (_ - _ = _).
       rewrite -> Nat.sub_diag.
       rewrite -> Nat.pow_0_r.
       rewrite -> Nat.mul_1_l.
       Search (S _ - _ = _).
       Search (_ + _ + _ = _).
       rewrite -> Nat.add_assoc.
       rewrite -> Nat.add_shuffle0.
       assert (H :   forall i : nat,
                     S (S n') ^ (S k' - i) * S n' ^ i =
                     S (S n') * (S (S n') ^ (k' - i) * S n' ^ i)).
       {
         intros i.
         (* Requires that k' < i *)
         admit.
       }
           
       rewrite -> (about_Sigma_with_two_equivalent_functions
                k'
                (fun j : nat => S (S n') ^ (S k' - j) * S n' ^ j)
                (fun j : nat => (S (S n')) * (S (S n') ^ (k' - j) * S n' ^ j))
                H
         ).
       rewrite -> (about_factoring_a_multiplicative_constant_on_the_left_in_Sigma
                k'
                (S (S n'))
                (fun j => S (S n') ^ (k' - j) * S n' ^ j)
         ).
       
       assert (J : S n' ^ S (S k') + S n' ^ S k'
                 =  (S (S n')) * (S n')^(S k')

                     ).
       {
         simpl.
         ring.
       }
       rewrite -> J.
       rewrite <- Nat.mul_add_distr_l.
       rewrite -> IHk'.
       simpl.
       ring.

