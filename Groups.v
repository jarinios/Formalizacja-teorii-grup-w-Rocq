(*1. Podstawowe definicje*)

(* Definiujemy grupę*)
(* is_group mówi, że podane obiekty spełniają aksjomaty grup.*)
Definition is_group
  (G : Type) (*odpowiedni zbioru*)
  (e : G) (*element neutralny*)
  (op : G -> G -> G) (* działanie grupowe*)
  (inv : G -> G) (*działanie odwrotności*)
  : Prop := (*Aksjomaty grupy*)
  (forall a b c : G, op a (op b c) = op (op a b) c)
  /\
  (forall a : G, op e a = a)
  /\
  (forall a : G, op a e = a)
  /\
  (forall a : G, op (inv a) a = e)
  /\
  (forall a : G, op a (inv a) = e).
      

Require Import Ensembles.

(* Definicja podgrupy *)
Definition is_subgroup
  (G : Type)
  (e : G)
  (op : G -> G -> G)
  (inv : G -> G)
  (H : Ensemble G)
  : Prop :=
  In G H e (*Element neutralny należy do H, tak zapisuje się to z wykorzystanie In w Ensemble*)
  /\
  (forall a b : G, In G H a -> In G H b -> In G H (op a b))
  /\
  (forall a : G, In G H a -> In G H (inv a)).


(*Definicja wartwy lewostronnej*)
Definition left_coset
  (G : Type)
  (op : G -> G -> G)
  (H : Ensemble G) (*H jest podgrupą G*)
  (g : G) 
  : Ensemble G :=  fun x : G => exists h : G, In G H h /\ x = op g h.
  
  
(*Definicja warstwy prawostronnej*)  
Definition right_coset
  (G : Type)
  (op : G -> G -> G)
  (H : Ensemble G) (*H jest podgrupą G*)
  (g : G) 
  : Ensemble G :=  fun x : G => exists h : G, In G H h /\ x = op h g.
  
  
  
  
  
  
  
Inductive Z4 : Type :=
  | z0 | z1 | z2 | z3.

Definition Z4_add (a b : Z4) : Z4 :=
  match a, b with
  | z0, x => x
  | x, z0 => x
  | z1, z1 => z2
  | z1, z2 => z3
  | z1, z3 => z0
  | z2, z1 => z3
  | z2, z2 => z0
  | z2, z3 => z1
  | z3, z1 => z0
  | z3, z2 => z1
  | z3, z3 => z2
  end.


Definition Z4_zero : Z4 := z0.

Definition Z4_inv (a : Z4) : Z4 :=
  match a with
  | z0 => z0
  | z1 => z3
  | z2 => z2
  | z3 => z1
  end.


Lemma Z4_add_zero_r :
  forall a, Z4_add a Z4_zero = a.
Proof.
  intros a.
  destruct a; simpl; reflexivity.
Qed.

Lemma Z4_add_assoc :
  forall a b c, Z4_add a (Z4_add b c) = Z4_add (Z4_add a b) c.
Proof.
  intros a b c.
  destruct a, b, c;
  simpl;
  reflexivity.
Qed.

Lemma Z4_inv_l :
  forall a, Z4_add (Z4_inv a) a = Z4_zero.
Proof.
  intros a.
  destruct a;
  simpl; 
  reflexivity.
Qed.

Lemma Z4_inv_r :
  forall a, Z4_add a (Z4_inv a) = Z4_zero.
Proof.
  intros a.
  destruct a;
  simpl;
  reflexivity.
Qed. 

  
Theorem Z4_is_group :
  is_group Z4 Z4_zero Z4_add Z4_inv.
Proof.
  unfold is_group.
  repeat split.
  - apply Z4_add_assoc.
  - apply Z4_add_zero_r.
  - apply Z4_inv_l.
  - apply Z4_inv_r.
Qed.
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
(*2. Podstawowe twierdzenia i przykłady*)

(*Dla każdej grupy istnieje dokładnie jeden element neutralny*)
(*Na początek definiujemy co znaczny, że element jest neutralny*)
Definition is_identity
  (G : Type)
  (op : G -> G -> G)
  (e : G)
  : Prop := (forall a : G, op e a = a) /\ (forall a : G, op a e = a).
  
(*Formułujemy twierdzenie: jeśli są dwa elementy neutralne to jest to ten sam element*)
Theorem identity_unique_in_group :
  forall (G : Type) (op : G -> G -> G) (e1 e2 : G),
    is_identity G op e1 -> is_identity G op e2 -> e1 = e2.
Proof.
  intros G op e1 e2 H1 H2.
  destruct H1 as [H11 H12]. (*Wygodny sposób robicia*)
  destruct H2 as [H21 H22].
  rewrite <- (H11 e2).
  rewrite (H22 e1).
  reflexivity.
Qed.

(*Definiujemy pojecie odwrotności*)
Definition is_inverse
  (G : Type)
  (e : G)
  (op : G -> G -> G)
  (a b : G)
  : Prop := op a b = e /\ op b a = e.
  
(*Dla dowolnego elementu grupy element odwrotny jest wyznaczony jednoznacznie, tzn. jeśli są dwa 
elementy odwrotne b i c do elementu a to b = c*)
Theorem inverse_unique_in_group :
  forall (G : Type) (e : G) (op : G -> G -> G) (inv : G -> G) (a b c : G),
    is_group G e op inv -> is_inverse G e op a b -> is_inverse G e op a c -> b = c.
Proof.
  intros G e op inv a b c Hgroup Hinv_b Hinv_c.
  destruct Hgroup.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct Hinv_b.
  destruct Hinv_c.
  rewrite <- (H1 b).
  rewrite <- H6.
  rewrite <- H0.
  rewrite <- H5.
  rewrite <- H.
  reflexivity.
Qed.

(*Prawo skracania z lewej strony*)
Theorem left_cancellation :
  forall (G : Type) (e : G) (op : G -> G -> G) (inv : G -> G) (a b c : G),
    is_group G e op inv -> op a b = op a c -> b = c.
Proof.
  intros G e op inv a b c Hgroup H1.
  destruct Hgroup.
  destruct H0.
  destruct H2.
  destruct H3.
  rewrite <- (H0 b).
  rewrite <- (H0 c).
  rewrite <- (H3 a).
  rewrite <- H.
  rewrite <- H.
  rewrite <- H1.
  reflexivity.
Qed.

(*Prawo skracania z prawej strony*)
Theorem right_cancellation :
  forall (G : Type) (e : G) (op : G -> G -> G) (inv : G -> G) (a b c : G),
    is_group G e op inv -> op b a = op c a -> b = c.
Proof.
  intros G e op inv a b c Hgroup H1.
  destruct Hgroup.
  destruct H0.
  destruct H2.
  destruct H3.
  rewrite <- (H2 b).
  rewrite <- (H2 c).
  rewrite <- (H4 a).
  rewrite H.
  rewrite H.
  rewrite H1.
  reflexivity.
Qed.


(*(a^-1)^-1 = a*)
Theorem inv_involutive :
  forall (G : Type) (e : G) (op : G -> G -> G) (inv : G -> G) (a : G),
    is_group G e op inv -> inv (inv a) = a.
Proof.
  intros G e op inv a Hgroup.
  apply (inverse_unique_in_group G e op inv (inv a) (inv (inv a)) a).
  - exact Hgroup.
  - split.
    + apply Hgroup.
    + apply Hgroup.
  - split.
    + destruct Hgroup.
      destruct H0.
      destruct H1.
      destruct H2.
      apply H2.
    + destruct Hgroup.
      destruct H0.
      destruct H1.
      destruct H2.
      apply H3.
Qed.
  
 
  
(*(ab)^-1 = b^-1 a^-1*)
Theorem inv_op :
  forall (G : Type) (e : G) (op : G -> G -> G) (inv : G -> G) (a b : G),
    is_group G e op inv -> inv (op a b) = op (inv b) (inv a).
Proof.
  intros G e op inv a b Hgroup.
  apply sym_eq. (*zamienia strony w równości*)
  apply (inverse_unique_in_group G e op inv (op a b)).
  - exact Hgroup. (*Dowód pierwszego celu, który jest w założeniach*)
  - (* inv (ab) jest odwrotnością ab *)
    split.
    + destruct Hgroup.
      destruct H0.
      destruct H1.
      destruct H2.
      rewrite (H (op a b) (inv b) (inv a)).
      rewrite <- (H a b (inv b)).
      rewrite H3.
      rewrite H1.
      apply H3.
    + destruct Hgroup.
      destruct H0.
      destruct H1.
      destruct H2.
      rewrite <- (H (inv b) (inv a) (op a b)).
      rewrite (H (inv a) a b).
      rewrite H2.
      rewrite H0.
      apply H2.
  - (* b^{-1}a^{-1} jest odwrotnością ab *)
    split.
    + destruct Hgroup.
      destruct H0.
      destruct H1.
      destruct H2.
      apply H3.

    + destruct Hgroup.
      destruct H0.
      destruct H1.
      destruct H2.
      apply H2.      
Qed.
  
(*Przykłady *)




(*3*)
Inductive Z3 : Type := | z0 | z1 | z2.

Definition Z3_add (a b : Z3) : Z3 :=
  match a, b with
  | z0, x => x 
  | x, z0 => x 
  | z1, z1 => z2
  | z1, z2 => z0 
  | z2, z1 => z0 
  | z2, z2 => z1 end.

Definition Z3_zero : Z3 := z0.

Definition Z3_inv (a : Z3) : Z3 := 
  match a with
  | z0 => z0
  | z1 => z2 
  | z2 => z1 
end.

(*Definicja grupy abelowej*)
Definition is_abelian_group
  (G : Type)
  (e : G)
  (op : G -> G -> G)
  (inv : G -> G)
  : Prop := is_group G e op inv /\ (forall a b : G, op a b = op b a).
  
(*Dowód, że Z3 jest grupą abelową*)
Theorem Z3_abelian :
  is_abelian_group Z3 Z3_zero Z3_add Z3_inv.
Proof.
  split.
  - split.
    + intros a b c.
      destruct a; 
      destruct b; 
      destruct c; 
      reflexivity.
    + split.
      * intros a.
        destruct a; 
        reflexivity.
      * split.
        -- intros a.
           destruct a;
           reflexivity.
        -- split.
           ++ intros a.
              destruct a;
              reflexivity.
           ++ intros a.
              destruct a;
              reflexivity.
  - intros a b.
    destruct a;
    destruct b;
    reflexivity.
Qed. 
 
 
 
 
 
