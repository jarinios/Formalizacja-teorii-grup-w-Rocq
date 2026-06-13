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
      
Require Import ZArith.
Open Scope Z_scope.
Compute (Z.add 2 3).
Compute (Z.opp 7).


(*Tu miała być grupa liczba całkowitych*)
Definition Z_group :=
  is_group Z 0 Z.add Z.opp.
Check Z_group.


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
  

(*Przykład*)



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
  destruct H1 as [H1_left H1_right].
  destruct H2 as [H2_left H2_right].
  rewrite <- (H1_left e2).
  rewrite (H2_right e1).
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
