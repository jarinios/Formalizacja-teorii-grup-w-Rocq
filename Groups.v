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
  (g : G) (*Element generujący warstwę*)
  : Ensemble G :=  fun x : G => exists h : G, In G H h /\ x = op g h.
  
  
(*Definicja warstwy prawostronnej*)  
Definition right_coset
  (G : Type)
  (op : G -> G -> G)
  (H : Ensemble G) (*H jest podgrupą G*)
  (g : G) (*element generujący warstwę*)
  : Ensemble G :=  fun x : G => exists h : G, In G H h /\ x = op h g.
  
  
(*Dla każdej grupy istnieje dokładnie jeden element neutralny*)
(**)
Definition is_identity
  (G : Type)
  (op : G -> G -> G)
  (e : G)
  : Prop := (forall a : G, op e a = a) /\ (forall a : G, op a e = a).
  
Theorem identity_unique :
  forall (G : Type) (op : G -> G -> G) (e1 e2 : G),
    is_identity G op e1 -> is_identity G op e2 -> e1 = e2.
Proof.
  intros G op e1 e2 H1 H2.
