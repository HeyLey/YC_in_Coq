Import Nat.

Require Import fl.cfg.Definitions.
Require Import fl.int.Base2.
Require Import fl.cfg.Derivation.

Require Import List.

Module Base.
  Import ListNotations.

  Import Definitions Derivation.
  Import Base2.Base.

  Context {Tt Vt: Type}.

  Inductive ext_der {Tt Vt} (G : (@grammar Tt Vt)) : (list symbol) -> (list symbol) -> Prop :=
    | refl (p : list symbol) : ext_der G p p
    | inDer A p (in_der : (der G A p)): ext_der G [Vs A] p.


  Inductive SPPF_node : Type :=
  | mk_terminal_node : Tt  -> nat -> nat -> SPPF_node
  | mk_epsilon_node: nat -> nat -> SPPF_node
  | mk_nonterminal_node : Vt  -> nat -> nat -> SPPF_node
  | mk_intermediate_node :  @phrase Tt Vt -> nat -> nat -> SPPF_node.

  Inductive valid_parent : SPPF_node -> Type :=
  | mk_nonterminal_node_parent v from to : valid_parent (mk_nonterminal_node v from to)
  | mk_intermediate_node_parent p from to : valid_parent (mk_intermediate_node p from to).

  Inductive packed_SPPF_node : Type :=
  | mk_packed_node1 : SPPF_node -> packed_SPPF_node
  | mk_packed_node2 : SPPF_node -> SPPF_node -> packed_SPPF_node.

  Inductive SPPF_rel : Type :=
  | mk_rel : forall p : SPPF_node, (valid_parent p) -> packed_SPPF_node -> SPPF_rel.

  Definition SPPF := list SPPF_rel.

  Inductive sppf_der (sppf: SPPF) :  SPPF_node -> word -> Prop :=
  |  terDer (t : Tt) (from : nat) (to : nat) : sppf_der sppf (mk_terminal_node t from to) [T t]
  |  epsilonDer (from : nat) (to : nat) : sppf_der sppf (mk_epsilon_node from to) []
  |  mkRel1 p (vp : valid_parent p) ch1 w1 : In (mk_rel vp (mk_packed_node1 ch1)) sppf ->
                          (sppf_der sppf ch1 w1) -> sppf_der sppf p w1
  |  mkRel2 p (vp : valid_parent p) ch1 ch2 w1 w2 : In (mk_rel vp (mk_packed_node2 ch1 ch2)) sppf ->
                                 (sppf_der sppf ch1 w1) -> (sppf_der sppf ch2 w2) -> sppf_der sppf p (w1 ++ w2).

  Inductive triple :=
  |  var_triple : nat -> Vt -> nat -> triple
  |  phrase_triple : nat -> (@phrase Tt Vt) -> nat -> triple.

  Definition valid_parent_to_triple (s : SPPF_node) (vp : (valid_parent s)) : triple  :=
    match vp with
    | mk_nonterminal_node_parent v from to => (var_triple from v to)
    | mk_intermediate_node_parent p from to => (phrase_triple from p to)
    end.

  Definition node_to_phrase (s : SPPF_node) : (@phrase Tt triple):=
    match s with
    | mk_terminal_node t from to => [Ts (T t)]
    | mk_epsilon_node from to  => []
    | mk_nonterminal_node v from to => [Vs (V (var_triple from v to))]
    | mk_intermediate_node p from to => [Vs (V (phrase_triple from p to))]
    end.

  Definition SPPF_rel_to_rule (r : SPPF_rel) : (@rule Tt triple) :=
    match r with
    |  mk_rel p v n => let var := V (valid_parent_to_triple v) in
                       match n with
                       | mk_packed_node1 n1 => R var (node_to_phrase n1)
                       | mk_packed_node2 n1 n2 => R var ((node_to_phrase n1) ++ (node_to_phrase n2))
                       end
    end.

  Definition SPPF_to_grammar (s : SPPF) : (@grammar Tt triple) :=
    map SPPF_rel_to_rule s.


  Theorem in_p_eq (p : SPPF_node) (is_p1 is_p2 : valid_parent p) :
    (valid_parent_to_triple is_p1 = valid_parent_to_triple is_p2).
  Proof.
    destruct is_p1.
    simpl.
    remember (mk_nonterminal_node v from to) as p in *.
    destruct is_p2.
    injection Heqp.
    clear Heqp.
    intro H0; rewrite H0 in *; clear H0.
    intro H0; rewrite H0 in *; clear H0.
    intro H0; rewrite H0 in *; clear H0.
    simpl.
    reflexivity.
    discriminate.
    simpl.
    remember (mk_intermediate_node p from to) as n in *.
    destruct is_p2.
    discriminate.
    injection Heqn.
    clear Heqn.
    intro H0; rewrite H0 in *; clear H0.
    intro H0; rewrite H0 in *; clear H0.
    intro H0; rewrite H0 in *; clear H0.
    simpl.
    reflexivity.
  Qed.

  Theorem in_conversion (sppf : SPPF) (r : SPPF_rel):
  In r sppf -> In (SPPF_rel_to_rule r) (SPPF_to_grammar sppf).
  Proof.
    induction sppf.
    contradiction.
    intro H0.
    destruct H0.
    left.
    rewrite H.
    reflexivity.
    right.
    apply IHsppf.
    auto.
  Qed.

  Theorem simpl_node_to_phrase (n : SPPF_node) (is_p : valid_parent n):
       (node_to_phrase n) = [Vs (V (valid_parent_to_triple is_p))].
  Proof.
    destruct is_p.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Theorem eq1 {A} (l: list A): l = [] ++ l ++ [].
    simpl.
    induction l.
    reflexivity.
    simpl.
    rewrite <- IHl.
    reflexivity.
  Qed.


  Theorem der_from_in (sppf : SPPF) (p : SPPF_node) (vp : valid_parent p) (ch1 : SPPF_node):

  In (mk_rel vp (mk_packed_node1 ch1)) sppf ->
  der (SPPF_to_grammar sppf) (V (valid_parent_to_triple vp)) (node_to_phrase ch1).
  Proof.
    intro H0.
    apply rDer.
    apply (@in_conversion sppf (mk_rel vp (mk_packed_node1 ch1))).
    apply H0.
  Qed.

  Theorem to_phrase_conc {V0 T0} w1 w2: (@to_phrase V0 T0 (w1 ++ w2)) = (to_phrase w1 ++ to_phrase w2).
    induction w1.
    simpl.
    reflexivity.
    simpl.
    rewrite IHw1.
    reflexivity.
  Qed.

  Theorem der_cov1 (g : @grammar Tt triple) (A B: var) p0 p1
          (der1 : der g A p0) (der2 :  der g B ([Vs A] ++ p1)): der g B (p0 ++ p1).

   assert (eq1: forall(l1 l2: list (@symbol Tt triple)), l1 ++ l2 = [] ++ l1 ++ l2).
    { intros.
      simpl.
      reflexivity.
    }
    rewrite (eq1 p0 p1).

    apply replN with (B0 := A).

    apply der2.

    apply der1.
  Qed.

  Theorem der_cov2 (g : @grammar Tt triple) (A B: var) p0 p1
          (der1 : der g A p1) (der2 :  der g B (p0 ++ [Vs A])): der g B (p0 ++ p1).

   assert (eq1: forall(l1 l2: list (@symbol Tt triple)), l1 ++ l2 = l1 ++ l2 ++ []).
    { intros.
      rewrite app_nil_r.
      reflexivity.
    }
    rewrite (eq1 p0 p1).

    apply replN with (B0 := A).

    apply der2.

    apply der1.
  Qed.


  Theorem trains0 (sppf : SPPF) (n : SPPF_node) (w : word)
           (d : (sppf_der sppf n w)) :
    ext_der (SPPF_to_grammar sppf) (node_to_phrase n) (to_phrase w).
  Proof.
    induction d.
    simpl.
    apply refl.
    simpl.
    apply refl.
    pose proof (simpl_node_to_phrase vp).
    rewrite H0.
    apply inDer.
    remember (node_to_phrase ch1) as p1 in *.
    remember (to_phrase w1) as p2 in *.
    destruct IHd.
    rewrite Heqp1.
    apply der_from_in.
    exact H.
    rewrite (eq1 p0).
    apply replN with (B := A).
    rewrite <- (eq1 [Vs A]).
    rewrite Heqp1.
    apply  der_from_in.
    exact H.
    exact in_der.

    rewrite (simpl_node_to_phrase vp).

    rewrite (to_phrase_conc w1 w2).

    pose proof (@in_conversion sppf (mk_rel vp (mk_packed_node2 ch1 ch2))) H.
    clear H.

    remember (node_to_phrase ch1) as p1 in *.
    remember (to_phrase w1) as p2 in *.

    destruct IHd1.

    rewrite Heqp1.
    clear d1 Heqp1 Heqp2.

    remember (node_to_phrase ch2) as p1 in *.
    remember (to_phrase w2) as p2 in *.

    destruct IHd2.

    rewrite Heqp1.

    clear d2 Heqp1 Heqp2.

    apply inDer .
    apply rDer.
    apply H0.

    apply inDer.

    apply der_cov2 with (A := A).
    exact in_der.
    rewrite Heqp1.

    apply rDer.
    exact H0.

    remember (node_to_phrase ch2) as p1 in *.
    remember (to_phrase w2) as p2 in *.

    destruct IHd2.

    apply inDer.

    apply der_cov1 with (A := A).
    exact in_der.
    rewrite Heqp1.
    rewrite Heqp0.

    apply rDer.
    exact H0.

    apply inDer.

    apply der_cov1 with (A := A).
    exact in_der.
    apply der_cov2 with (A := A0).
    exact in_der0.
    rewrite Heqp1.
    rewrite Heqp0.

    apply rDer.

    exact H0.

  Qed.


  Theorem trains1 (sppf : SPPF) (n : SPPF_node) (is_p : valid_parent n) (w : word)
           (d : (sppf_der sppf n w)) :
     der (SPPF_to_grammar sppf) (V (valid_parent_to_triple is_p)) (to_phrase w).
  Proof.
    pose proof trains0 d.
    remember (node_to_phrase n) as p1 in *.
    remember (to_phrase w) as p2 in *.
    destruct H.
    destruct is_p.
    simpl in Heqp1.
    rewrite  Heqp1 in Heqp2.
    exfalso.
    clear Heqp1 d p.
    induction w.
    discriminate.
    discriminate.
    exfalso.
    rewrite  Heqp1 in Heqp2.
    clear Heqp1 d p.
    induction w.
    discriminate.
    discriminate.

    rewrite (simpl_node_to_phrase is_p) in Heqp1.
    injection Heqp1.
    intros.

    rewrite <- H.
    exact in_der.
  Qed.
End Base.








