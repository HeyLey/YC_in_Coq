Import Nat.

Require Import List.

Module Base.

  Import ListNotations.

  Context {Tt Vt: Type}.

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
  |  mkRel1 p vp ch1 w1 : In (mk_rel p vp (mk_packed_node1 ch1)) sppf ->
                          (sppf_der sppf ch1 w1) -> sppf_der sppf p w1
  |  mkRel2 p vp ch1 ch2 w1 w2 : In (mk_rel p vp (mk_packed_node2 ch1 ch2)) sppf ->
                                 (sppf_der sppf ch1 w1) -> (sppf_der sppf ch2 w2) -> sppf_der sppf p w1.

  Inductive triple :=
    mkTriple : nat -> (@phrase Tt Vt) -> nat -> triple.

  Definition valid_parent_to_triple (s : SPPF_node) (vp : (valid_parent s)) : triple  :=
    match vp with
    | mk_nonterminal_node_parent v from to => (mkTriple from [Vs (V v)] to)
    | mk_intermediate_node_parent p from to => (mkTriple from p to)
    end.

  Definition node_to_phrase (s : SPPF_node) : (@phrase Tt triple):=
    match s with
    | mk_terminal_node t from to => [Ts (T t)]
    | mk_epsilon_node from to  => []
    | mk_nonterminal_node v from to => [Vs (V (mkTriple from [Vs (V v)] to))]
    | mk_intermediate_node p from to => [Vs (V (mkTriple from p to))]
    end.

  Definition SPPF_rel_to_rule (r : SPPF_rel) : (@rule Tt triple) :=
    match r with
    |  mk_rel p v n => let var := V (valid_parent_to_triple p v) in
                       match n with
                       | mk_packed_node1 n1 => R var (node_to_phrase n1)
                       | mk_packed_node2 n1 n2 => R var ((node_to_phrase n1) ++ (node_to_phrase n2))
                       end
    end.

  Definition SPPF_to_grammar (s : SPPF) : (@grammar Tt triple) :=
    map SPPF_rel_to_rule s.


  Theorem in_p_eq (p : SPPF_node) (is_p1 is_p2 : valid_parent p) :
    (valid_parent_to_triple p is_p1 = valid_parent_to_triple p is_p2).
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

  Theorem in1 (t : Tt) (from to : nat) (p : SPPF_node) (is_p vp : valid_parent p) (sppf : SPPF) :
    In (mk_rel p vp (mk_packed_node1 (mk_terminal_node t from to))) sppf ->
    In (R (V (valid_parent_to_triple p is_p)) (to_phrase [T t])) (SPPF_to_grammar sppf).
  Proof.
    intro H0.
    induction sppf.
    contradiction.
    destruct H0.
    simpl.
    left.
    rewrite H.
    simpl.
    assert (Heq : (valid_parent_to_triple p vp) = (valid_parent_to_triple p is_p)).
    apply in_p_eq.
    rewrite Heq.
    reflexivity.
    right.
    apply IHsppf.
    exact H.
  Qed.

  Theorem in2 (from to : nat) (p : SPPF_node) (is_p vp : valid_parent p) (sppf : SPPF) :
    In (mk_rel p vp (mk_packed_node1 (mk_epsilon_node from to))) sppf ->
    In (R (V (valid_parent_to_triple p is_p)) (to_phrase [])) (SPPF_to_grammar sppf).
  Proof.
    intro H0.
    induction sppf.
    contradiction.
    destruct H0.
    left.
    rewrite H.
    simpl.
    assert (Heq : (valid_parent_to_triple p vp) = (valid_parent_to_triple p is_p)).
    apply in_p_eq.
    rewrite Heq.
    reflexivity.
    right.
    apply IHsppf.
    exact H.
  Qed.

  Theorem trains1 (sppf : SPPF) (n : SPPF_node) (is_p : valid_parent n) (w : word)
           (d : (sppf_der sppf n w)) :
    der (SPPF_to_grammar sppf) (V (valid_parent_to_triple n is_p)) (to_phrase w).
  Proof.
    induction d.
    remember (mk_terminal_node t from to) as root in *.
    destruct is_p; discriminate.
    remember (mk_epsilon_node from to) as root in *.
    destruct is_p; discriminate.
    destruct ch1.
    remember (mk_terminal_node t n n0) as root in *.
    destruct d.
    injection Heqroot.
    clear Heqroot.
    intro H0; rewrite H0 in *; clear H0.
    intro H0; rewrite H0 in *; clear H0.
    intro H0; rewrite H0 in *; clear H0.

    apply rDer.
    apply (in1 t n n0 p is_p vp).
    exact H.

    apply rDer.

    apply (in2 from to p is_p vp).
    exact H.

    rewrite -> Heqroot in IHd.
    simpl IHd.
    assert der (SPPF_to_grammar sppf) ((mkTriple n [Vs (V v)] n0)) (to_phrase w1).


    apply IHd.

End Base.








