Import Nat.

Add LoadPath "..".
Require Import CFG.Definitions.

Module Base.

  Import ListNotations.

  Context {Tt Vt: Type}.

  Inductive SPPF_node : Type :=
  | mk_terminal_node : Tt  -> nat -> nat -> SPPF_node
  | mk_epsilon_node: nat -> nat -> SPPF_node
  | mk_nonterminal_node : Vt  -> nat -> nat -> SPPF_node
  | mk_intermediate_node :  @phrase Tt Vt -> nat -> nat -> SPPF_node.

  Inductive valid_parent : SPPF_node -> Prop :=
  | mk_nonterminal_node_parent v from to : valid_parent (mk_nonterminal_node v from to)
  | mk_intermediate_node_parent p from to : valid_parent (mk_intermediate_node p from to).

  Inductive packed_SPPF_node : Type :=
  | mk_packed_node1 : SPPF_node -> packed_SPPF_node
  | mk_packed_node2 : SPPF_node -> SPPF_node -> packed_SPPF_node.

  Inductive SPPF_rel : Type :=
  | mk_rel : forall p : SPPF_node, (valid_parent p) -> packed_SPPF_node -> SPPF_rel.

  Record SPPF := mkSPPF {
    relations : list SPPF_rel;
  }.

  Inductive sppf_der (sppf: SPPF) :  SPPF_node -> word -> Prop :=
  |  terDer (t : Tt) (from : nat) (to : nat) : sppf_der sppf (mk_terminal_node t from to) [T t]
  |  epsilonDer (from : nat) (to : nat) : sppf_der sppf (mk_epsilon_node from to) []
  |  mkRel1 p vp ch1 w1 : In (mk_rel p vp (mk_packed_node1 ch1)) (relations sppf) ->
                          (sppf_der sppf ch1 w1) -> sppf_der sppf p w1
  |  mkRel2 p vp ch1 ch2 w1 w2 : In (mk_rel p vp (mk_packed_node2 ch1 ch2)) (relations sppf) ->
                          (sppf_der sppf ch1 w1) -> (sppf_der sppf ch2 w2) -> sppf_der sppf p w1.


End Base.








