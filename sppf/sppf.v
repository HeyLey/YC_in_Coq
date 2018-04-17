Import Nat.

Add LoadPath "..".
Require Import CFG.Definitions.

Module Base.

  Import Definitions.

  Context {Tt Vt: Type}.

  Inductive SPPF_node : Type :=
  | symbol_node : (@symbol Tt Vt)  -> nat -> nat -> SPPF_node
  | epsilon_node: nat -> nat -> SPPF_node
  | intermediate_node :  @phrase Tt Vt -> nat -> nat ->  SPPF_node.

  Inductive SPPF_packed_node : Type :=
  | mk_packed_node :  @phrase Tt Vt -> nat -> SPPF_node -> SPPF_node -> SPPF_packed_node.

  Inductive SPPF_rel : Type :=
    | sr : SPPF_node -> SPPF_node -> SPPF_rel
    | sp : SPPF_node -> SPPF_packed_node -> SPPF_rel.

  Record SPPF :=
  mkSPPF {
    nodes : list SPPF_node;
    packed_node : list SPPF_packed_node;
    relation : list SPPF_rel;
    }.

End Base.








