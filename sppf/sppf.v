Import Nat.

Context {Tt Vt: Type}.
    
Inductive ter : Type :=
    | T : Tt -> ter.
    
Inductive var : Type :=
    | V : Vt -> var.
    
Inductive symbol : Type :=
    | Ts : ter -> symbol
    | Vs : var -> symbol.
    
Definition phrase := list symbol.

Inductive rule : Type :=
    | R : var -> phrase -> rule.

Inductive dot_rule : Type :=
    | dR : var -> phrase -> phrase -> dot_rule.

Definition grammar := list rule.

Inductive SPPF_node : Type :=
    | symbol_node : symbol -> nat -> nat -> SPPF_node
    | intermediate_node :  dot_rule -> nat -> nat ->  SPPF_node.

Inductive SPPF_packed_node : Type :=
    | single_packed_node : dot_rule -> nat -> SPPF_node -> SPPF_packed_node
    | double_packed_node : dot_rule -> nat -> SPPF_node -> SPPF_node -> SPPF_packed_node.

Inductive SPPF_rel : Type :=
    | sr : SPPF_node -> SPPF_packed_node -> SPPF_rel.

Record SPPF :=
  mkSPPF {
    root : SPPF_node;
    nodes : list SPPF_node;
    packed_node : list SPPF_packed_node;
    relation : list SPPF_rel;
  }.








