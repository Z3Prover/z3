module Z3FiniteFieldCertificate

open Z3AstTheory

type pac_node =
  | PacInput : index:int -> pac_node
  | PacAdd : left:int -> right:int -> pac_node
  | PacMul : source:int -> coefficient:expr -> factor:list int -> pac_node

type certificate = {
  pac_premises: list expr;
  pac_nodes: list pac_node;
  pac_root: int;
  pac_support: list int;
}
