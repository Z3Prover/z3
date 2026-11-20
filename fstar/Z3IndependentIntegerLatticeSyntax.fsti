module Z3IndependentIntegerLatticeSyntax

module C = Z3LpCertificate
module G = Z3LpGomorySyntax

val candidate (context:C.certificate) (index:nat) : option G.certificate
