# This is a temporary support file for emacs annotations. 
# It does not compile the Z3 ML API; this will be built 
# in the top-level build directory.

all: 
	ocamlbuild -cflag -annot z3.cmxa

doc: *.ml
	mkdir -p doc
	ocamldoc -html -d doc -I _build -sort *.mli -hide Z3
