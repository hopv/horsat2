SOURCE = flags.ml utilities.ml scc.ml syntax.ml parser.mli parser.ml lexer.ml grammar.ml automaton.ml typing.ml reduce.ml flow.ml conversion.ml  stype.ml type.ml main.ml

parser.mli parser.ml:
	ocamlyacc parser.mly
lexer.ml:
	ocamllex lexer.mll

horsat: $(SOURCE)
	(ocamlopt -o horsat unix.cmxa  $(SOURCE); rm *.o *.cmi *.cmx; cd ..)

.SUFFIXES:
	.ml .cmo .mli .cmi

.ml.cmo:
	ocamlc $(SOURCE)

top: $(SOURCE)
	(ocamlmktop unix.cma $(SOURCE); cd ..)

clean: 
	rm *.cmi *.cmx *.o *.cmo *.exe parser.ml lexer.ml parser.mli lexer.mli



