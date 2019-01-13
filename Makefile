SOURCE = flags.ml utilities.ml setqueue.ml obdd.mli obdd.ml pobdd.mli pobdd.ml scc.ml syntax.ml parser.mli parser.ml lexer.ml grammar.ml automaton.ml alternatingAutomaton.mli alternatingAutomaton.ml conversion.ml stype.ml ai.ml type.ml cegen.ml saturate.ml main.ml

all: horsat2

parser.mli parser.ml: parser.mly
	ocamlyacc parser.mly
lexer.ml: lexer.mll
	ocamllex lexer.mll

horsat2: $(SOURCE)
	(ocamlopt -inline 1000 -o horsat2 unix.cmxa $(SOURCE); rm *.o *.cmi *.cmx; cd ..)
#	(ocamlopt -unsafe -inline 1000 -o horsat unix.cmxa $(SOURCE); rm *.o *.cmi *.cmx; cd ..)


.SUFFIXES:
	.ml .cmo .mli .cmi

.PHONY:
	all clean

.ml.cmo:
	ocamlc $(SOURCE)

top: $(SOURCE)
	(ocamlmktop unix.cma $(SOURCE); cd ..)

clean: 
	rm *.cmi *.cmx *.o *.cmo *.exe horsat parser.ml lexer.ml parser.mli lexer.mli



