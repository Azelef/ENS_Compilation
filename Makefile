CMO= x86_64.cmo lexer.cmo parser.cmo astprinter.cmo typer.cmo TtoA.cmo AtoAsm.cmo main.cmo
GENERATED = lexer.ml parser.ml parser.mli
SOURCES = x86_64.ml typer.ml TtoA.ml AtoAsm.ml main.ml
FLAGS=-annot -g

all: pkotlinc

pkotlinc: $(CMO)
	ocamlc $(FLAGS) -o $@ $(CMO)

.SUFFIXES: .mli .ml .cmi .cmo .mll .mly

.mli.cmi:
	ocamlc $(FLAGS) -c  $<

.ml.cmo:
	ocamlc $(FLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	menhir -v $<

.mly.mli:
	menhir -v $<

clean:
	rm -f *.cm[io] *.o *.annot *~ pkotlinc $(GENERATED)
	rm -f parser.output parser.automaton parser.conflicts
	rm -f parser.mli parser.ml

.depend depend:$(GENERATED)
	rm -f .depend
	ocamldep *.ml *.mli > .depend

include .depend



