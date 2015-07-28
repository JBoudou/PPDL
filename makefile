OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
OCAMLDOC=ocamldoc
COMPFLAGS=-g
OPTFLAGS=

.PHONY: all objs test clean doc

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

all: .depend ppdltab

objs: more.cmo form.cmo tForm.cmo tab.cmo

test: test_tab

clean:
	-rm -v *.cmo *.cmx *.cmi *.o ppdltab test_tab parser.ml parser.mli lexer.ml .depend

doc: more.ml form.ml tForm.ml tab.ml
	$(OCAMLDOC) -d html -html $^

.depend: $(wildcard *.mli) *.ml
	$(OCAMLDEP) $^ > .depend

include .depend

.ml.cmo:
	$(OCAMLC) -c $(COMPFLAGS) $<

.ml.cmx:
	$(OCAMLOPT) -c $(OPTFLAGS) $<

.mli.cmi:
	$(OCAMLOPT) -c $(OPTFLAGS) $<

.mll.ml:
	$(OCAMLLEX) $<

.mly.ml:
	$(OCAMLYACC) -v $<

lexer.cmo: lexer.ml parser.cmi

lexer.cmx: lexer.ml parser.cmi

parser.mli: parser.ml

ppdltab: more.cmx form.cmx lexer.cmx parser.cmx tForm.cmx tab.cmx ppdltab.cmx
	$(OCAMLOPT) -o $@ $(OPTFLAGS) $^

test_tab: more.cmo form.cmo tForm.cmo tab.cmo test_tab.ml
	$(OCAMLC) -o $@ $(COMPFLAGS) $^
