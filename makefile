OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc

.PHONY: all objs clean

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

all: .depend ppdltab

objs: more.cmo form.cmo tForm.cmo tab.cmo

clean:
	-rm -v *.cmo *.cmx *.cmi *.o ppdltab parser.ml parser.mli lexer.ml .depend

.depend: $(wildcard *.mli) *.ml
	$(OCAMLDEP) $^ > .depend

include .depend

.ml.cmo:
	$(OCAMLC) -c $(COMPFLAGS) $<

.ml.cmx:
	$(OCAMLOPT) -c $(COMPFLAGS) $<

.mli.cmi:
	$(OCAMLOPT) -c $(COMPFLAGS) $<

.mll.ml:
	$(OCAMLLEX) $<

.mly.ml:
	$(OCAMLYACC) -v $<

lexer.cmo: lexer.ml parser.cmi

lexer.cmx: lexer.ml parser.cmi

parser.mli: parser.ml

ppdltab: more.cmx form.cmx lexer.cmx parser.cmx tForm.cmx tab.cmx ppdltab.cmx
	$(OCAMLOPT) -o $@ $^
	strip $@
