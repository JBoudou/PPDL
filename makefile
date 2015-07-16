CAMLC=ocamlc
CAMLDEP=ocamldep
CAMLOPT=ocamlopt

SRCS= more.ml form.ml dir.ml hForm.ml setSet.ml hintikka.ml elimination.ml test.ml tForm.ml tab.ml
OBJS= ${SRCS:.ml=.cmo}

all: .depend ${OBJS} test

.depend: $(SRCS)
	$(CAMLDEP) $^ test.ml > .depend

include .depend

#doc:
#	cd doc && $(MAKE)

clean:
	-rm -v ${OBJS} {SRCS:.ml=.cmi} test
#	cd doc && $(MAKE) clean

.PHONY: all clean

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(CAMLC) -c $(COMPFLAGS) $<

.ml.cmx:
	$(CAMLOPT) -c $(COMPFLAGS) $<

.mli.cmi:
	$(CAMLOPT) -c $(COMPFLAGS) $<

.mll.ml:
	ocamllex $<

.mly.ml:
	ocamlyacc -v $<

test_parse: more.cmx form.cmx lexer.cmx parser.cmx tForm.cmx tab.cmx test_parse.cmx
	$(CAMLOPT) -o $@ $^

lexer.cmo: lexer.ml parser.cmi

lexer.cmx: lexer.ml parser.cmi

parser.mli: parser.ml

test: ${SRCS:.ml=.cmx}
	$(CAMLOPT) -o test $^
