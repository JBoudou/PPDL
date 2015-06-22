CAMLC=ocamlc
CAMLDEP=ocamldep
CAMLOPT=ocamlopt

SRCS= more.ml form.ml dir.ml hForm.ml setSet.ml hintikka.ml elimination.ml test.ml tForm.ml
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

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(CAMLC) -c $(COMPFLAGS) $<

.ml.cmx:
	$(CAMLOPT) -c $(COMPFLAGS) $<

test: ${SRCS:.ml=.cmx}
	$(CAMLOPT) -o test $^
