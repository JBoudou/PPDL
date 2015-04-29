CAMLC=ocamlc
CAMLDEP=ocamldep

SRCS= form.ml hForm.ml more.ml loc.ml setSet.ml hintikka.ml elimination.ml
OBJS= ${SRCS:.ml=.cmo}

all: .depend ${OBJS}

.depend: $(SRCS)
	$(CAMLDEP) $^ > .depend

include .depend

#doc:
#	cd doc && $(MAKE)

clean:
	-rm -v ${OBJS} {SRCS:.ml=.cmi}
#	cd doc && $(MAKE) clean

.PHONY: all clean

.SUFFIXES: .ml .mli .cmo .cmi

.ml.cmo:
	$(CAMLC) -c $(COMPFLAGS) $<


