# The base name of the executable
PROG=test

# The list of object files
CMOS=iSet.cmo test.cmo
CMXS=$(CMOS:.cmo=.cmx)

# Choose your target: bytecode, native or both
#all: $(PROG).byte
all: $(PROG).native
#all: $(PROG).byte $(PROG).native

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLDOC=ocamldoc
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

byte:
	# chowanie iSet.mli żeby wewnątrz testu można było oglądać drzewa
	mv -v iSet.mli iSet.mli.schowane || true 
	$(MAKE) $(PROG).byte || true
	# przywracanie iSet.mli
	mv -v iSet.mli.schowane iSet.mli || true 
	

native: $(PROG).native

$(PROG).byte: $(CMOS)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $^

$(PROG).native: $(CMXS)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $^

.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.FORCE:

doc:	.FORCE
	mkdir -p doc
	$(OCAMLDOC) $(INCLUDES) -html -d doc *.mli *.ml

clean:
	rm -f *.cm[iox] *.o

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > $@

depend:
	rm .depend
	$(MAKE) .depend

include .depend

zip:
	cd ..; rm testy.zip; zip -r testy.zip testy/iSet.mli testy/test.ml testy/Makefile testy/README_do_testowania.txt
