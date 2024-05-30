all: Bindings.a


BindingsCaml.o: Bindings.ml
	ocamlfind ocamlc -package base64 -linkpkg -custom -output-obj -o BindingsCaml.o Bindings.ml
#	ocamlc -custom -output-obj -o BindingsCaml.o Bindings.ml

BindingsWrap.o: BindingsWrap.c
	ocamlc -c BindingsWrap.c

Bindings.a: BindingsCaml.o BindingsWrap.o
	cp `ocamlc -where`/libcamlrun.a Bindings.a && chmod +w Bindings.a
	ar r Bindings.a BindingsCaml.o BindingsWrap.o


clean:
	rm -f *.cm[ioxa] *.o *.a
