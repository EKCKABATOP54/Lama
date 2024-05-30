FLAGS=-m32 -g2 -fstack-protector-all -I `ocamlc -where` -lcurses -lm -lzstd

all:Bindings.a byterun.o
	$(CC) $(FLAGS) -o byterun byterun.o ../runtime/runtime.a Bindings.a

Bindings.a:
	cp ../bindings/Bindings.a .

byterun.o: byterun.c
	$(CC) $(FLAGS) -g -c byterun.c

clean:
	$(RM) *.a *.o *~ byterun
