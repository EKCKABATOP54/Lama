
#ifndef __BINDINGS_H__
#define __BINDINGS_H__

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/callback.h>

/*extern*/ int extern_ocaml_fib(int n);

/*extern*/ value extern_ocaml_is_consistent(value t1, value t2);

#endif