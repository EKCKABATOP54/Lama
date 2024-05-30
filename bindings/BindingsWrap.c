#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>
#include "../runtime/runtime_type_checks.h"
#include "../runtime/runtime_common.h"

int extern_ocaml_fib(int n)
{
  run_caml();
  static const value * fib_closure = NULL;
  if (fib_closure == NULL) fib_closure = caml_named_value("extern_ocaml_fib");
  return Int_val(caml_callback(*fib_closure, Val_int(n)));
}

PACKED_VALUE_TYPE extern_ocaml_is_consistent(value t1, void* trash1, value t2, void* trash2){
  run_caml();
  //caml_param2(t1, t2); ld error???
  static const value * is_consistent_closure = NULL;
  if (is_consistent_closure == NULL) is_consistent_closure = caml_named_value("extern_ocaml_is_consistent");
  //camlReturn ld error???
  return pack_type(Bool_val(caml_callback2(*is_consistent_closure, t1, t2)), INT_OPND_TYPE);
}

void* gen_ocaml_value(char* serialized_type, void* trash){
  //run_caml();
  //static const value * marshal_from_string_closure = NULL;
  //if (marshal_from_string_closure == NULL) marshal_from_string_closure = caml_named_value("extern_ocaml_marshal_from_b64string");
  return pack_type(1, INT_OPND_TYPE);
  //return pack_type(caml_callback(*marshal_from_string_closure, caml_copy_string(serialized_type)), UNDEFINED_OPND_TYPE);
}

char* extern_ocaml_type_to_string(){

}