#define _GNU_SOURCE 1

#include "runtime.h"

#include "gc.h"
#include "runtime_type_checks.h"
#include "runtime_common.h"

long long pack_type(void* x, OPND_TYPE_T x_type){
    long long result = ((unsigned long long)x_type << 32) | (unsigned int)x;
    return result;
}

char* type_to_string(OPND_TYPE_T t){
    if(t == INT_OPND_TYPE){
        return "int";
    }
    else if(t == STR_OPND_TYPE){
        return "string";
    }
    else if(t == ARR_OPND_TYPE){
        return "array";
    }
    else if(t == SEXP_OPND_TYPE){
        return "sexp";
    }
    else{
        return "UndefinedType";
    }
}

void type_check_error(char* info){
    failure("TypeError: %s", info);
}

void Bsta_type_check(void *x, OPND_TYPE_T x_type, int i, OPND_TYPE_T i_type, void *v, OPND_TYPE_T v_type){
  //failure("%s %s %s", type_to_string(x_type), type_to_string(i_type), type_to_string(v_type));
  bool is_array_or_string_or_sexp = (x_type == ARR_OPND_TYPE) || (x_type == STR_OPND_TYPE) || (x_type == SEXP_OPND_TYPE);
  if(!is_array_or_string_or_sexp){
    char * info = malloc(100);
    sprintf(info, "%s has no [] method", type_to_string(x_type));
    type_check_error(info);
  }

  if(i_type != INT_OPND_TYPE){
    char * info = malloc(100);
    sprintf(info, "indices must integers, not %s", type_to_string(i_type));
    type_check_error(info);
  }

}