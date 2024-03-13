#define _GNU_SOURCE 1

#include "runtime.h"

#include "gc.h"
#include "runtime_type_checks.h"
#include "runtime_common.h"

#define ERROR_BUF_SIZE 400
const char error_buffer[ERROR_BUF_SIZE];

/*
PACKED_VALUE_TYPE pack_type(void* x, OPND_TYPE_T x_type){
    PACKED_VALUE_TYPE result = ((PACKED_VALUE_TYPE)x_type << 32) | (unsigned int)x;
    return result;
}
*/

PACKED_VALUE_TYPE pack_type(void* x, OPND_TYPE_T x_type){
    
    int *addr = default_return_memory_loc();
    addr[0] = x_type;
    addr[1] = x;
    return addr;
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

static type_check_error(char* fmt, ...){
    va_list args;
    va_start(args, fmt);
    char *formatted_error_buf = malloc(ERROR_BUF_SIZE);
    sprintf(formatted_error_buf, "TypeError: %s", fmt);
    vfailure(formatted_error_buf, args);
    va_end(args);
}


static void element_access_check(void *p, void* p_type, int i, void* i_type){
    bool is_array_or_string_or_sexp = (p_type == ARR_OPND_TYPE) || (p_type == STR_OPND_TYPE) || (p_type == SEXP_OPND_TYPE);
    if(!is_array_or_string_or_sexp){
        type_check_error("%s has no method for accessing elements", type_to_string(p_type));
    }

    if(i_type != INT_OPND_TYPE){
        type_check_error("indices must be integers, not %s", type_to_string(i_type));
    } 
}

void Bsta_type_check(void *x, OPND_TYPE_T x_type, int i, OPND_TYPE_T i_type, void *v, OPND_TYPE_T v_type){
    if (x_type == STR_OPND_TYPE || x_type == ARR_OPND_TYPE) { //ugly beceause strange STI and STA generation in SM
        element_access_check(x, x_type, i, i_type);
        if(x_type == STR_OPND_TYPE && v_type != INT_OPND_TYPE){
            type_check_error("Unable to set %s as string's element", type_to_string(v_type));
        }
    }
    else{ //x - addr, not string, array, sexp
        //TODO
    }
}

void Belem_type_check(void *p, OPND_TYPE_T p_type, int i, OPND_TYPE_T i_type){
    element_access_check(p, p_type, i, i_type);
}

void Llength_type_check (void *p, OPND_TYPE_T p_type){
    if(!(p_type == ARR_OPND_TYPE || p_type == STR_OPND_TYPE || p_type == SEXP_OPND_TYPE )){
        type_check_error("%s has no \"length\" attribute", type_to_string(p_type));
    }
}
