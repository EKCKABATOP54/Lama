#include "runtime_common.h"

PACKED_VALUE_TYPE pack_type(void* x, OPND_TYPE_T x_type);

void Bsta_type_check(void *x, OPND_TYPE_T x_type, int i, OPND_TYPE_T i_type, void *v, OPND_TYPE_T v_type);

void Belem_type_check(void *p, void* p_type, int i, void* i_type);

void Llength_type_check (void *p, OPND_TYPE_T p_type);