#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>


#ifndef SNAKE_H
#define SNAKE_H

typedef uint64_t snake_val_t;

extern const uint64_t NUM_MASK;
extern const uint64_t BOOL_MASK;
extern const uint64_t TUP_MASK;
extern const uint64_t CLOS_MASK;
extern const uint64_t FWD_PTR_MASK;
extern const uint64_t NUM_TAG;
extern const uint64_t BOOL_TAG;
extern const uint64_t TUP_TAG;
extern const uint64_t CLOS_TAG;
extern const uint64_t FWD_PTR_TAG;
extern const uint64_t SNAKE_VAL_TRUE;
extern const uint64_t SNAKE_VAL_FALSE;
extern const uint64_t NIL;
extern const uint64_t ALG_TAG;
extern const uint64_t ALG_MASK;
extern const uint64_t NONE;

typedef enum {
  Bool,
  Int,
  Tuple,
  Closure,
  FwdPtr,
  Algebraic
} snake_val_type_t;

snake_val_type_t determine_snake_val_type(snake_val_t val);
uint64_t snake_int_to_c_int(snake_val_t val);
char* sv_serialize(snake_val_t val);


#endif
