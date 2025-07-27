#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "gc.h"
#include "snake.h"


extern snake_val_t our_code_starts_here(uint64_t* HEAP, uint64_t size) asm("?our_code_starts_here");
extern void error(uint64_t errCode, snake_val_t val) asm("?error");
extern snake_val_t set_stack_bottom(uint64_t* stack_bottom) asm("?set_stack_bottom");
extern snake_val_t print(snake_val_t val) asm("print");
extern snake_val_t println(snake_val_t val) asm("println");
extern snake_val_t input_bool() asm("inputBool");
extern snake_val_t input_int() asm("inputInt");
extern snake_val_t printStack(snake_val_t val, uint64_t* rsp, uint64_t* rbp, snake_val_t num_args) asm("printStack");
extern snake_val_t equal(snake_val_t val1, snake_val_t val2) asm("equal");
extern uint64_t* try_gc(uint64_t* alloc_ptr, uint64_t amount_needed, uint64_t* first_frame, uint64_t* stack_top) asm("?try_gc");
extern uint64_t* HEAP_END asm("?HEAP_END");
extern uint64_t* HEAP asm("?HEAP");

extern uint64_t* type_lookup[];

const uint64_t ERR_COMP_NOT_NUM = 1;
const uint64_t ERR_ARITH_NOT_NUM = 2;
const uint64_t ERR_LOGIC_NOT_BOOL = 3;
const uint64_t ERR_IF_NOT_BOOL = 4;
const uint64_t ERR_OVERFLOW = 5;
const uint64_t ERR_GET_NOT_TUP = 6;
const uint64_t ERR_GET_LOW_IDX = 7;
const uint64_t ERR_GET_HIGH_IDX = 8;
const uint64_t ERR_NIL_DEREF = 9;
const uint64_t ERR_INPUT_INVALID = 10;
const uint64_t ERR_OUT_OF_MEMORY = 11;
const uint64_t ERR_SET_NOT_TUPLE = 12;
const uint64_t ERR_SET_LOW_INDEX = 13;
const uint64_t ERR_SET_NOT_NUM = 14;
const uint64_t ERR_SET_HIGH_INDEX = 15;
const uint64_t ERR_CALL_NOT_CLOSURE = 16;
const uint64_t ERR_CALL_ARITY_ERR = 17;
const uint64_t ERR_NO_MATCH = 18;

const uint64_t NUM_SAVED_REGS = 4;

size_t HEAP_SIZE;
uint64_t* STACK_BOTTOM;
uint64_t* HEAP;
uint64_t* HEAP_END;

snake_val_t set_stack_bottom(uint64_t* stack_bottom) {
  STACK_BOTTOM = stack_bottom;
  return 0;
}

uint64_t* FROM_S;
uint64_t* FROM_E;
uint64_t* TO_S;
uint64_t* TO_E;

// Completely ignores the file out and just prints, quick fix
void printHelp(FILE *out, snake_val_t val) {
  printf("%s\n", sv_serialize(val));
}

snake_val_t println(snake_val_t val) {
  printf("%s\n", sv_serialize(val));
  return val;
}

snake_val_t print(snake_val_t val) {
  printf("%s", sv_serialize(val));
  return val;
}

// Determines whether o1 is structural equal to o2
snake_val_t equal(snake_val_t val1, snake_val_t val2) {
  if (val1 == NIL || val2 == NIL) { return SNAKE_VAL_FALSE; }
  snake_val_type_t sv_type_1 = determine_snake_val_type(val1);
  snake_val_type_t sv_type_2 = determine_snake_val_type(val2);
  // might need to define these here
  if (sv_type_1 == sv_type_2) { // really cool version of instance of ig
    if (sv_type_1 == Bool || sv_type_1 == Int || sv_type_1 == Closure) {
      if (val1 == val2) { 
        // hurts a little to write this but technically we need to be returning the snake true not true
        return SNAKE_VAL_TRUE;
      } else {
        return SNAKE_VAL_FALSE;
      }
    } else if (sv_type_1 == Tuple) {
      // Tuple case :D lets recur
      uint64_t* tuple1 = (uint64_t*) (val1 - TUP_TAG);
      uint64_t* tuple2 = (uint64_t*) (val2 - TUP_TAG);
      if (tuple1 == 0 && tuple2 == 0) {
        return SNAKE_VAL_TRUE;
      } else if (tuple1 == 0 || tuple2 == 0) {
        return SNAKE_VAL_FALSE;
      }
      int64_t length1 = tuple1[0] >> 1;
      int64_t length2 = tuple2[0] >> 1;
      if (length1 != length2) {
        return SNAKE_VAL_FALSE;
      }
      for (int i = 1; i <= length1; i++) {
        if (equal(tuple1[i], tuple2[i]) == SNAKE_VAL_FALSE) {
          return SNAKE_VAL_FALSE;
        }
      }
      return SNAKE_VAL_TRUE;
    } else /* Algebraic type case */ {
      uint64_t* untag_v_1 = (uint64_t*) (val1 - ALG_TAG); 
      uint64_t* untag_v_2 = (uint64_t*) (val2 - ALG_TAG); 

      // nil, conveniently, also same tuple
      if(untag_v_1 == untag_v_2) {
        return SNAKE_VAL_TRUE;
      } else if ((uint64_t) untag_v_1 == NONE || (uint64_t) untag_v_2 == NONE) {
        return SNAKE_VAL_FALSE;
      }

      uint64_t v1_t_tag = *untag_v_1;
      uint64_t v2_t_tag = *untag_v_2;
      uint64_t v1_v_tag = *(untag_v_1 + 1);
      uint64_t v2_v_tag = *(untag_v_2 + 1);

      if (v1_t_tag == v2_t_tag) {
        if (v1_v_tag == v2_v_tag) {
          snake_val_t assoc1 = (snake_val_t) *(untag_v_1 + 2);
          snake_val_t assoc2 = (snake_val_t) *(untag_v_2 + 2);
          
          return equal(assoc1, assoc2);
        }
      }

      return SNAKE_VAL_FALSE;
    }
  } else {
    return SNAKE_VAL_FALSE;
  }
}

// TODO: abstract these

// Waits for user to input a boolean and returns it as a snake_val
snake_val_t input_bool() {
  int buffersize = 16;
  char input[buffersize]; 
  if (!fgets(input, buffersize, stdin)) {
    fprintf(stderr, "Input bool was not in a valid format, expected one of: true or false, and got ''");
    exit(ERR_INPUT_INVALID);
  }
  // remove \n character
  input[strcspn(input, "\n")] = '\0';  
  if (strcmp(input, "true") == 0) {
    return SNAKE_VAL_TRUE;
  } else if (strcmp(input, "false") == 0) {
    return SNAKE_VAL_FALSE;
  }
  fprintf(stderr, "Input bool was not in a valid format, expected one of: true or false, and got '%s'", input);
  exit(ERR_INPUT_INVALID);
}

// Waits for user to input an integer and returns it as a snake_val
snake_val_t input_int() {
  // need up to 20ish characters to write a 63 bit number, giving extra cuz we're generous
  int buffersize = 32;
  char input[buffersize]; 
  if (!fgets(input, buffersize, stdin)) {
    fprintf(stderr, "Input int was not in a valid format, expected an integer and got ''");
    exit(ERR_INPUT_INVALID);
  }
  // remove \n character
  input[strcspn(input, "\n")] = '\0';  
  char *endptr;
  uint64_t number = strtoull(input, &endptr, 10);
  if (!*endptr && *input) {
      return (number * 2);
  }
  fprintf(stderr, "Input int was not in a valid format, expected an integer and got '%s'", input);
  exit(ERR_INPUT_INVALID);
}


snake_val_t printStack(snake_val_t val, uint64_t* rsp, uint64_t* rbp, snake_val_t num_args) {
  printf("RSP: %#018llx\t==>  ", (uint64_t)rsp); fflush(stdout);
  printHelp(stdout, *rsp); fflush(stdout);
  printf("\nRBP: %#018llx\t==>  ", (uint64_t)rbp); fflush(stdout);
  printHelp(stdout, *rbp); fflush(stdout);
  printf("\n(difference: %lld)\n", (int64_t)(rsp - rbp)); fflush(stdout);
  printf("Requested return val: %#018llx\t==> ", (uint64_t)val); fflush(stdout);
  printHelp(stdout, val); fflush(stdout);
  printf("\n"); fflush(stdout);

  int64_t args = snake_int_to_c_int(num_args);
  printf("Num args: %lld\n", args);

  uint64_t* origRsp = rsp;

  if (rsp > rbp) {
    printf("Error: RSP and RBP are not properly oriented\n"); fflush(stdout);
  } else {
    for (uint64_t* cur = rsp; cur <= STACK_BOTTOM; cur++) {
      if (cur == STACK_BOTTOM) {
        printf("BOT %#018llx: %#018llx\t==>  old rbp 1\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == rbp) {
        printf("RBP %#018llx: %#018llx\t==>  old rbp 2\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == origRsp) {
        printf("    %#018llx: %#018llx\t==>  old rbp 3\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur <= (rbp + NUM_SAVED_REGS) && (cur > rbp)) {
        printf("    %#018llx: %#018llx\t==>  saved REG\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == (rbp + NUM_SAVED_REGS + 1)) {
        printf("    %#018llx: %#018llx\t==>  saved ret\n", (uint64_t)cur, *cur); fflush(stdout);
        rsp = rbp + 2;
        rbp = (uint64_t*)(*rbp);
      } else if (cur == STACK_BOTTOM + 2) {
        printf("    %#018llx: %#018llx\t==>  heap\n", (uint64_t)cur, *cur); fflush(stdout);
      } else {
        snake_val_type_t svt = determine_snake_val_type(*cur);
        if (svt == -1) {
          printf("    %#018llx: %#018llx\t==> ???", (uint64_t)cur, *cur); fflush(stdout);
          printf("\n"); fflush(stdout);
        } else {
          printf("    %#018llx: %#018llx\t==> %s", (uint64_t)cur, *cur, sv_serialize(*cur)); fflush(stdout);
          printf("\n"); fflush(stdout);
        }
      }
      // if (cur > rbp) break; // this is broken as is...
    }
  }
  return val;
}


void error(uint64_t errCode, snake_val_t val) {
const uint64_t ERR_OUT_OF_MEMORY = 11;
  switch (errCode) {
    case ERR_COMP_NOT_NUM:
      fprintf(stderr, "Comparison expected a number, but got %s\n", sv_serialize(val));
      break;

    case ERR_ARITH_NOT_NUM:
      fprintf(stderr, "Arithmatic expected a number, but got %s\n", sv_serialize(val));
      break;

    case ERR_IF_NOT_BOOL:
      fprintf(stderr, "If expected a bool condition, but got %s\n", sv_serialize(val));
      break;

    case ERR_LOGIC_NOT_BOOL:
      fprintf(stderr, "Logic expected a bool, but got %s\n", sv_serialize(val));
      break;

    case ERR_OVERFLOW:
      fprintf(stderr, "Arithmatic operation overflowed");
      break;

    case ERR_GET_NOT_TUP:
      fprintf(stderr, "Get expected a tuple, but got %s\n", sv_serialize(val));
      break;

    case ERR_GET_LOW_IDX:
      fprintf(stderr, "Tuple recieved a negative index, index too small");
      break;

    case ERR_GET_HIGH_IDX:
      fprintf(stderr, "Tried to access out of bounds index for tuple, index too large");
      break;

    case ERR_NIL_DEREF:
      fprintf(stderr, "Attempted to deref a Nil");
      break;
    
    case ERR_INPUT_INVALID:
      // This shouldn't really be called here but if it is handle that case.
      fprintf(stderr, "Input was not in a valid format");
      break;

    case ERR_CALL_NOT_CLOSURE:
      fprintf(stderr, "Call wasn't closure");
      break;
    
    case ERR_CALL_ARITY_ERR:
      fprintf(stderr, "Call had incorrect arity");
      break;

    case ERR_SET_NOT_TUPLE:
      fprintf(stderr, "Set expected a tuple, but got %s\n", sv_serialize(val));
      break;

    case ERR_SET_LOW_INDEX:
      fprintf(stderr, "Tuple set recieved a negative index, index too small");
      break;

    case ERR_SET_HIGH_INDEX:
      fprintf(stderr, "Tuple get recieved an out of bounds index, index to high");
      break;

    case ERR_SET_NOT_NUM:
      fprintf(stderr, "Tried to set a tuple index with a non-number index");
      break;

    case ERR_OUT_OF_MEMORY:
      fprintf(stderr, "Heap is out of memory");
      break;

    case ERR_NO_MATCH:
      fprintf(stderr, "Failed to match against a pattern");
      break;

    default:
      fprintf(stderr, "Got unknown error %010x (this should not happen)\n", val);
      break;
  }

  exit(errCode);
}


/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does 
  not actually allocate the desired number of bytes of memory; the caller 
  will do that.

  Arguments:

    uint64_t* alloc_ptr - the current top of the heap (which we store in R15), where
                          the next allocation should occur, if possible
    uint64_t bytes_needed - the number of bytes of memory we want to allocate
                            (including padding)
    uint64_t* cur_frame - the base pointer of the topmost stack frame of our code
                          (i.e., RBP)
    uint64_t* cur_stack_top - the stack pointer of the topmost stack frame of our
                              code (i.e., RSP)

  Returns:
    The new top of the heap (i.e. the new value of R15) after garbage collection.  
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP and HEAP_END to point to the new location of the heap
*/
uint64_t* try_gc(uint64_t* alloc_ptr, uint64_t bytes_needed, uint64_t* cur_frame, uint64_t* cur_stack_top) {
  uint64_t* new_heap = (uint64_t*)calloc(HEAP_SIZE + 15, sizeof(uint64_t));
  uint64_t* old_heap = HEAP;
  uint64_t* old_heap_end = HEAP_END;

  uint64_t* new_r15 = (uint64_t*)(((uint64_t)new_heap + 15) & ~0xF);
  uint64_t* new_heap_end = new_r15 + HEAP_SIZE;

  FROM_S = (uint64_t*)(((uint64_t)HEAP + 15) & ~0xF);
  FROM_E = HEAP_END;
  TO_S = new_r15;
  TO_E = new_heap_end;

  // printf("FROM_S = %p, FROM_E = %p, TO_S = %p, TO_E = %p\n", FROM_S, FROM_E, TO_S, TO_E);
  // naive_print_heap(FROM_S, FROM_E);
  /* printStack(BOOL_TRUE, cur_stack_top, cur_frame, 0); */

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection\n");
    fflush(stderr);
    if (old_heap != NULL) free(old_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
 
#ifdef DEBUG
  printf("GC to get %d bytes", bytes_needed);
#endif

  new_r15 = gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, HEAP_END, new_r15);
  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  // Note: strict greater-than is correct here: if new_r15 + (bytes_needed / 8) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / sizeof(uint64_t) > HEAP_SIZE) {
    fprintf(stderr, "Allocation error: needed %ld words, but the heap is only %ld words\n",
            bytes_needed / sizeof(uint64_t), HEAP_SIZE);
    fflush(stderr);
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else if((new_r15 + (bytes_needed / sizeof(uint64_t))) > HEAP_END) {
    fprintf(stderr, "Out of memory: needed %ld words, but only %ld remain after collection\n",
            bytes_needed / sizeof(uint64_t), (HEAP_END - new_r15));
    fflush(stderr);
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else {
    /* fprintf(stderr, "new_r15 = %p\n", new_r15); */
    /* naive_print_heap(HEAP, HEAP_END); */
    return new_r15;
  }
}

int main(int argc, char** argv) {
  HEAP_SIZE = 100000;
  if (argc > 1) { HEAP_SIZE = atoi(argv[1]); }
  if (HEAP_SIZE < 0 || HEAP_SIZE > 1000000) { HEAP_SIZE = 0; }
  HEAP = (uint64_t*)calloc(HEAP_SIZE + 15, sizeof(uint64_t));

  // uint64_t* heap2 = HEAP;

  uint64_t* aligned = (uint64_t*)(((uint64_t)HEAP + 15) & ~0xF);
  HEAP_END = aligned + HEAP_SIZE;
  /* printf("HEAP = %p, aligned = %p, HEAP_END = %p\n", HEAP, aligned, HEAP_END); */
  snake_val_t result = our_code_starts_here(aligned, HEAP_SIZE);
  /* smarter_print_heap(aligned, HEAP_END, TO_S, TO_E); */
  /* naive_print_heap(TO_S, TO_E);
  naive_print_heap(FROM_S, FROM_E); */
  println(result);

  // free(heap2);
  return 0;
}
