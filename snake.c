#include "snake.h"

extern uint64_t* type_lookup[];

// All of the important constants related to our snake values 
const uint64_t NUM_MASK     = 0x0000000000000001;
const uint64_t BOOL_MASK    = 0x000000000000000F;
const uint64_t TUP_MASK     = 0x0000000000000007;
const uint64_t CLOS_MASK    = 0x0000000000000007;
const uint64_t FWD_PTR_MASK = 0x0000000000000007;
const uint64_t NUM_TAG      = 0x0000000000000000;
const uint64_t BOOL_TAG     = 0x000000000000000F;
const uint64_t TUP_TAG      = 0x0000000000000001;
const uint64_t CLOS_TAG     = 0x0000000000000005;
const uint64_t FWD_PTR_TAG  = 0x0000000000000003;
const uint64_t SNAKE_VAL_TRUE  = 0xFFFFFFFFFFFFFFFF;
const uint64_t SNAKE_VAL_FALSE = 0x7FFFFFFFFFFFFFFF;
const uint64_t NIL         = ((uint64_t)NULL | TUP_TAG);
const uint64_t ALG_TAG      = 0x0000000000000007;
const uint64_t ALG_MASK      = 0x000000000000000F;
const uint64_t NONE         = ((uint64_t)NULL | ALG_TAG);


// Determines the type the snake value is based on the tag
snake_val_type_t determine_snake_val_type(snake_val_t val) {
    if (((val & NUM_MASK) ^ NUM_TAG) == 0) {
       return Int;
    } else if (((val & BOOL_MASK) ^ BOOL_TAG) == 0) {
       return Bool;
    }  else if (((val & TUP_MASK) ^ TUP_TAG) == 0) {
      return Tuple;
    } else if (((val & CLOS_MASK) ^ CLOS_TAG) == 0) {
      return Closure;
    } else if (((val & FWD_PTR_MASK) ^ FWD_PTR_TAG) == 0) {
      return FwdPtr;
    } else if (((val & ALG_MASK) ^ ALG_TAG) == 0) {
      return Algebraic;
    }
 
    printf("Unknown type for value %010x\n", val);
    return -1;
 }
 
 // Converts the snake value, if it is an integer, to an integer
 uint64_t snake_int_to_c_int(snake_val_t val) {
   snake_val_type_t sv_type = determine_snake_val_type(val);
   if (sv_type == Int) {
     return val >> 1; 
   }
   printf("Some value that was not an Int was passed to the integer converted\n");
   return -1;
 }
 
 #define MAX_SNAKE_NAME_LENGTH 1024
 
 // Returns the stringified version of a snake value
 char* sv_serialize(snake_val_t val) {
   snake_val_type_t sv_type = determine_snake_val_type(val);
   char* str = malloc(sizeof(char) * MAX_SNAKE_NAME_LENGTH);
   uint64_t* tuple;
   uint64_t length;
   uint64_t* addr;
   switch (sv_type) {
     case Int:
       sprintf(str, "%d", snake_int_to_c_int(val));
       break;
     case Bool:
       if (val == SNAKE_VAL_TRUE) {
         sprintf(str, "true");
       } else if (val == SNAKE_VAL_FALSE) {
         sprintf(str, "false");
       } else {
         printf("Unknown boolean type found %010x\n", val);
       }
       break;
     case Tuple:
       tuple = (uint64_t*) (val - TUP_TAG);
       if (tuple == 0) {
         sprintf(str, "nil");
         break;
       }
       length = tuple[0] >> 1;
       if (length == 1) {
        // Since 1-tuples don't exist, this is the case of a single type in an algebric type
        strcat(str, sv_serialize(tuple[0]));
       } else {
        sprintf(str, "(");
        for (int i = 1; i <= length; i++) {
          strcat(str, sv_serialize(tuple[i]));
          if (i != length) {
            strcat(str, ", ");
          } else if (length == 1) {
            strcat(str, ",");
          }
        }
        strcat(str, ")");
       }
       break;
     case Closure:
       addr = (uint64_t*)(val - CLOS_TAG);
       // To allow for determinism in printing for tests we print just the arity
       sprintf(str, "<function arity %ld>", addr[0] >> 1);
       
       // some of this commented-out code may be useful for debugging purposes
       // sprintf(str, "[%p - 5] ==> <function arity %ld, closed %ld, fn-ptr %p>",
       //         (uint64_t*)val, addr[0] / 2, addr[1] / 2, (uint64_t*)addr[2]);
 
       /* fprintf(out, "\nClosed-over values:\n"); */
       /* for (uint64_t i = 0; i < addr[1] / 2; i++) { */
       /*   if (i > 0) { fprintf(out, "\n"); } */
       /*   if ((addr[3 + i] & TUPLE_TAG_MASK) == 5) { */
       /*     fprintf(out, "<closure %p>", (uint64_t*)addr[3 + i]); */
       /*   } else { */
       /*     printHelp(out, addr[3 + i]); */
       /*   } */
       /* } */
     
       break;
     case Algebraic:
       addr = (uint64_t*)(val - ALG_TAG);
       if (addr == 0) {
         // We should probably never get here
         sprintf(str, "");
         break;
       }

       uint64_t v_tag = addr[0] >> 1;
       uint64_t t_tag = addr[1] >> 1;

       char* name = (char *) type_lookup[t_tag][v_tag];

       uint64_t assoc = addr[2];

       sprintf(str, "%s", name);
       if (assoc != NONE) {
         strcat(str, "(");
         strcat(str, sv_serialize(assoc));
         strcat(str, ")");
       }

       break;
     default:
       printf("Unknown type found %010x\n", val);
   }
   return str;
 }
