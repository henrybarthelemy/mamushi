#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "gc.h"
#include "snake.h"

extern uint64_t* STACK_BOTTOM;
extern uint64_t* FROM_S;
extern uint64_t* FROM_E;
extern uint64_t* TO_S;
extern uint64_t* TO_E;

snake_val_t printStack(snake_val_t val, uint64_t* rsp, uint64_t* rbp, snake_val_t num_args);
snake_val_t print(snake_val_t val);

void naive_print_heap(uint64_t* heap, uint64_t* heap_end) {
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for(uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1) {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t*)(*(heap + i)), *(heap + i));
  }
}

// Implement the functions below
void smarter_print_heap(uint64_t* from_start, uint64_t* from_end, uint64_t* to_start, uint64_t* to_end) {
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
  printf("In smarter_print_heap from space %p to %p and to space %p to %p", from_start, from_end, to_start, to_end);
  printf("From heap space: ");
  for(uint64_t i = 0; i < (uint64_t)(from_end - from_start); i += 1) {
    if (determine_snake_val_type(*(from_start + i)) != -1) {
      // this has a type so lets serialize it and print it
      printf("  %ld/%p: %p (%ld)\n", i, (from_start + i), (uint64_t*)(*(from_start + i)), sv_serialize(*(from_start + i)));
    } else {
      printf("  %ld/%p: %p (%ld)\n", i, (from_start + i), (uint64_t*)(*(from_start + i)), *(from_start + i));
    }
  }
  printf("To heap space: ");
  for(uint64_t i = 0; i < (uint64_t)(to_end - to_start); i += 1) {
    if (determine_snake_val_type(*(to_start + i)) != -1) {
      // this has a type so lets serialize it and print it
      printf("  %ld/%p: %p (%ld)\n", i, (to_start + i), (uint64_t*)(*(to_start + i)), sv_serialize(*(to_start + i)));
    } else {
      printf("  %ld/%p: %p (%ld)\n", i, (to_start + i), (uint64_t*)(*(to_start + i)), *(to_start + i));
    }
  }
}

/*
  Copies a Garter value from the given address to the new heap, 
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.  
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location 
    with a forwarding pointer to its new location
 */
/*
 * Sorry that we don't actually use snake_val_t here... which is probably the much better thing to do.
 * I could change the type signatures at some point, but honestly this works and so I'll leave it as a TODO for later :3
 */
uint64_t* copy_if_needed(uint64_t* garter_val_addr, uint64_t* heap_top) {
#ifdef DEBUG
  printf("Copying: %#018llx\n", garter_val_addr);
#endif
  snake_val_type_t garter_val_typ = determine_snake_val_type(*garter_val_addr);

  uint64_t* heap_thing_ptr;
  char is_fp;

  switch (garter_val_typ) {
    case Closure:

      // Untag SV
      heap_thing_ptr = (uint64_t*) (*garter_val_addr ^ CLOS_TAG);

      if (heap_thing_ptr == 0) {
        break;
      }

      // Check if it points to a forwarding ptr
      is_fp = (determine_snake_val_type(*heap_thing_ptr) == FwdPtr);

      if (!is_fp) {
        // Is not a forwarding ptr, therefore we need to copy over to the new heap

        // Get freevars number
        uint64_t free_vars_count = *(heap_thing_ptr + 3) >> 1;

        // The total number of words in the closure
        uint64_t words = free_vars_count + 4; // (arity | ptr | ptr | free_count | ... )
        
#ifdef DEBUG
        printf("Closure | FV#: %d | SZ: %d | WD: %d\n", free_vars_count, words, words * 8);
#endif

        // Copy the correct number of words to the new heap top
        memcpy(heap_top, heap_thing_ptr, words * 8);

        // Put the forwarding pointer in the place where it goes
        *heap_thing_ptr = (uint64_t) heap_top | FWD_PTR_TAG;

        uint64_t* new_heap_top = (uint64_t*) heap_top + words;
        // for each free var recurse DFS-wise
        for (int i = 0; i < free_vars_count; i += 1) {
          new_heap_top = copy_if_needed(heap_top + 4 + i, new_heap_top);
        }
         
        // Update the value on the stack to to the new location
        *garter_val_addr = (uint64_t) heap_top | CLOS_TAG;
        
        // returns new heap top
        return new_heap_top;
      } else {
        // Is a forwarding ptr, therefore, we can use the current tag to update the garter_val
        *garter_val_addr = (*heap_thing_ptr ^ FWD_PTR_TAG) | CLOS_TAG;
      }

      break;
    case Tuple:
      
      // Untag SV
      heap_thing_ptr = (uint64_t*) (*garter_val_addr ^ TUP_TAG);

      if (heap_thing_ptr == 0) {
        break;
      }

      // Check if it points to a forwarding ptr
      is_fp = (determine_snake_val_type(*heap_thing_ptr) == FwdPtr);

      if (!is_fp) {
        // Is not a forwarding ptr, therefore we need to copy over to the new heap

        // Get arity number
        uint64_t arity_count = *heap_thing_ptr >> 1;

        // The total number of words in the tup
        uint64_t words = arity_count + 1; // (arity | ... )
                                          //
#ifdef DEBUG
        printf("TUPLE | A#: %d | SZ: %d | WD: %d\n", arity_count, words, words * 8);
#endif

        // Copy the correct number of words to the new heap top
        memcpy(heap_top, heap_thing_ptr, words * 8);

        // Put the forwarding pointer in the place where it goes
        *heap_thing_ptr = (uint64_t) heap_top | FWD_PTR_TAG;

        uint64_t* new_heap_top = (uint64_t*) heap_top + words;
        // for each arity recurse DFS-wise
        for (int i = 0; i < arity_count; i += 1) {
          new_heap_top = copy_if_needed(heap_top + 1 + i, new_heap_top);
        }
         
        // Update the value on the stack to to the new location
        *garter_val_addr = (uint64_t) heap_top | TUP_TAG;
        
        // returns new heap top
        return new_heap_top;
      } else {
        // Is a forwarding ptr, therefore, we can use the current tag to update the garter_val
        *garter_val_addr = (*heap_thing_ptr ^ FWD_PTR_TAG) | TUP_TAG;
      }

      break;
    case Algebraic:
      // Untag SV
      heap_thing_ptr = (uint64_t*) (*garter_val_addr ^ ALG_TAG);

      // none type
      if (heap_thing_ptr == 0) {
        break;
      }

      // Check if it points to a forwarding ptr
      is_fp = (determine_snake_val_type(*heap_thing_ptr) == FwdPtr);

      if (!is_fp) {
        // Is not a forwarding ptr, therefore we need to copy over to the new heap

        // Get tuple tag
        uint64_t var_tag = *heap_thing_ptr >> 1;
        uint64_t typ_tag = *(heap_thing_ptr + 1) >> 1;
        uint64_t assoc = *(heap_thing_ptr + 2) >> 1;

        uint64_t words = 3 * 8;
#ifdef DEBUG
        printf("ALGEBRAIC | VT: %d | TT: %d | AS: %d\n", var_tag, typ_tag, assoc);
#endif

        // Copy the correct number of words to the new heap top
        memcpy(heap_top, heap_thing_ptr, words);

        // Put the forwarding pointer in the place where it goes
        *heap_thing_ptr = (uint64_t) heap_top | FWD_PTR_TAG;

        uint64_t* new_heap_top = (uint64_t*) heap_top + words;
        new_heap_top = copy_if_needed(heap_top + 2, new_heap_top);
         
        // Update the value on the stack to to the new location
        *garter_val_addr = (uint64_t) heap_top | ALG_TAG;
        
        // returns new heap top
        return new_heap_top;
      } else {
        // Is a forwarding ptr, therefore, we can use the current tag to update the garter_val
        *garter_val_addr = (*heap_thing_ptr ^ FWD_PTR_TAG) | ALG_TAG;
      }

      break;

    default:
    return heap_top;
  }

  return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t* gc(uint64_t* bottom_frame, uint64_t* top_frame, uint64_t* top_stack, uint64_t* from_start, uint64_t* from_end, uint64_t* to_start) {

  uint64_t* top_frame_init = top_frame;
  uint64_t* top_stack_init = top_stack;

#ifdef DEBUG
  printStack(0x0, top_stack_init, top_frame_init, 0);
  printf("-------------------------------\n");
  naive_print_heap(FROM_S, FROM_E);
  printf("\n-------------------------------\n");
#endif

  uint64_t* to_start_init = to_start;

  uint64_t* old_top_frame = top_frame;
  do {
    /* Goes over saved regs. stupid calling convention :P */
    for (uint64_t* reg_word = top_stack; reg_word < top_stack + 4; reg_word++) {
      to_start = copy_if_needed(reg_word, to_start);
    }

    /*
     * We... need to figure out where RSP will be when we call GC
     */
    for (uint64_t* cur_word = top_stack + 1 + 4; cur_word < top_frame; cur_word++) {
      // print((snake_val_t) *cur_word);
      to_start = copy_if_needed(cur_word, to_start);
    }

    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * The next 4 are saved regs
     * [top_frame + 56] is the return address
     */
    top_stack = top_frame + 1;
    old_top_frame = top_frame;
    top_frame = (uint64_t*)(*top_frame);
    /*
     * We want this loop to run when top_frame == bottom_frame, but not after.
     * When top_frame == bottom frame, old_top_frame will less than bottom frame.
     * At then end of collecting the bottom-most frame, old_top_frame will then equal top_frame, and we want the loop to stop
     * Therefore < is correct
     */
  } while (old_top_frame < bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do
                                          
#ifdef DEBUG
  printStack(0x0, top_stack_init, top_frame_init, 0);
  printf("\n-------------------------------\n");
  naive_print_heap(to_start_init, to_start);
  printf("\n-------------------------------\n\n\n\n\n");
#endif

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return to_start;       
}

