
/** Andrew ID: xinyanzh,  Name: Xinyan Zhao **/

/* Header Comment:
*
*  I used the explicit and segregated free list to store and itentify free
*blocks.
*
*  For allocated block, I just need to make its "allocated" mask bit to be 1.
*And remove it from
*  free-block segregated list if needed.
*
*  For each free block, I used the union to bound the payload and two pointers,
*  incluing 1 prev-pointer for previous free block and 1 next-pointer for next
*free block. So is is a
*  duobly-linked structure.
*  If one free block has no previous or next free block, the pointer is set to
*be NULL(also default value).
*
*  I also use 1 segregated list to store free-block doubly links with different
*size-classes. Due to the
*  global data limitation, I set the segregated list with the size of 15, which
*could contain 15 doubly links at the maximum.
*  From link1 to link15, they contain free blocks with different size ranges.
*Link1(segregated[0]) contains only 2^5 btye free blocks,
*  Link2(segregated[1]) contains 2^5+1 to 2^6 btyes free blocks,
*link3(segregated[3]) contains 2^6+1 to 2^7 btyes free blocks, ect.
*
*  Each time when we want to find one fit free block, we need to calculate its
*index(of segregated-list) firstly, and search for
*  the fit block from that doubly link and afterwards. It is the same way when
*we remove one free block from the segregated list.
*
*  To increase its utilization, I also made some changes on footers to decrease
*inner fragmentation.
*  I only set footers to free blocks, since they need its information to
*coalesce. But I defuse footers for allocated block,
*  so they have more space for payload. In this case, in the header of each
*block, I add an extra bit for
*  recording the status of the previous block.
*
*/

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif

#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

// This is the size of my segregated list for free blocks
// Because of global data limitation, I set it to be 15 maximum
#define LISTMAX 15

typedef uint64_t word_t;
// Word and header size (bytes)
static const size_t wsize = sizeof(word_t);
// Double word size (bytes)
static const size_t dsize = 2 * wsize;
// Minimum block size (bytes)
static const size_t min_block_size = 2 * dsize;
static const size_t chunksize = (1 << 12);
// This is to indicate whether this block is allocated or free
static const word_t alloc_mask = 0x1;
// This is to indicate whether the previous block is allocated or free
static const word_t prev_alloc_mask = 0x2;
// This is used to do mask to get allocation flag
static const word_t size_mask = ~(word_t)0xF;

/* Represents the header and payload of one block in the heap */
typedef struct block {
  /* Header contains size + allocation flag */
  word_t header;
  union {
    // Allocated blocks use this area as payload
    // Free blocks use this area to store two pointers(next-free and
    // previous-free)
    struct free {
      struct block *prev;
      struct block *next;
    } free;
    char payload[0];
  };
} block_t;

/* Global variables */

// Pointer to first block
static block_t *heap_start = NULL;

/* Function prototypes for internal helper routines */

// This is segregated list to store free-block doubly links
static block_t *segregated_list[LISTMAX];
bool mm_checkheap(int lineno);

static block_t *extend_heap(size_t size);
static block_t *find_fit(size_t asize);
static block_t *coalesce_block(block_t *block);
static void split_block(block_t *block, size_t asize);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static word_t *header_to_footer(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static block_t *find_prev_free(block_t *block);
static block_t *find_prev_free_footer(block_t *block);
static block_t *find_next_free(block_t *block);

// These are used to add or reomove free blocks with the segregated list
static void insert_to_empty(block_t *block);
static void remove_from_empty(block_t *block);

// This is used to get segregated list index for certain free block
static int get_index(block_t *block);

// This is used to set previous block's status(free/allocated) to currrent
// block's header
static void write_prev_bit(block_t *block, bool alloc);
// This is used to get previous block's status(free/allocated) of the currrent
// block
static bool get_prev_alloc(block_t *block);

// This is used to print all existing blocks for me to debug
static void print();

/* Initialization function each time for running */
bool mm_init(void) {
  for (int i = 0; i < LISTMAX; i++) {
    segregated_list[i] = NULL;
  }
  // Create the initial empty heap
  word_t *start = (word_t *)(mem_sbrk(2 * wsize));

  if (start == (void *)-1) {
    return false;
  }
  start[0] = pack(0, true); // Heap prologue (block footer)
  start[1] = pack(0, true); // Heap epilogue (block header)

  // Heap starts with first "block header", currently the epilogue
  heap_start = (block_t *)&(start[1]);
  write_prev_bit(heap_start, true); // add the previous block's status to header

  // Extend the empty heap with a free block of chunksize bytes
  if (extend_heap(chunksize) == NULL) {
    return false;
  }
  return true;
}

/* Do malloc action overall */
void *malloc(size_t size) {
  dbg_requires(mm_checkheap(__LINE__));

  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  block_t *block;
  void *bp = NULL;

  if (heap_start == NULL) // Initialize heap if it isn't initialized
  {
    mm_init();
  }

  if (size == 0) // Ignore spurious request
  {
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  // Adjust block size to include overhead and to meet alignment requirements
  asize = round_up(size + wsize,
                   dsize); // allocated block don't need the footer space

  // Search the free list for a fit
  block = find_fit(asize);
  // If no fit is found, request more memory, and then and place the block
  if (block == NULL) {
    // Always request at least chunksize
    extendsize = max(asize, chunksize);
    block = extend_heap(extendsize);
    if (block == NULL) // extend_heap returns an error
    {
      return bp;
    }
  }

  // The block should be marked as free
  dbg_assert(!get_alloc(block));

  // Mark block as allocated
  size_t block_size = get_size(block);
  write_header(block, block_size, true);

  // this free block that found or extended(already coalesced) must has one
  // allocated previous block
  write_prev_bit(block, true);

  remove_from_empty(block); // remove this allocated block from free-list
  write_prev_bit(find_next(block),
                 true); // add its allocated status to next block

  // Try to split the block if too large
  split_block(block, asize);
  bp = header_to_payload(block);

  dbg_ensures(mm_checkheap(__LINE__));
  return bp;
}

/* Do free action overall */
void free(void *bp) {
  dbg_requires(mm_checkheap(__LINE__));

  if (bp == NULL) {
    return;
  }

  block_t *block = payload_to_header(bp);

  size_t size = get_size(block);
  dbg_assert(get_alloc(block));

  bool prev_alloc = get_prev_alloc(block); // get previous block's status

  // Mark the block as free
  write_header(block, size, false);
  write_footer(block, size, false); // free block also has footer

  write_prev_bit(block, prev_alloc);       // add previous block's status
  write_prev_bit(find_next(block), false); // add its status to next block

  // Try to coalesce the block with its neighbors if possible
  block = coalesce_block(block);

  dbg_ensures(mm_checkheap(__LINE__));
}

/* Do realloc action overall */
void *realloc(void *ptr, size_t size) {
  block_t *block = payload_to_header(ptr);
  size_t copysize;
  void *newptr;

  // If size == 0, then free block and return NULL
  if (size == 0) {
    free(ptr);
    return NULL;
  }

  // If ptr is NULL, then equivalent to malloc
  if (ptr == NULL) {
    return malloc(size);
  }

  // Otherwise, proceed with reallocation
  newptr = malloc(size);

  // If malloc fails, the original block is left untouched
  if (newptr == NULL) {
    return NULL;
  }

  // Copy the old data
  copysize = get_payload_size(block); // gets size of old payload
  if (size < copysize) {
    copysize = size;
  }
  memcpy(newptr, ptr, copysize);

  // Free the old block
  free(ptr);
  return newptr;
}

/* Do calloc action overall */
void *calloc(size_t elements, size_t size) {
  void *bp;
  size_t asize = elements * size;

  if (asize / elements != size) {
    // Multiplication overflowed
    return NULL;
  }
  bp = malloc(asize);
  if (bp == NULL) {
    return NULL;
  }

  // Initialize all bits to 0
  memset(bp, 0, asize);

  return bp;
}

/******** The remaining content below are helper and debug routines ********/

/* This function is used to extend the heap if no existing available free block
   for allocating.

   It should noted that for the newly extended block, its header just replace
   the original epilogue
   header, and it adds its payload(+footer) afterwards, then adds one new
   epilogue. Thus, for this
   new extended block, its previous block is same with the preivous block of
   original epilogue.
   So we could store its previous block's status at first from orginal epilogue
   before extending,
   and set it finally.
*/
static block_t *extend_heap(size_t size) {
  void *bp;

  // Allocate an even number of words to maintain alignment
  size = round_up(size, dsize);
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }

  // Initialize free block header/footer
  block_t *block = payload_to_header(bp);

  // store preivous block's status from orginal epilogue at fisrt
  bool prev_alloc = get_prev_alloc(block);
  write_header(block, size, false);
  write_footer(block, size, false);

  // add previous block's status
  write_prev_bit(block, prev_alloc);

  // Create new epilogue header
  block_t *block_next = find_next(block);
  write_header(block_next, 0, true);
  write_prev_bit(block_next, false); // its previous extended block must be free

  // Coalesce in case the previous block was free
  block = coalesce_block(block);
  return block;
}

/* This is used to coalesce adjacent free blocks if possible */
static block_t *coalesce_block(block_t *block) {
  dbg_requires(!get_alloc(block));

  size_t size = get_size(block);

  // get its previous block's status
  bool prev_alloc = get_prev_alloc(block);

  block_t *block_next = find_next(block);
  bool next_alloc = get_alloc(block_next);

  if (prev_alloc && next_alloc) // Case 1, previous & next: allocated
  {
    // Nothing to do
  } else if (prev_alloc && !next_alloc) // Case 2, only next free
  {
    remove_from_empty(block_next);
    size += get_size(block_next);
    write_header(block, size, false);
    write_footer(block, size, false);
  } else if (!prev_alloc && next_alloc) // Case 3, only previous free
  {
    block_t *block_prev = find_prev(block);
    remove_from_empty(block_prev);
    size += get_size(block_prev);
    write_header(block_prev, size, false);
    write_footer(block_prev, size, false);
    block = block_prev;
  } else // Case 4, both free
  {
    block_t *block_prev = find_prev(block);
    remove_from_empty(block_next);
    remove_from_empty(block_prev);
    size += get_size(block_next) + get_size(block_prev);
    write_header(block_prev, size, false);
    write_footer(block_prev, size, false);
    block = block_prev;
  }

  // insert this new free block to segregated list;
  insert_to_empty(block);
  write_prev_bit(block, true); // The previous block of this coalesces block
                               // must be allocated
  write_prev_bit(find_next(block), false);

  dbg_ensures(!get_alloc(block));

  return block;
}

/* This is used to split this allocated block if it is too large compared with
 * requested size */
static void split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc(block));
  bool prev_alloc = get_prev_alloc(block);
  size_t block_size = get_size(block);

  if ((block_size - asize) >= min_block_size) {
    block_t *block_next;
    write_header(block, asize, true);
    write_prev_bit(block, prev_alloc);

    block_next = find_next(block);
    // the spliting-left block is free
    write_header(block_next, block_size - asize, false);
    write_footer(block_next, block_size - asize, false);
    write_prev_bit(block_next, true); // its previous block must be allocated
    write_prev_bit(find_next(block_next), false);

    // Coalesce in case the next block was free
    coalesce_block(block_next);
  }
  dbg_ensures(get_alloc(block));
}

/* This is used to find oen fit free block for allocating */
static block_t *find_fit(size_t asize) {
  int index;

  // Calculate the segregated-list index for the wanted free block
  if (asize > (1 << (LISTMAX + 3))) {
    index = LISTMAX -
            1; // for too large block size, it must be in the last doubly link
  } else {
    index = 0;
    while (asize > (1 << (index + 5))) {
      index++;
    }
  }

  // Search for fit block starting from the calculated index
  while (index < LISTMAX) { // Continue to find until no more doubly links
    if (segregated_list[index] == NULL) {
      index++;
    } else {
      block_t *fit;
      for (fit = segregated_list[index]; fit != NULL; fit = fit->free.next) {
        if (asize <= get_size(fit)) { // If found, return that block
          return fit;
        }
      }
      index++;
    }
  }

  return NULL; // no fit found
}

/* This is used to get the segregated-list index for the wanted free block */
static int get_index(block_t *block) {
  int index;
  size_t size = get_size(block);
  if (size > (1 << (LISTMAX + 3))) {
    index = LISTMAX -
            1; // for too large block size, it must be in the last doubly link
  } else {
    index = 0;
    while (size > (1 << (index + 5))) {
      index++;
    }
  }
  return index;
}

/* This is used to remove any allocated block from the segregated list */
static void remove_from_empty(block_t *block) {
  int index = get_index(block); // get block's index in segregated list
  if (segregated_list[index] == NULL) {
    return;
  }
  block_t *prev_empty;
  block_t *next_empty;

  // get block's previous and next free block
  prev_empty = block->free.prev;
  next_empty = block->free.next;

  if (prev_empty == NULL &&
      next_empty == NULL) { // case1: This link only has 1 block (this block)
    segregated_list[index] = NULL; // set that link root to be NULL
  } else if (prev_empty == NULL) { // case2: This block is the root of the link
    next_empty->free.prev = NULL;
    block->free.next = NULL;
    segregated_list[index] = next_empty;
  } else if (next_empty == NULL) { // case3: This block is the end of the link
    prev_empty->free.next = NULL;
    block->free.prev = NULL;
  } else { // case4: This block is in the middle of the link
    prev_empty->free.next = next_empty;
    next_empty->free.prev = prev_empty;
    block->free.prev = NULL;
    block->free.next = NULL;
  }
}

/* This is used to add any new free block to the segregated list */
static void insert_to_empty(block_t *block) {
  int index = get_index(block);         // get block's index in segregated list
  if (segregated_list[index] == NULL) { // case1: that link has no block
    segregated_list[index] =
        block; // set this new free block to be root of that link
    block->free.prev = NULL;
    block->free.next = NULL;
    return;
  }
  block_t *root = segregated_list[index]; // case2: that link already has
                                          // blocks, get the root block
  root->free.prev = block;
  block->free.prev = NULL;
  block->free.next = root;
  segregated_list[index] =
      block; // insert the new free block at the start, to be the root
}

/* This is used to help check the some common and special errors of the
 * allocator and existing heap */
bool mm_checkheap(int line) {
  block_t *block;
  int index = 0;
  int free_traverse = 0; // count the free block number when traverse all blocks
  int free_segregated =
      0; // count the free block number when traverse the segregated list

  /* traverse all existing blocks */
  for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
    /* Check block address alignment */
    if ((int)header_to_payload(block) % 16 != 0) {
      printf("Block address doesn't satisfy 16-bytes alignment %p\n", block);
      return false;
    }
    /* Check for free blocks */
    if (!get_alloc(block)) {
      /* Check header and footer consistentcy */
      if (block->header != *(header_to_footer(block))) {
        printf("Inconsist header and footer in this block %p\n", block);
        return false;
      }

      free_traverse++; // Count free blocks in traversal

      /* Check two continous non-coalesced free blocks */
      if (find_next(block) &&
          !get_alloc(find_next(block))) // check with next block
      {
        printf(
            "Non-coalesced free block with its next adjacent free block %p\n",
            block);
        return false;
      }
      if (!get_prev_alloc(block)) // check with previous block
      {
        printf("Non-coalesced free block with its previous adjacent free block "
               "%p\n",
               block);
        return false;
      }
    }
    /* Check two block overlap */
    if (find_next(block) &&
        header_to_footer(block) > &(find_next(block)->header)) {
      printf("Overlap with its next adjacent block %p\n", block);
      return false;
    }
  }

  /* traverse the segregated list */
  while (index < LISTMAX) {
    if (segregated_list[index] == NULL) {
      index++; // continue to next doubly link
    } else {
      block_t *free;
      for (free = segregated_list[index]; free != NULL;
           free = free->free.next) {
        free_segregated++; // Count free block in segregated list
        /* check next/previous pointers are consistent */
        if (free->free.next != NULL) {
          if (free != free->free.next->free.prev) {
            printf("This free block's pointer isn't consistent with its next "
                   "pointing free block %p",
                   free);
            return false;
          }
        }
        /* check whether the free block(size) is in correct index group */
        if (index == 0 && get_size(free) != 32) { // when index=0, it only
                                                  // contains 32-bytes blocks
          printf("This free block (%p) size isn't within its segregated buket "
                 "size range",
                 free);
          return false;
        }
        if (index > 0 && (get_size(free) > (1 << (index + 5)) ||
                          get_size(free) < ((1 << (index + 4)) + 1))) {
          printf("This free block (%p) size isn't within its segregated buket "
                 "size range",
                 free);
          return false;
        }
      }
      index++;
    }
  }

  /* compare the free blocks' number in heap with that insegregated list */
  if (free_traverse != free_segregated) {
    printf("Different number of free blocks stored in segregated list %d with "
           "atcual number in heap %d ",
           free_segregated, free_traverse);
    return false;
  }
  return true;
}

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ba c1 e1 52 13 0a               *
 *                                                                           *
 *****************************************************************************
 */

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) { return (x > y) ? x : y; }

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n) {
  if (n * ((size + (n - 1)) / n) <
      32) { // it must have 32-bytes at least (for free case)
    return 32;
  }
  return n * ((size + (n - 1)) / n);
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc) {
  return alloc ? (size | alloc_mask) : size;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word) {
  return (word & size_mask);
} // total size including header (footer)

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block) { return extract_size(block->header); }

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block) {
  size_t asize = get_size(block);
  if (get_alloc(block)) {
    return asize - wsize; // allocated block has no footer space
  } else {
    return asize - dsize; // afree block wsize footer space
  }
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word) { return (bool)(word & alloc_mask); }

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block) { return extract_alloc(block->header); }

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc) {
  dbg_requires(block != NULL);
  block->header = pack(size, alloc);
}

/*
 * write_prev_bit: given a block and its size and its previous block's
 * allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_prev_bit(block_t *block, bool alloc) {
  if ((void *)block <= mem_heap_hi()) {
    if (alloc) { // write previous block's allocation status bit (2nd least
                 // significant bit in header)
      block->header = block->header | prev_alloc_mask;
    } else {
      block->header = block->header & (~prev_alloc_mask);
    }
    if (get_alloc(block) == false) { // also write to footer for free blocks
      word_t *footerp = header_to_footer(block);
      if (alloc) {
        *footerp = block->header | prev_alloc_mask;
      } else {
        *footerp = block->header & (~prev_alloc_mask);
      }
    }
  }
}

/*
 * print: print all existing blocks in the heap, including allocated and free
 * ones.
 */
static void print() {
  for (block_t *block = heap_start; get_size(block) > 0;
       block = find_next(block)) {
    printf("%" PRIx64 ": %p\n", block->header,
           block); // print the size of each block
  }
}

/*
 * get_prev_alloc: given a block, get its previous block's allocation status.
 */
static bool get_prev_alloc(block_t *block) {
  word_t head = block->header;
  // read previous allocation bit(2nd least significant bit in header)
  return (bool)(head & prev_alloc_mask);
}
/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer. Only for free blocks.
 */
static void write_footer(block_t *block, size_t size, bool alloc) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) == size && size > 0);
  word_t *footerp = header_to_footer(block);
  *footerp = pack(size, alloc);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);
  return (block_t *)((char *)block + get_size(block));
}

/*
 * find_prev_footer: returns the footer of the previous block.
 * Only if previous block is free.
 */
static word_t *find_prev_footer(block_t *block) {
  // Compute previous footer position as one word before the header
  return &(block->header) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size. Only if previous block is free.
 */
static block_t *find_prev(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);
  word_t *footerp = find_prev_footer(block);
  size_t size = extract_size(*footerp);
  return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp) {
  return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block) {
  return (void *)(block->payload);
}

/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer. Only if previous block is free.
 */
static word_t *header_to_footer(block_t *block) {
  return (word_t *)(block->payload + get_size(block) - dsize);
}
