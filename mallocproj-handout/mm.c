/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first fit placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Blocks must be aligned to doubleword (8 byte)
 * boundaries. Minimum block size is 16 bytes.
 *
 *
 * In our constructed dynamic memory allocator, we use the size of the 
 * pointer --- "sizof(void *)", 
 * to define the size of a word. We also put "uintptr_t" into practice 
 * in order to define the unsigned integers.
 * We implement explicit free list with first fit.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
group_t group = {
    /* Project group number (You're required to join a group on Canvas) */
    "2",
    /* First member's full name */
    "LIU Junqi",
    /* First member's email address */
    "junqiliu2-c@my.cityu.edu.hk",
    /* Second member's full name */
    "TANG Junyi",
    /* Second member's email address (leave blank if none) */
    "junyitang2-c@my.cityu.edu.hk",
    /* Third member's full name */
    "FENG Chuxiao",
    /* Third member's email address */
    "chuxifeng2-c@my.cityu.edu.hk"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/*Pointer to get NEXT and PREVIOUS pointer of free_list*/ //my macros
#define NEXT_PTR(p)  (*(char **)(p + WSIZE))
#define PREV_PTR(p)  (*(char **)(p))

/* Global variables: */
static char *heap_listp = 0; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkheap(int verbose);
static void checkblock(void *bp);

/////////////////
static char* free_listp = 0; /* Pointer to first block in the free list */  
static void freeList_push(void* ptr);
static void freeList_pop(void* ptr);


/*
 * mm_init - Initialize the memory manager
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1) 
	return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /////////////////
    free_listp = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
	mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = 2*DSIZE;
    else
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
	place(bp, asize);
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *bp)
{
    if(bp == 0)
	return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
	mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    /* Pointer to first block */  
    bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
	freeList_push(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        freeList_pop(NEXT_BLKP(bp));
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        freeList_pop(PREV_BLKP(bp));
	bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        freeList_pop(PREV_BLKP(bp));
        freeList_pop(NEXT_BLKP(bp));
	bp = PREV_BLKP(bp);
    }
    freeList_push(bp);
    return bp;
}

/*
 * The remaining routines are internal helper routines
 */

/////////////////
static void freeList_push(void* ptr){
    NEXT_PTR(ptr) = free_listp;
    PREV_PTR(free_listp) = ptr;
    PREV_PTR(ptr) = NULL;
    free_listp = ptr;
}

/////////////////
static void freeList_pop(void* ptr){
    if(PREV_PTR(ptr) == NULL)
        free_listp = NEXT_PTR(ptr);
    else
        NEXT_PTR(PREV_PTR(ptr)) = NEXT_PTR(ptr);
    PREV_PTR(NEXT_PTR(ptr)) = PREV_PTR(ptr);
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        freeList_pop(bp);
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else {
        freeList_pop(bp);
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    /* First fit search */
    void *bp;

    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_PTR(bp)) {
	if (asize <= GET_SIZE(HDRP(bp)))
	    return bp;
    }
    return NULL; /* No fit */
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
	   hsize, (halloc ? 'a' : 'f'),
	   fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) 
{
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: The header does not meet with the footer\n");

    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);

}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose) 
{
    /*checks if blocks in free_list are actually free*/
    void*bp = free_listp;        
    while (NEXT_PTR(bp)!=NULL) {                       
           
      if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1) {
          printf("Come across an allocated block in the free list.\n");
          return;
      }                  
          bp = NEXT_PTR(bp);
    }

    if (verbose == 1)
	printf("Heap (%p): ", heap_listp);

    if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
        !GET_ALLOC(HDRP(heap_listp)))
	    printf("Bad p-header\n");
	checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose == 1)
	    printblock(bp);
	checkblock(bp);
    }

    if (verbose == 1)
	printblock(bp);
    if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
	printf("Bad e-header\n");

}

