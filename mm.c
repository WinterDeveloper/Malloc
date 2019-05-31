/*
 ******************************************************************************
 *                                   mm.c                                     *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                              name:Siyu Zhang                               *
 *                              andrew id:siyuz2                              *
 *  ************************************************************************  *
 * mm: A program which imitates malloc, free realloc, calloc function in c    *
 * program.It can allocate space and free space according to function         *
 * arguments.In this program,it uses boundary tags, segregated lists, first   *
 * fit and FIFO policy.In block design,each block contains a header, two      *
 * pointers which consist doubly list,and a pointer points to payload ,least  *
 * significant bit represents status of current block, the second least       *
 * significant bit represents status of previous block and the third least    *
 * significant bit represents whether previous block is 16 bytes.If block size* 
 * if 16 bytes, block will only keep header and next pointer,using third least* 
 * significant bit.                                                           *
 ******************************************************************************
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>
#include <unistd.h>
#include <inttypes.h>
#include "mm.h"
#include "memlib.h"
/* Do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */
/* You can change anything from here onward */
/*
 * If DEBUG is defined (such as when running mdriver-dbg), these macros
 * are enabled. You can use them to print debugging output and to check
 * contracts only in debug mode.
 *
 * Only debugging macros with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...)     printf(__VA_ARGS__)
#define dbg_requires(expr)  assert(expr)
#define dbg_assert(expr)    assert(expr)
#define dbg_ensures(expr)   assert(expr)
#define dbg_printheap(...)  print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...)     (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr)  (sizeof(expr), 1)
#define dbg_assert(expr)    (sizeof(expr), 1)
#define dbg_ensures(expr)   (sizeof(expr), 1)
#define dbg_printheap(...)  ((void) sizeof(__VA_ARGS__))
#endif
/* Basic constants */
typedef uint64_t word_t;
// Word and header size (bytes)
static const size_t wsize = sizeof(word_t);
// Double word size (bytes)
static const size_t dsize = 2 * wsize;
// Minimum block size (bytes)
static const size_t min_block_size = dsize;
// every time we need new heap space,we will add chunksize bytes space to our old heap
// (Must be divisible by dsize)
static const size_t chunksize = (1 << 14);
// using this mask to get least significant bit of header to find out block's status
static const word_t alloc_mask = 0x1;
//using this mask to get status of previous block
static const word_t prev_alloc_mask = 0x2;
// using this mask to find out block size
static const word_t size_mask = ~(word_t)0xF;
//using this mask to find out whether size of previous block is dsize(16bytes)
static const word_t dsize_mask = 0x4;
//num of free lists
static const size_t NUM = 12;
/* Represents the header and payload of one block in the heap */
typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    
    union {
        struct {
            struct block* next;
            struct block* prev;
        } st;
        char payload[0];
    } u;
    
} block_t;
//free list start block
static block_t* root[NUM];
//free list end block
static block_t* leaf[NUM];


/* Global variables */
// Pointer to first block
static block_t *heap_start = NULL;
/* Function prototypes for internal helper routines */
bool mm_checkheap(int lineno);
bool check_pro_and_epi();
bool check_size(block_t* block);
bool check_address_alignment(block_t* block);
bool check_consistency(block_t* block);
bool check_free_lists();
bool check_dsize_free_lists();

static block_t *extend_heap(size_t size);
static block_t *find_fit(size_t asize);
static block_t *find_dsize_fit(size_t asize);
static block_t *coalesce_block(block_t *block);
static void split_block(block_t *block, size_t asize);
static size_t max(size_t x, size_t y);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void my_write_header(block_t *block, size_t size, bool prev_dsize_or_not, bool prev_alloc, bool alloc);
static void my_write_footer(block_t *block, size_t size, bool prev_dsize_or_not, bool prev_alloc, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static word_t *header_to_footer(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

//manage free lists
static void initialize_list(block_t** root, block_t** leaf, block_t* block);
static bool delete_block_from_list(block_t* block);
static bool delete_dsize_free_block(block_t* block);
static bool add_new_free_block(block_t* block);
static bool add_dsize_free_block(block_t* block);
static int find_free_list(size_t size);

static size_t my_round_up(size_t size,size_t n);
static word_t my_pack(size_t size, bool prev_dsize_or_not, bool alloc_prev, bool alloc);

static unsigned get_address(char* pl);
/*
 * this function will initialize all data structure,extend heap space and set prologue and
 * epilogue
 * if this function initialize successfully,it will return true,otherwise false;
 * this function will only be used when heap_start is null.
 */
bool mm_init(void)
{  
    word_t *start = (word_t *) (mem_sbrk(2 * wsize));
    
    if (start == (void *)-1)
    {
        return false;
    }
    
    /*
     * we can use prologue and epilogue to find the end and start of our heap
     * once we find there is a block whose size is zero we will know that.Also,
     * since we set their alloc as true,it will not influence our coalescing and splitting 
     * and so on.
     */
    
    start[0] = my_pack(0, false, true, true);// Heap prologue (block footer)
    start[1] = my_pack(0, false, true, true);// Heap epilogue (block header)
    
    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *) &(start[1]);
    
    // Extend the empty heap with a free block of chunksize bytes
    block_t* block = extend_heap(chunksize);
    if (block == NULL)
    {
        return false;
    }
    //initialize free lists
    initialize_list(root, leaf, block);
    block->u.st.prev = NULL;
    block->u.st.next = NULL;
    return true;
}
/*
 * malloc will allocate a block
 */
void *malloc(size_t size)
{
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
    //asize = round_up(size + dsize, dsize);
    asize = my_round_up(size + wsize,dsize);
    
    // Search the free list for a fit
    block = find_fit(asize);
    
    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
        
    }
    bool prev_alloc = (block->header) & prev_alloc_mask;
    bool prev_dsize_or_not = (block->header) & dsize_mask;
    
    delete_block_from_list(block);
    
    // The block should be marked as free
    dbg_assert(!get_alloc(block));
    
    // Mark block as allocated
    size_t block_size = get_size(block);
    my_write_header(block, block_size, prev_dsize_or_not, prev_alloc, true);
    //so far we have finished this current block
    block_t* next_block = find_next(block);
    bool next_alloc = get_alloc(next_block);
    if(next_alloc){
        next_block->header = (next_block->header) | prev_alloc_mask;
    }
    else{
        next_block->header = (next_block->header) | prev_alloc_mask;
        size_t next_size = get_size(next_block);
        if(next_size != dsize){
            word_t* footerp_next = header_to_footer(next_block);
            *footerp_next = next_block->header;
        }
    }
    
    // Try to split the block if too large
    split_block(block, asize);
    
    bp = header_to_payload(block);
    
    /* TODO: Can you write a postcondition about the alignment of bp? */
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}
/*
 * free: set one allocated block as free
 */
void free(void *bp)
{
    dbg_requires(mm_checkheap(__LINE__));
    
    if (bp == NULL)
    {
        return;
    }
    
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    
    // The block should be marked as allocated
    dbg_assert(get_alloc(block));
    
    bool prev_alloc = (block->header) & prev_alloc_mask;
    bool prev_dsize_or_not = (block->header) & dsize_mask;
    
    // Mark the block as free
    my_write_header(block, size, prev_dsize_or_not, prev_alloc, false);
    if(size != dsize){
        my_write_footer(block, size, prev_dsize_or_not, prev_alloc, false);
    }
    add_new_free_block(block);
    //so far we have finished current block
    //deal with next block
    block_t* next_block = find_next(block);
    bool next_alloc = get_alloc(next_block);
    if(next_alloc){
        next_block->header = (next_block->header) & (~prev_alloc_mask);
    }
    else{
        next_block->header = (next_block->header) & (~prev_alloc_mask);
        size_t next_size = get_size(next_block);
        if(next_size != dsize){
            word_t* footerp_next = header_to_footer(next_block);
            *footerp_next = (*footerp_next) & (~prev_alloc_mask);
            *footerp_next = next_block->header;
        }
        
    }

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    
    dbg_ensures(mm_checkheap(__LINE__));
}
/*
 * returns a pointer to an allocated region of at least size bytes.if pointer is NULL 
 * the call is equivalent to malloc(size),if size is equal to zero, the call is
 * equivalent to free(ptr) and should return NULL.Otherwise,it must have been returned by an 
 * earlier call to malloc or realloc and not yet have been freed.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;
    
    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }
    
    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }
    
    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }
    
    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);
    
    // Free the old block
    free(ptr);
    
    return newptr;
}
/*
 * Allocates memory for an array of nmemb elements of size bytes each 
 * and returns a pointer to the allocated memory. The memory is set to zero before returning.
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;
    
    if (asize/elements != size)
    {
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    
    // Initialize all bits to 0
    memset(bp, 0, asize);
    
    return bp;
}
/******** The remaining content below are helper and debug routines ********/
/*
 * extend_heap:extend heap size given argument size.
 * return value:pointer points to first block in extended part
 */
static block_t *extend_heap(size_t size)
{
    void *bp;
    word_t* epi = (word_t*) (mem_heap_hi()-wsize + 1);
    bool prev_alloc = (*epi) & prev_alloc_mask;
    bool prev_dsize_or_not = (*epi) & dsize_mask;
    
    // Allocate an even number of words to maintain alignment
    size = my_round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    /*
     * bp represent payload of a block,so if we want to get block we need to find header
     */
    
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    my_write_header(block, size, prev_dsize_or_not, prev_alloc, false);
    my_write_footer(block, size, prev_dsize_or_not, prev_alloc, false);
    add_new_free_block(block);
    
    // Create new epilogue header
    block_t *block_next = find_next(block);

    my_write_header(block_next, 0, false, false, true);
    
    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    
    return block;
}
/*
 * coalesce function will work if we have two continuous free blocks ,this might happen 
 * when we free an allocated block.The return value if a pointer points to coalesced 
 * block
 * This function will only be called when argument block is free.
 */
static block_t *coalesce_block(block_t *block)
{
    dbg_requires(!get_alloc(block));
    
    size_t size = get_size(block);
    
    /*
     * we need to know status of next block and prev block
     */
    
    block_t *block_next = find_next(block);
    //block_t *block_prev = find_prev(block);
    block_t *block_prev;
    
    //bool prev_alloc = extract_alloc(*find_prev_footer(block));
    bool prev_alloc = (block->header) & prev_alloc_mask;
    bool next_alloc = get_alloc(block_next);
    bool prev_dsize_or_not = (block->header) & dsize_mask;
    
    if (prev_alloc && next_alloc)              // Case 1
    {
        // Nothing to do
    }
    
    else if (prev_alloc && !next_alloc)        // Case 2
    {
        block_t* next_next_block = find_next(block_next);
        next_next_block->header = next_next_block->header & (~dsize_mask);
        //delete old free blocks
        delete_block_from_list(block);
        delete_block_from_list(block_next);
        size += get_size(block_next);
        bool temp = (block->header) & prev_alloc_mask;
        //rewrite new size
        my_write_header(block, size, prev_dsize_or_not, temp, false);
        my_write_footer(block, size, prev_dsize_or_not, temp, false);
        add_new_free_block(block);
    }
    
    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_next->header = block_next->header & (~dsize_mask);
        if(prev_dsize_or_not){
            block_prev = (block_t*) ((char *)block - dsize);
        }
        else{
            block_prev = find_prev(block);
        }
        //delete old free blocks
        delete_block_from_list(block);
        delete_block_from_list(block_prev);
        size += get_size(block_prev);
        bool temp = (block_prev->header) & prev_alloc_mask;
        bool tmp = (block_prev->header) & dsize_mask;
        //rewrite new size
        my_write_header(block_prev, size, tmp, temp, false);
        my_write_footer(block_prev, size, tmp, temp, false);
        block = block_prev;
        add_new_free_block(block);
    }
    
    else                                        // Case 4
    {
        block_t* next_next_block = find_next(block_next);
        next_next_block->header = next_next_block->header & (~dsize_mask);
        if(prev_dsize_or_not){
            block_prev = (block_t*) ((char *)block - dsize);
        }
        else{
            block_prev = find_prev(block);
        }
        //delete old free blocks
        delete_block_from_list(block_prev);
        delete_block_from_list(block);
        delete_block_from_list(block_next);
        size += get_size(block_next) + get_size(block_prev);
        bool temp = (block_prev->header) & prev_alloc_mask;
        bool tmp = (block_prev->header) & dsize_mask;
        //rewrite new size
        my_write_header(block_prev, size, tmp, temp, false);
        my_write_footer(block_prev, size, tmp, temp, false);
        block = block_prev;
        add_new_free_block(block);
    }
    
    dbg_ensures(!get_alloc(block));
    /* TODO: Can you write a postcondition about get_size(block)? */
    
    return block;
}
/*
 * if we use a too large block then many bytes of this block are wasted,so we 
 * need to split this allocated block into an allocated block and a free block.
 */
static void split_block(block_t *block, size_t asize)
{
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */
    
    size_t block_size = get_size(block);
    bool prev_alloc = (block->header) & prev_alloc_mask;
    bool prev_dsize_or_not = (block->header) & dsize_mask; 
    
    if ((block_size - asize) >= min_block_size)
    {
        block_t *block_next;
        bool block_dsize_or_not = false;
        my_write_header(block, asize, prev_dsize_or_not, prev_alloc, true);
        my_write_footer(block, asize, prev_dsize_or_not, prev_alloc, true);
        
        block_next = find_next(block);
        if(get_size(block) == dsize){
            block_dsize_or_not = true;
        }
        my_write_header(block_next, block_size - asize, block_dsize_or_not, true, false);
        my_write_footer(block_next, block_size - asize, block_dsize_or_not, true, false);
        add_new_free_block(block_next);
        block_t* block_next_next = find_next(block_next);
        bool next_next_alloc = get_alloc(block_next_next);
        if(next_next_alloc){
            block_next_next->header = (block_next_next->header) & (~prev_alloc_mask);
            if((block_size - asize) == dsize){
                block_next_next->header = block_next_next->header | dsize_mask;
            }
        }
        else{
            block_next_next->header = (block_next_next->header) & (~prev_alloc_mask);
            if((block_size - asize) == dsize){
                block_next_next->header = block_next_next->header | dsize_mask;
            }
            if(get_size(block_next_next) != dsize){
                word_t* footerp_next_next = header_to_footer(block_next_next);
                *footerp_next_next = block_next_next->header;
            }
        }
    }
    
    dbg_ensures(get_alloc(block));
}
/*
 * this function will search free lists and find the first block whose size is larger than
 * what we need.the return value is a pointer points to this block
 * <Are there any preconditions or postconditions?>
 */
static block_t *find_fit(size_t asize)
{
    int index = find_free_list(asize);
    while(index >= 0){
        if(index == NUM-1){
            block_t* temp =  find_dsize_fit(asize);
            if(temp == NULL){
                index -= 1;
                continue;
            }
            else{
                return temp;
            }
        }
        block_t *block = leaf[index];
        while(block != NULL){
            if(!get_alloc(block) && get_size(block) >= asize){
                return block;
            }
            block = block->u.st.prev;
        }
        index -= 1;
    }
    return NULL;
}
static block_t *find_dsize_fit(size_t asize){
    if(root[NUM-1] == NULL){
        return NULL;
    }
    else{
        return root[NUM-1];
    }
}
/*
 * this function is to check whether your heap satisfy requirements
 */
bool mm_checkheap(int line)
{
    /*
     * this function is to check whether your heap satisfy requirements
    */
    //check prologue and epilogue
    check_pro_and_epi();
    block_t* block = heap_start;
    while(get_size(block)){
        //check size
        check_size(block);
        //check address
        check_address_alignment(block);
        //check consistency
        check_consistency(block);
        block = find_next(block);
    }
    check_free_lists();
    return true;
    
}
/*
* check_consistency:check whether adjacent blocks such as adjacent free blocks and bits indications are wrong
*/
bool check_consistency(block_t* block){
    block_t* next = find_next(block);
    size_t size = get_size(block);
    bool alloc = get_alloc(block);
    bool dsize_or_not = (size==dsize);
    bool next_alloc = get_alloc(next);
    bool next_indic_alloc = (next->header) & prev_alloc_mask;
    bool next_indic_dsize = (next->header) & dsize_mask;
    if((!alloc) && (!next_alloc)){
        dbg_printf("adjacent free blocks!!!");
        return false;
    }
    if(alloc != next_indic_alloc){
        dbg_printf("prev alloc is wrong!!!");
        return false;
    }
    if(dsize_or_not != next_indic_dsize){
        dbg_printf("prev adsize_or_not is wrong!!!");
        return false;
    }
    return true;
}
/*
* check_address_alignment:check whether payload address is a multiple of 16 
*/
bool check_address_alignment(block_t* block){
    char* pl = block->u.payload;
    unsigned address = get_address(pl);
    if(address & 0xf){
        dbg_printf("payload is not a multiple of 16!!!");
        return false;
    }
    return true;
}
/*
* check_size:check whether size is a multiple of 16 
*/
bool check_size(block_t* block){
    size_t size = get_size(block);
    if(size & 0xf){
        dbg_printf("Block size is not a multiple of 16!!!");
        return false;
    }
    if(size == dsize){
        block_t* next = find_next(block);
        bool temp = (next->header) & dsize_mask;
        if(!temp){
            dbg_printf("16 bytes's next block does not set!!!");
            return false;
        }
    }
    return true;
}
/*
* check_pro_and_epi: check whether epologue and prologue satisfy requirements
*/
bool check_pro_and_epi(){
    word_t* pro = (word_t*) mem_heap_lo();
    word_t* epi = (word_t*) (mem_heap_hi()-wsize + 1);
    //check prologue
    if(*pro != 0x3){
        dbg_printf("The prologue is wrong!!!");
        return false;
    }
    if(extract_size(*epi) != 0){
        dbg_printf("The epilogue is not 0!!!");
        return false;
    }
    if(extract_alloc(*epi) != true){
        dbg_printf("The epilogue is not allocated!!!");
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
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}
/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}
/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}
/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static size_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    //return asize - dsize;
    return asize - wsize;
}
/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool) (word & alloc_mask);
}
/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}
/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    return (block_t *) ((char *) block + get_size(block));
}
/*
 * find_prev_footer: returns the footer of the previous block.
 * it will only be used when block is free
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}
/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *) ((char *) block - size);
}
/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *) ((char *) bp - offsetof(block_t, u.payload));
}
/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *) (block->u.payload);
}
/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer.
 */
static word_t *header_to_footer(block_t *block)
{
    return (word_t *) (block->u.payload + get_size(block) - dsize);
}
/*
 *this function will add a new free block to the free list ,we always add it as 
 * the new root.the return value is true if we add this free block successfully,
 * otherwise false;
*/
static bool add_new_free_block(block_t* block){
    //FIFO
    if(block == NULL){
        return false;
    }
    size_t size = get_size(block);
    int index = find_free_list(size);
    if(index == NUM-1){
        add_dsize_free_block(block);
        return true;
    }
    if(root[index] == NULL){
        root[index] = block;
        leaf[index] = block;
        block->u.st.next = NULL;
        block->u.st.prev = NULL;
    }
    else{
        block_t* temp = root[index];
        root[index] = block;
        block->u.st.next = temp;
        block->u.st.prev = NULL;
        temp->u.st.prev = block;
    }
    return true;
}
/*
* add_dsize_free_block: given block ,add it as first block of free list.This function 
* will only be called when block is 16 bytes.In this case,free list is single list.
*/
static bool add_dsize_free_block(block_t* block){
    int index = NUM - 1;
    if(root[index] == NULL){
        root[index] = block;
        leaf[index] = block;
        block->u.st.next = NULL;
    }
    else{
        block->u.st.next = root[index];
        root[index] = block;
    }
    return true;
}
/*
 *this function will delete a free block if this free block get picked and set as allocated
 *the return value is true if we delete this free block successfully,otherwise false;
*/
static bool delete_block_from_list(block_t* block){
    size_t size = get_size(block);
    int index = find_free_list(size);
    if(index == NUM - 1){
        delete_dsize_free_block(block);
        return true;
    }
    if((block == NULL) || (root[index] == NULL)){
        return false;
    }
    block_t* next = block->u.st.next;
    block_t* prev = block->u.st.prev;
    if((next == NULL) && (prev == NULL)){
        //it is root
        root[index] = NULL;
        leaf[index] = NULL;
    }
    else if((next != NULL) && (prev == NULL)){
        root[index] = next;
        next->u.st.prev = NULL;
    }
    else if((next == NULL) && (prev != NULL)){
        prev->u.st.next = next;
        leaf[index] = prev;
    }
    else{
        prev->u.st.next = next;
        next->u.st.prev = prev;
    }
    return true;
}
/*
* delete_dsize_free_block: given block ,delete it from free list.This function will only
* be called when block is 16 bytes.In this case,free list is single list
*/
static bool delete_dsize_free_block(block_t* block){
    if(block == root[NUM-1]){
        if(root[NUM-1] == leaf[NUM-1]){
            root[NUM-1] = NULL;
            leaf[NUM-1] = NULL;
        }
        else{
            root[NUM-1] = root[NUM-1]->u.st.next;
        }
    }
    else{
        block_t* temp = root[NUM-1];
        block_t* tmp = temp->u.st.next;
        while(tmp != NULL){
            if(tmp==block){
                block_t* blk = tmp->u.st.next;
                temp->u.st.next = blk;
                if(blk == NULL){
                    leaf[NUM-1] = temp;
                }
                return true;
            }
            temp = tmp;
            tmp = tmp->u.st.next;
        }
    }
    return true;
}
/*
 * my_round_up: if size is less than wsize then return dsize,otherwise due to existence of 
 * two pointers,the least size of one block is 32 bytes
 */
static size_t my_round_up(size_t size,size_t n){
    if(size <= dsize){
        return dsize;
    }
    else{
        size_t result = n * ((size + (n-1))/n);
        return result;
    }
}
/*
 * my_pack: returns a header reflecting a specified size, its alloc status and status of 
 *          its previous block
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.If its previous 
 *       block is allocated, the second lowest bit is set to 1 ,and 0 otherwise.If the previous 
 *       block is 16 bytes then the third lowest bit is set to 1.
 */
static word_t my_pack(size_t size, bool prev_dsize_or_not, bool alloc_prev, bool alloc){
    word_t t_3 = 0x0;
    word_t t_2 = 0x0;
    word_t t_1 = 0x0;
    if(prev_dsize_or_not){
        t_3 = dsize_mask;
    }
    if(alloc_prev){
        t_2 = prev_alloc_mask;
    }
    if(alloc){
        t_1 = 0x1;
    }
    size = ((size | t_3) | t_2) | t_1;
    return size;
}
/*
 *my_write_header: given a block and its size and allocation status and status of its 
 *                 previous block
 *               writes an appropriate value to the block header.
*/
static void my_write_header(block_t *block, size_t size, bool prev_dsize_or_not, bool prev_alloc, bool alloc){
    dbg_requires(block != NULL);
    block->header = my_pack(size, prev_dsize_or_not, prev_alloc, alloc);
}
/*
 *my_write_footer: given a block and its size and allocation status and status of its 
 *                 previous block
 *               writes an appropriate value to the block footer
 *               this function is only used when block is free
*/
static void my_write_footer(block_t *block, size_t size, bool prev_dsize_or_not, bool prev_alloc, bool alloc){
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) == size && size > 0);
    word_t* footerp = header_to_footer(block);
    *footerp = my_pack(size, prev_dsize_or_not, prev_alloc, alloc);
}
/*
 *find_free_list:find corresponding free list according to block size
 *arguments:size of block
 *return value:offset of corresponding free list
*/
static int find_free_list(size_t size){
    if(size >= chunksize){
        return 0;
    }
    else if(size >= (chunksize>>1)){
        return 1;
    }
    else if(size >= (chunksize>>2)){
        return 2;
    }
    else if(size >= (chunksize>>3)){
        return 3;
    }
    else if(size >= (chunksize>>4)){
        return 4;
    }
    else if(size >= (chunksize>>5)){
        return 5;
    }
    else if(size >= (chunksize>>6)){
        return 6;
    }
    else if(size == (chunksize>>7)){
        return 7;
    }
    else if(size >= (chunksize>>8)){
        return 8;
    }
    else if(size == (chunksize>>8)-dsize){
        return 9;
    }
    else if(size == (chunksize>>8)-2*dsize){
        return 10;
    }
    else if(size == (chunksize>>8)-3*dsize){
        return 11;
    }
    else{
        return -1;
    }
}
/*
 *initialize_list:initialize free lists.
 *arguments:root:an array of pointers which are first blocks of free lists
 *          leaf:an array of pointers which are last blocks of free lists
 *          block:return value of function extend_heap
 * return value:none
*/
static void initialize_list(block_t** root, block_t** leaf, block_t* block){
    root[0] = block;
    leaf[0] = block;
    size_t index;
    for(index = 1;index < NUM; index++){
        root[index] = NULL;
        leaf[index] = NULL;
    }
    return;
}
/*
 *check_free_lists:check free blocks in free lists
 *arguments:root:start block
 * return value:if every block in free lists satisfy requirements ,return true ,false otherwise.
*/
bool check_free_lists(){
    size_t index = NUM - 1;
    while(index >= 0){
        if(index == NUM - 1){
            check_dsize_free_lists();
        }
        else{
            block_t* begin = root[index];
            while(begin != NULL){
                if(get_alloc(begin)){
                dbg_printf("there is allocated block in free list!!!");
                return false;
                }
                block_t* next = begin->u.st.next;
                if(next != NULL){
                    block_t* next_prev = next->u.st.prev;
                    if(begin != next_prev){
                        dbg_printf("link list is not right!!!");
                        return false;
                    }
                }
                begin = next;
            }
        }
        index -= 1;
    }
    return true;
}
/*
 *check_dsize_free_lists:check singly free list
*/
bool check_dsize_free_lists(){
    size_t index = NUM - 1;
    block_t* start = root[index];
    while(start != NULL){
        size_t size = get_size(start);
        if(size != dsize){
            dbg_printf("there is something weird in dsize free list!!!");
            return false;
        }
        if(get_alloc(start)){
            dbg_printf("there is allocated block in dsize free list!!!");
            return false;
        }
        if(start != root[index]){
            bool dsize_or_not = (start->header) & dsize_mask;
            if(!dsize_or_not){
                dbg_printf("dsize bit is wrong!!!");
                return false;
            }
        }
        start = start->u.st.next;
    }
    return true;
}
/*
 *get_address:given a pointer ,turn this pointer to an address
*/
static unsigned get_address(char* pl){
    union {
        unsigned address;
        char* pld;
    }u;
    u.pld = pl;
    return u.address;
}
