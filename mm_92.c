/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG

#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (512)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define DDSIZE	    16      /* 2 times double word size */
#define TDSIZE      24      /* 3 times double word size*/

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

#define MASK (((unsigned long int)heap_listp & 0xffffffff00000000))
#define MASK_POINTER ((unsigned int *) MASK)

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define GET_POINTER(p) ((unsigned long int *)(*(unsigned long int *)(p)))

/*get pointer from address p*/
#define GET_POINTER_4BYTES(p) ((unsigned int *)((unsigned int long)(GET(p)+MASK)))
/*get pointer from address p+1 */
#define GET_POINTER_4BYTES_NXT(p) ((unsigned int *)(((unsigned int long)GET(((unsigned int *)(p))+1)) + MASK))
								
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  
#define PUT_POINTER(p,val) ((*(unsigned long int *)(p) = (unsigned long int) (val)))

#define PUT_POINTER_NULL(p)  ((*(unsigned int *)(p) = ((unsigned int)0))) 

/*Put 32bits address to location p*/
#define PUT_POINTER_4BYTES(p,val) (*(unsigned int *)(p) = ((unsigned int )(((unsigned long int)val)))) 
/*Put 32bits address to location p+1*/
#define PUT_POINTER_4BYTES_NXT(p,val) (*(((unsigned int *)(p))+1) = ((unsigned int )(((unsigned long int)val)))) 
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_BLKP_POINTER(bp)  (unsigned int *)((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP_POINTER(bp)  (unsigned int *)((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Read address of pointer by adding 64bit offset given address of pointer */
#define GET_PTR_VAL(p) ((char *)(GET(p) + MASK)

/*Define True or False*/
#define TRUE 1
#define FALSE 0
#define ALLOC 1
#define UNALLOC 0
/*Define how may segregated list we have*/

#define LISTNUMBER 15//list is from 0 to (LISTNUMBER-1)
#define INITIALVALUE 1000000
#define DIVIDESIZE 14
#define DIVIDVALUE 128

/* The only global variable is a pointer to the first block */
static unsigned char *heap_listp; 
static unsigned int min_minlist;
static unsigned int freelist_count;


/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void checkcoales(unsigned int *bp,unsigned int *bp_prev);
static int in_heap(const void *p); 
static int aligned(const void *p); 
static void add_freelist(unsigned int *bp);
static void remove_freelist(unsigned int *bp);



/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    unsigned int i = 0;
    /* create the initial empty heap */
    freelist_count=0;
    min_minlist=INITIALVALUE;
    if ((heap_listp = mem_sbrk((LISTNUMBER)*WSIZE+DDSIZE+(LISTNUMBER%2)*WSIZE)) == NULL)
        return -1;
   
    PUT(heap_listp, UNALLOC);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK((LISTNUMBER)*WSIZE+DSIZE+(LISTNUMBER%2)*WSIZE, ALLOC));  /* prologue header */
    for(i = 0;i < LISTNUMBER; i++)
    {
        PUT_POINTER_4BYTES(heap_listp+(i*WSIZE)+DSIZE,(unsigned int*) NULL);    /*initialize segregated first pointer*/
    }
    PUT(heap_listp+(LISTNUMBER*WSIZE)+DSIZE+(LISTNUMBER%2)*WSIZE, PACK((LISTNUMBER)*WSIZE+(LISTNUMBER%2)*WSIZE+DSIZE, ALLOC));  /* prologue footer */ 
    PUT(heap_listp+(LISTNUMBER+1)*WSIZE+DSIZE+(LISTNUMBER%2)*WSIZE, PACK(0, ALLOC));   /* epilogue header */
    heap_listp += DSIZE;

    
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

    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    unsigned int *bp;      


    /* Ignore spurious requests */
    if (size <=  0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DDSIZE;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
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
    if(bp!=NULL)
    {
        size_t size = GET_SIZE(HDRP(bp));

        PUT(HDRP(bp), PACK(size, UNALLOC));
        PUT(FTRP(bp), PACK(size, UNALLOC));
        coalesce(bp);
    }
}

/* Not implemented. For consistency with 15-213 malloc driver */

void *mm_realloc(void *oldptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    if(size==0)
    {
        mm_free(oldptr);
        return NULL;
    }
    if(oldptr==NULL)
    {
        return mm_malloc(size);
    }
    newptr=mm_malloc(size);
    if(!newptr)
    {
        return 0;
    }
    oldsize=GET_SIZE(HDRP(oldptr));
    if(size<oldsize)
        oldsize=size;
    memcpy(newptr,oldptr,oldsize);

    mm_free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes=nmemb*size;
    void *newptr;
    if((nmemb==0)||(size==0))
    {

        return NULL;
    }
    else
    {
        newptr=mm_malloc(bytes);
        memset(newptr,0,bytes);
    }
    return newptr;
}
/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    unsigned int count,list_length;
    unsigned int * bp =(unsigned int *) heap_listp;
    unsigned int *bp_prev = (unsigned int *)heap_listp;
    unsigned int number_freelist_pointer=0;
    unsigned int block_free_count=0; 

    if (verbose)
    {
        printf("Heap (%p):\n", heap_listp);
        printf("begenning pointer of the heap is %p \n last pointer of the heap is %p\n heapsize is %ld\n",
                (unsigned int *)mem_heap_lo(),(unsigned int *)mem_heap_hi(),mem_heapsize());
    }

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE+LISTNUMBER*WSIZE+(LISTNUMBER%2)*WSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    if (((GET_SIZE(FTRP(heap_listp))) != DSIZE+LISTNUMBER*WSIZE+(LISTNUMBER%2)*WSIZE) || !GET_ALLOC(FTRP(heap_listp)))
        printf("Bad prologue footer\n");

    for (bp = ((unsigned int *)(heap_listp + (LISTNUMBER+2)*WSIZE + (LISTNUMBER%2)*WSIZE)); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP_POINTER(bp))
    {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
        if(bp!=(unsigned int *)heap_listp)      //when it is not the initial position, we should check coales.
        {
            checkcoales(bp,bp_prev);
        }
        if(GET_ALLOC(HDRP(bp))==UNALLOC)
        {
            block_free_count++;
        }
        bp_prev=bp;
    }


    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    /*check segregated free list*/
    for(count=0;count<LISTNUMBER;count++)
    {
        if(GET_POINTER_4BYTES(heap_listp+count*WSIZE)==MASK_POINTER)
            printf("list[%u] is empty\n",count);
        else
        {
            list_length=0;
            printf("list[%u] is not empty\n",count);

            for(bp=GET_POINTER_4BYTES(heap_listp+count*WSIZE);bp!=MASK_POINTER&&bp!=NULL;bp=GET_POINTER_4BYTES_NXT(bp))
            {
                number_freelist_pointer++;
                list_length++;
                if(GET_ALLOC(bp)==ALLOC)
                {
                    printf("No.%u block in list[%u] is already allocated which should be removed from freelist\n",list_length,count);
                }

                if(!in_heap(bp))
                {
                    printf("No.%u block in list[%u] is out of the boundary of the heap\n",list_length,count);
                }

                if(list_length==1)
                {
                    if(GET_POINTER_4BYTES(bp)!=MASK_POINTER)
                        printf("First block previous is wrong in list[%u] and list_length=%u.\n",count,list_length);                 
                }

                else 
                {
                    if(bp_prev!=MASK_POINTER&&bp!=MASK_POINTER)
                    {
                        if(GET_POINTER_4BYTES_NXT(bp_prev)!=bp)
                            printf("prev's next block pointer is wrong in list[%u] and list_length=%u.\n",count,list_length);
                        if(GET_POINTER_4BYTES(bp)!=bp_prev)
                            printf("bp's previous block pointer is wrong in list[%u] and list_length=%u.\n",count,list_length);
                    }
                }
                bp_prev=bp;
            }
            printf("list[%u] has %u blocks\n",count,list_length);
        }
    }

    /* Count free blocks by iterating through every block and traversing free list by pointers and see if
       they match */
    if(number_freelist_pointer!=block_free_count)
    {
        printf("Count free blocks by iterating through every block are not equal to traversing free list by pointer\n");
        if(freelist_count!=block_free_count)
        {
            printf("get wrong freelist count by interating through every block\n");
            printf("freelist_count=%u block_free_count=%u \n",freelist_count,block_free_count);
        }
        if(freelist_count!=number_freelist_pointer)
        {
            printf("get wrong freelist count by traversing through free list\n");
            printf("freelist_count= %u number_freelist_pointer=%u \n",freelist_count,number_freelist_pointer);
        }
    }
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
     if ((char*)(bp = mem_sbrk(size)) < (char*)NULL) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, UNALLOC));         /* free block header */
    PUT(FTRP(bp), PACK(size, UNALLOC));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, ALLOC)); /* new epilogue header */

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

    if ((csize - asize) >= (DDSIZE)) 
    {
        remove_freelist(bp);     
        PUT(HDRP(bp), PACK(asize, ALLOC));
        PUT(FTRP(bp), PACK(asize, ALLOC));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, UNALLOC));
        PUT(FTRP(bp), PACK(csize-asize, UNALLOC));;
        add_freelist(bp);
    }

    else 
    {

        PUT(HDRP(bp), PACK(csize, ALLOC));
        PUT(FTRP(bp), PACK(csize, ALLOC));
        remove_freelist(bp);
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    unsigned int *bp;
    unsigned int position_in_list;
    if(freelist_count==0)
    {
        return NULL;
    } 

    //unsigned int position_in_list =asize/DIVIDESIZE;
    //
    /*
    if(asize<=TDSIZE)
    {
        position_in_list=0;
    }

    else if(asize<=32) 
    {
        position_in_list=1;
    }

    else if(asize<=40)
    {
        position_in_list=2;
    }
    
    else if(asize<=48)
    {
        position_in_list=3;
    }
    
    else if(asize<=56)
    {
        position_in_list=4;
    }

    else if(asize<=64)
    {
    position_in_list=5;
    }
    */

    if(asize<=64)
    {
        switch(asize/DSIZE-2)
        {
        case 0: position_in_list=0;break;   //asize=16;
        case 1: position_in_list=1;break;   //aszie=24;
        case 2: position_in_list=2;break;   //asize=32;
        case 3: position_in_list=3;break;   //asize=40;
        case 4: position_in_list=4;break;   //asize=48;
        case 5: position_in_list=5;break;   //asize=56;
        case 6: position_in_list=6;break;   //asize=64;
        }
    }

    else if(asize<=2047) 
    {
        switch(asize/DIVIDVALUE)
        {
            case 0:position_in_list=7;break;    //65<=aszie<=127
            case 1:position_in_list=8;break;    //128<=asize<=255
            case 2:
            case 3:position_in_list=9;break;    //256<=asize<=511
            case 4:
            case 5:
            case 6:
            case 7:position_in_list=10;break;    //512<=asize<=1023
            case 8:
            case 9:
            case 10:
            case 11:
            case 12:
            case 13:
            case 14:
            case 15:position_in_list=11;break;  //1023<=asize<=2047
        }
    }

    else if(asize<=4095)                        //2048<=asize<=4095
    {
        position_in_list=12;
    }

    else if(asize<=8191)
    {
        position_in_list=13;                    //4096<=asize;
    }

    else
    {
        position_in_list=14;
    }


  /*  if(position_in_list>(LISTNUMBER-1))
    {
        position_in_list=LISTNUMBER-1;
    }
  */
    if(position_in_list<min_minlist)
    {
        position_in_list=min_minlist;
    }
    /* first fit search */
    while(position_in_list<LISTNUMBER)
    {      

        for (bp = GET_POINTER_4BYTES(heap_listp+(position_in_list*WSIZE)); bp!=MASK_POINTER&&bp!=NULL&&(GET_SIZE(HDRP(bp))>0); bp = GET_POINTER_4BYTES_NXT(bp)) 
        {   

            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) 
            {
                return bp;
            }
        }
        position_in_list++;
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{


    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) /* Case 1 */
    { 
        //just need to add this block to corresponding freelist;
        add_freelist(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc)   /* Case 2 */
    {   
        //first remove the next freelist and coalesce to one
        remove_freelist(NEXT_BLKP_POINTER(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, UNALLOC));
        PUT(FTRP(bp), PACK(size, UNALLOC));
        add_freelist(bp);
        return(bp);
    }

    else if (!prev_alloc && next_alloc) /* Case 3 */
    {   
        remove_freelist(PREV_BLKP_POINTER(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, UNALLOC));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, UNALLOC));
        add_freelist(PREV_BLKP_POINTER(bp));
        return(PREV_BLKP(bp));
    }


    else   /* Case 4 */
    {  
        remove_freelist(NEXT_BLKP_POINTER(bp));
        remove_freelist(PREV_BLKP_POINTER(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, UNALLOC));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, UNALLOC));
        add_freelist(PREV_BLKP_POINTER(bp));
        return(PREV_BLKP(bp));
    }
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) 
    {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
            (long int)hsize, (halloc ? 'a' : 'f'), 
            (long int)fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if (!(aligned(bp)))
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    if(!(in_heap(bp)))
        printf("Error: bp is in heap\n");
}

static void checkcoales(unsigned int  *bp,unsigned int  *bp_prev)
{
    if((GET_ALLOC(HDRP(bp))==FALSE) && (GET_ALLOC(HDRP(bp_prev))==FALSE))
        printf("Error: coalesce is not right!\n");
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */

static int in_heap(const void *p) 
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) 
{
    return (size_t)ALIGN(p) == (size_t)p;
}

static void add_freelist(unsigned int  *bp)
{
    unsigned int  *next,*cur,*prev;
    size_t size;
    unsigned int minlist;

    if(freelist_count>=INITIALVALUE)
    {
        freelist_count=0;
    }

    freelist_count++;

    size=GET_SIZE(HDRP(bp));

    // minlist=size/DIVIDESIZE;

/*    if(minlist>(LISTNUMBER-1))
    {
        minlist=(LISTNUMBER-1);
    }
*/

        if(size<=64)
    {
        switch(size/DSIZE-2)
        {
        case 0: minlist=0;break;
        case 1: minlist=1;break;   //aszie=24;
        case 2: minlist=2;break;   //asize=32;
        case 3: minlist=3;break;   //asize=40;
        case 4: minlist=4;break;   //asize=48;
        case 5: minlist=5;break;   //asize=56;
        case 6: minlist=6;break;   //asize=64;
        default: minlist=-1; break; //if there is an error;
        }
    }

    else if(size<=2047) 
    {
        switch(size/DIVIDVALUE)    //DIVIDVALUE 128
        {
            case 0:minlist=7;break;    //65<=aszie<=127
            case 1:minlist=8;break;    //128<=asize<=255
            case 2:
            case 3:minlist=9;break;    //256<=asize<=511
            case 4:
            case 5:
            case 6:
            case 7:minlist=10;break;    //512<=asize<=1023
            case 8:
            case 9:
            case 10:
            case 11:
            case 12:
            case 13:
            case 14:
            case 15:minlist=11;break;  //1023<=asize<=2047
            default: minlist=-1; break; //if there is an error;
        }
    }

    else if(size<=4095)                        //2048<=asize<=4095
    {
        minlist=12;
    }

    else if(size<=8191)
    {
        minlist=13;                    //4096<=asize;
    }

    else 
    {
        minlist=14;
    }

    if(min_minlist>minlist||min_minlist==INITIALVALUE)
    {
        min_minlist=minlist;
    }

    cur=GET_POINTER_4BYTES(heap_listp+(minlist*WSIZE));

    if(cur==MASK_POINTER||(cur==NULL))  //it means it is the first block in this type list
    {
        PUT_POINTER_4BYTES(heap_listp+(minlist*WSIZE),(bp));
        PUT_POINTER_NULL(bp);
        PUT_POINTER_4BYTES_NXT(bp,NULL);
    }

    else //it has been initialized
    {
        prev=cur;
        while(TRUE)
        {
            if((cur!=MASK_POINTER)&&cur!=NULL&&GET_SIZE(HDRP(cur))<size)
            {
                prev=cur;
                cur=GET_POINTER_4BYTES_NXT(cur);
            }
            else
            {
                cur=prev;
                break;
            }
        }
        next=GET_POINTER_4BYTES_NXT(cur);
        PUT_POINTER_4BYTES_NXT(cur,bp);

        PUT_POINTER_4BYTES(bp,cur);
        PUT_POINTER_4BYTES_NXT(bp,next);

        if((next!=MASK_POINTER)&&(next!=NULL))
        {
            PUT_POINTER_4BYTES(next,bp);
        }
    }
}

static void remove_freelist(unsigned int  *bp)
{

    unsigned int minlist;
    unsigned int count;
    size_t size;

    size=GET_SIZE(HDRP(bp));

    freelist_count--;

   // minlist=size/DIVIDESIZE;

    /*
    if(minlist>(LISTNUMBER-1))
    {
        minlist=LISTNUMBER-1;
    }
    */


    if(size<=64)
    {
        switch(size/DSIZE-2)
        {
        case 0: minlist=0;break;
        case 1: minlist=1;break;   //aszie=24;
        case 2: minlist=2;break;   //asize=32;
        case 3: minlist=3;break;   //asize=40;
        case 4: minlist=4;break;   //asize=48;
        case 5: minlist=5;break;   //asize=56;
        case 6: minlist=6;break;   //asize=64;
        default: minlist=-1; break; //if there is an error;
        }
    }

    else if(size<=2047) 
    {
        switch(size/DIVIDVALUE)    //DIVIDVALUE 128
        {
            case 0:minlist=7;break;    //65<=aszie<=127
            case 1:minlist=8;break;    //128<=asize<=255
            case 2:
            case 3:minlist=9;break;    //256<=asize<=511
            case 4:
            case 5:
            case 6:
            case 7:minlist=10;break;    //512<=asize<=1023
            case 8:
            case 9:
            case 10:
            case 11:
            case 12:
            case 13:
            case 14:
            case 15:minlist=11;break;  //1023<=asize<=2047
            default: minlist=-1; break; //if there is an error;
        }
    }

    else if(size<=4095)                        //2048<=asize<=4095
    {
        minlist=12;
    }

    else if(size<=8191)
    {
        minlist=13;                    //4096<=asize;
    }

    else
    {
        minlist=14;
    }

    /*There are 4 cases to consider*/
    if(GET_POINTER_4BYTES(bp)==MASK_POINTER&&GET_POINTER_4BYTES_NXT(bp)==MASK_POINTER) //the block which will be removed is the only block in this type of list;
    {
        PUT_POINTER_4BYTES(heap_listp+WSIZE*minlist,NULL);
        if(min_minlist==minlist)
        {
            if(freelist_count<=0)
            {
                freelist_count=INITIALVALUE;
            }
            else
            {
                for(count=minlist;(GET_POINTER_4BYTES(heap_listp+count*WSIZE)==MASK_POINTER)&&(count<(LISTNUMBER-1));count++)
                {}
                min_minlist=count;
               
            }
        }
    }

    else if(GET_POINTER_4BYTES(bp)==MASK_POINTER&&GET_POINTER_4BYTES_NXT(bp)!=MASK_POINTER)     //the block will be removed is the first block but it is not the only block in its list
    {      
       
        {
            PUT_POINTER_4BYTES(heap_listp+WSIZE*minlist,GET_POINTER_4BYTES_NXT(bp)); 
            PUT_POINTER_4BYTES(GET_POINTER_4BYTES_NXT(bp),NULL);
        }
    }

    else if(GET_POINTER_4BYTES(bp)!=MASK_POINTER&&GET_POINTER_4BYTES_NXT(bp)==MASK_POINTER)     //the block will be removed is the last block in its list
    {
        
        PUT_POINTER_4BYTES_NXT((GET_POINTER_4BYTES(bp)),NULL); //need to modify
    }
    else                                            //the block is in the middle of its list; 
    {
       
        PUT_POINTER_4BYTES(GET_POINTER_4BYTES_NXT(bp),GET_POINTER_4BYTES(bp));
        PUT_POINTER_4BYTES_NXT((GET_POINTER_4BYTES(bp)),GET_POINTER_4BYTES_NXT(bp));

    }
   
}

