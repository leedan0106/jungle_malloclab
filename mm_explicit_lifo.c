/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) (header, footer size는 모두 1 word) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) 1을 12비트 만큼 왼쪽으로 시프트. 이진수 1이 왼쪽으로 12만큼 이동. 2의 12승 = 4096 */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size write a word at address p. 사이즈에 가용 여부 비트를 or 연산을 사용하여 합친다. -> 헤더에서 사용하기 위해서 */
#define PACK(size, alloc) ((size) | (alloc))

/* Read the size and allocated fields from address p */
#define GET(p) (*(unsigned int *)(p)) /* p에 할당된 값을 unsigned int형식으로 해석하여 반환? 왜 unsigned int?? -- header가 1 word라서 그런건가?? header 사이즈에 맞게 늘려 주는 건가? */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* p에 주소(val) 저장 */

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) /* header에서 size만 추출하기 ~0x7 = 11111000 and 연산을 통해서 000 앞의 값만 가져옴 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* header에서 allocated(가용여부)만 추출 0x1 = 00000111 and 연산을 통해서 마지막 3개의 비트 정보만 가져옴 */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE) /* header의 주소 가져오기 block pointer에서 -1word*/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* footer의 주소 가져오기 block size에서 header, footer 만큼 제외 -2word */
#define SCRP(bp) ((char *)(bp) + WSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) /* 다음 블록 위치 가져오기. bp에서 블록사이즈 만큼 더하면 다음 header 뒤로 감 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) /* 이전 블록 위치 가져오기. 이전 블록의 footer에서 블록 사이즈 가져와서 이동 ?? */

static char *heap_listp;
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // printf("1\n");
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                           /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(4*WSIZE, 1));  /* Prologue header */
    PUT(heap_listp + (2*WSIZE), NULL);            /* Predecessor pointer */
    PUT(heap_listp + (3*WSIZE), NULL);   /* Successor pointer */
    PUT(heap_listp + (4*WSIZE), PACK(4*WSIZE, 1));  /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));  /* Epilogue header */

    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

static void *extend_heap(size_t words) 
{
    // printf("2\n");
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) /* why long?? 캐스팅이 이해되지 않음.. bp에 mem_sbrk로 새로운 블록 할당*/
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
    
}

void remove_block(void *ptr) {
    if (ptr == heap_listp) {
        PUT(GET(SCRP(ptr)), NULL);
        heap_listp = GET(SCRP(ptr));
    }else{
        PUT(SCRP(GET(ptr)), GET(SCRP(ptr)));
        PUT(GET(SCRP(ptr)), GET(ptr));
    }
}

static void *coalesce(void *ptr) {
    // printf("3\n");

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (prev_alloc && next_alloc) { /* Case 1: 앞 뒤 블록 모두 할당되어 있는 경우: 연결할 블록 없음 */
        // 앞쪽에 붙여주기
        PUT(SCRP(ptr), heap_listp);
        PUT(ptr, NULL);
        PUT(heap_listp, ptr);
        heap_listp = ptr;
        return ptr;

        // PUT(ptr, HDRP(heap_listp));
        // PUT(SCRP(ptr), GET(SCRP(heap_listp)));

        // PUT(SCRP(heap_listp), HDRP(ptr));
        // if(GET(SCRP(ptr)) != NULL) {
        //     PUT(HD_PR(GET(SCRP(ptr))), HDRP(ptr));
        // }
    } 

    else if (prev_alloc && !next_alloc) { /* Case 2: 이전 블록은 할당되어 있고, 다음 블록은 가용블록인 경우: 다음 블록과 연결 */
        // 연결 끊기

        // PUT(SCRP(GET(NEXT_BLKP(ptr))), GET(SCRP(NEXT_BLKP(ptr)))); /* pred block 의 suc update*/
        // if (GET(SCRP(NEXT_BLKP(ptr))) != NULL) {
        //     PUT(HD_PR(GET(SCRP(NEXT_BLKP(ptr)))), GET(NEXT_BLKP(ptr))); /* suc block 의 pred update */
        // }

        remove_block(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3: 이전 블록이 가용블록이고, 다음 블록은 할당되어 있는 경우: 이전 블록과 연결 */
        // 연결 끊기
        // PUT(SCRP(GET(PREV_BLKP(ptr))), GET(SCRP(PREV_BLKP(ptr)))); /* pred block 의 suc update*/
        // if (GET(SCRP(PREV_BLKP(ptr))) != NULL) {
        //     PUT(HD_PR(GET(SCRP(PREV_BLKP(ptr)))), GET(PREV_BLKP(ptr))); /* suc block 의 pred update */
        // }

        remove_block(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(ptr)), PACK(size, 0)); // 이미 사이즈가 변경되었기 때문에 이렇게도 가능할 것 같은데.. 아래 코드가 더 간단하긴 하다. 둘 다 테스트 해보기.
        ptr = PREV_BLKP(ptr);


    }   

    else { /* Case 4: 앞 뒤 블록 모두 가용 블록인 경우: 두 블록 모두 연결 */
        // 연결 끊기
        remove_block(PREV_BLKP(ptr));
        remove_block(NEXT_BLKP(ptr));
        // PUT(SCRP(GET(NEXT_BLKP(ptr))), GET(SCRP(NEXT_BLKP(ptr)))); /* pred block 의 suc update*/
        // if (GET(SCRP(NEXT_BLKP(ptr))) != NULL) {
        //     PUT(HD_PR(GET(SCRP(NEXT_BLKP(ptr)))), GET(NEXT_BLKP(ptr))); /* suc block 의 pred update */
        // }

        // PUT(SCRP(GET(PREV_BLKP(ptr))), GET(SCRP(PREV_BLKP(ptr)))); /* pred block 의 suc update*/
        // if (GET(SCRP(PREV_BLKP(ptr))) != NULL) {
        //     PUT(HD_PR(GET(SCRP(PREV_BLKP(ptr)))), GET(PREV_BLKP(ptr))); /* suc block 의 pred update */
        // }

        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // GET_SIZE(FTRP(NEXT_BLKP(ptr)가 차이가 있을까.. 어차피 header, footer 같은 값을 가지는데.
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    PUT(SCRP(ptr), heap_listp);
    PUT(ptr, NULL);
    PUT(heap_listp, ptr);
    heap_listp = ptr;

    // PUT(ptr, HDRP(heap_listp));
    // PUT(SCRP(ptr), GET(SCRP(heap_listp)));

    // PUT(SCRP(heap_listp), HDRP(ptr));
    // if(GET(SCRP(ptr)) != NULL) {
    //     PUT(HD_PR(GET(SCRP(ptr))), HDRP(ptr));
    // }

    return ptr;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // printf("4\n");
    size_t asize;
    size_t extendsize;
    char *ptr;

    /* Ignore spurious requests */
    if (size == 0) 
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    // 이전 코드의 newsize를 사용하면 안될는지 테스트.
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((ptr = find_fit(asize)) != NULL) {
        place(ptr, asize);
        return ptr;
    }

    /* No fit found. Get more momory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    
    place(ptr, asize);
    return ptr;
}

static void *find_fit(size_t asize) // first fit 탐색
{   
    // printf("5\n");
    // heap_listp가 맨 첫번째 block를 가리키고 있음.
    void *cur_ptr = heap_listp;

    while(GET_ALLOC(HDRP(cur_ptr)) != 1) { // 이 부분 확인 필요.
        // printf("%lu\n", GET_ALLOC(HDRP(cur_ptr)));
        if (GET_SIZE(HDRP(cur_ptr)) >= asize) {
            return cur_ptr;
        }else{
            cur_ptr = GET(SCRP(cur_ptr));
        }
    }
    return NULL;
}

static void place(void *ptr, size_t asize)
{
    // printf("6\n");

    size_t size = GET_SIZE(HDRP(ptr));

    remove_block(ptr);
    if (size-asize < 2*DSIZE) { // 남은 블록을 사용할 수 없는 경우 - 분할하지 않는다.
        PUT(HDRP(ptr), PACK(size, 1));    
        PUT(FTRP(ptr), PACK(size, 1));

        // Pred의 Suc update
        // PUT(HD_SC(GET(ptr)), GET(SCRP(ptr)));
        // Suc의 Pred update
        // PUT(HD_PR(GET(SCRP(ptr))), GET(ptr));

    } else {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(size-asize, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size-asize, 0));

        // 맨 앞에 붙이기
        PUT(SCRP(NEXT_BLKP(ptr)), heap_listp);
        PUT(NEXT_BLKP(ptr), NULL);
        PUT(heap_listp, NEXT_BLKP(ptr));
        heap_listp = NEXT_BLKP(ptr);


        // PUT(NEXT_BLKP(ptr), GET(ptr));
        // PUT(SCRP(NEXT_BLKP(ptr)), GET(SCRP(ptr)));

        // 이전 블록과 다음 블록의 suc, pred를 새로 생긴 블록의 header로 업데이트 해주기.
        // PUT(HD_SC(GET(ptr)), HDRP(NEXT_BLKP(ptr)));
        // if (GET(SCRP(ptr)) != NULL) {
        //     PUT(GET(SCRP(ptr)), HDRP(NEXT_BLKP(ptr)));
        // }
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // printf("7\n");
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(ptr));
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














