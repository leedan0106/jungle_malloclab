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
#include <math.h>

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

#define GET_PRED(bp) GET(bp)
#define GET_SCRP(bp) GET(SCRP(bp))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) /* 다음 블록 위치 가져오기. bp에서 블록사이즈 만큼 더하면 다음 header 뒤로 감 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) /* 이전 블록 위치 가져오기. 이전 블록의 footer에서 블록 사이즈 가져와서 이동 ?? */

#define LISTLIMIT 20

static char *heap_listp;
static char *free_list[LISTLIMIT+1];

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);
static int find_idx(size_t);
static void insert_block(void*);
static void remove_block(void*);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* free list 초기화 */
    for (int i=0; i<=LISTLIMIT; i++) {
        free_list[i] = NULL;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                           /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));  /* Epilogue header */

    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;


    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) 
        return NULL;
    

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
    
}


static void remove_block(void *ptr) {
    int idx = find_idx(GET_SIZE(HDRP(ptr)));

    // 맨 앞 블록 삭제
    if (free_list[idx] == ptr) {
        if (GET_SCRP(ptr) == NULL) // 유일한 블록
            free_list[idx] = NULL;
        else {
            PUT(GET_SCRP(ptr), NULL);
            free_list[idx] = GET_SCRP(ptr);
        }
    }else{
        // 중간 블록 삭제
        if (GET_SCRP(ptr) != NULL) {
            PUT(GET_SCRP(ptr), GET_PRED(ptr));
            PUT(SCRP(GET_PRED(ptr)), GET_SCRP(ptr));
        }else{ // 맨 뒷 블록 삭제
            PUT(SCRP(GET_PRED(ptr)), NULL);
        }

    }
}

// 오름차순
static void insert_block(void *ptr) 
{
    size_t size = GET_SIZE(HDRP(ptr));
    int idx = find_idx(size);

    if (size == 0)
        return;

    char *front_ptr = free_list[idx];
    char *prev_ptr = NULL;

    if (front_ptr == NULL)
    {
        PUT(ptr, NULL);
        PUT(SCRP(ptr), NULL);
        free_list[idx] = ptr;
        return;
    }

    // 새로운 블록 사이즈가 size class의 첫 번째 블록보다 작은 경우 (리스트 내에서 제일 작은 사이즈)
    if (size <= GET_SIZE(HDRP(front_ptr))) {
        free_list[idx] = ptr;
        PUT(ptr, NULL);
        PUT(SCRP(ptr), front_ptr);
        PUT(front_ptr, ptr);
        return;
    }

    // 오름차순으로 정렬된 가용 리스트에서 블록이 들어갈 지점 찾기
    while (front_ptr != NULL && GET_SIZE(HDRP(front_ptr)) < size) 
    {
        prev_ptr = front_ptr;
        front_ptr = GET_SCRP(front_ptr);
    }

    if (front_ptr == NULL) { // 가용 리스트의 끝에 도달한 경우
        PUT(SCRP(prev_ptr), ptr);
        PUT(ptr, prev_ptr);
        PUT(SCRP(ptr), NULL);
        return;
    }
    else 
    { // 가용 리스트의 중간에 집어넣는 경우
        PUT(SCRP(prev_ptr), ptr);
        PUT(ptr, prev_ptr);
        PUT(SCRP(ptr), front_ptr);
        PUT(front_ptr, ptr);
        return;
    }
}


// 내림차순
// static void insert_block(void *ptr) 
// {
//     size_t size = GET_SIZE(HDRP(ptr));
//     int idx = find_idx(size);

//     if (size == 0)
//         return;

//     char *front_ptr = free_list[idx];
//     char *prev_ptr = NULL;

//     if (front_ptr == NULL)
//     {
//         PUT(ptr, NULL);
//         PUT(SCRP(ptr), NULL);
//         free_list[idx] = ptr;
//         return;
//     }

//     // 새로운 블록 사이즈가 size class의 첫 번째 블록보다 큰 경우(리스트 내에서 제일 큰 사이즈)
//     if (size >= GET_SIZE(HDRP(front_ptr))) {
//         free_list[idx] = ptr;
//         PUT(ptr, NULL);
//         PUT(SCRP(ptr), front_ptr);
//         PUT(front_ptr, ptr);
//         return;
//     }

//     // 내림차순으로 정렬된 가용 리스트에서 블록이 들어갈 지젘 찾기
//     while (front_ptr != NULL && GET_SIZE(HDRP(front_ptr)) > size) 
//     {
//         prev_ptr = front_ptr;
//         front_ptr = GET_SCRP(front_ptr);
//     }

//     if (front_ptr == NULL) { // 가용 리스트의 끝에 도달한 경우
//         PUT(SCRP(prev_ptr), ptr);
//         PUT(ptr, prev_ptr);
//         PUT(SCRP(ptr), NULL);
//         return;
//     }
//     else 
//     { // 가용 리스트의 중간에 집어넣는 경우
//         PUT(SCRP(prev_ptr), ptr);
//         PUT(ptr, prev_ptr);
//         PUT(SCRP(ptr), front_ptr);
//         PUT(front_ptr, ptr);
//         return;
//     }
// }

// static void insert_block(void *ptr) {
//     int idx = find_idx(GET_SIZE(HDRP(ptr)));

//     if (free_list[idx] == NULL) {
//         PUT(ptr, NULL);
//         PUT(SCRP(ptr), NULL);
//     } else {
//         PUT(ptr, NULL);
//         PUT(SCRP(ptr), free_list[idx]); // 맨 앞에 삽입
//         PUT(free_list[idx], ptr);
//     }
//     free_list[idx] = ptr;
// }

int find_idx(size_t size) {
    int idx;
    for (idx = 0; idx<LISTLIMIT;idx++) {
        if (size <= (1 << idx))
            return idx;
    }
    return idx;
}


static void *coalesce(void *ptr) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (prev_alloc && next_alloc) { /* Case 1: 앞 뒤 블록 모두 할당되어 있는 경우: 연결할 블록 없음 */
        insert_block(ptr);
        return ptr;
    } 

    else if (prev_alloc && !next_alloc) { /* Case 2: 이전 블록은 할당되어 있고, 다음 블록은 가용블록인 경우: 다음 블록과 연결 */

        remove_block(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3: 이전 블록이 가용블록이고, 다음 블록은 할당되어 있는 경우: 이전 블록과 연결 */

        remove_block(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(ptr)), PACK(size, 0)); // 이미 사이즈가 변경되었기 때문에 이렇게도 가능할 것 같은데.. 아래 코드가 더 간단하긴 하다. 둘 다 테스트 해보기.
        ptr = PREV_BLKP(ptr);
    }   

    else { /* Case 4: 앞 뒤 블록 모두 가용 블록인 경우: 두 블록 모두 연결 */
        remove_block(PREV_BLKP(ptr));
        remove_block(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // GET_SIZE(FTRP(NEXT_BLKP(ptr)가 차이가 있을까.. 어차피 header, footer 같은 값을 가지는데.
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    insert_block(ptr);
    return ptr;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

int round_up_power_2(int x) {
    int result = 1;
    while (result < x) {
        result <<= 1;
    }
    return result;
}

void *mm_malloc(size_t size)
{
    // printf("4\n");
    size_t asize;
    size_t extendsize;
    char *ptr;

    /* Ignore spurious requests */
    if (size == 0) 
        return NULL;

    if (size <= CHUNKSIZE)
        size = round_up_power_2(size); // 사이즈를 2의 제곱수로 올림한다.

    size_t words = ALIGN(size) / WSIZE;


    /* Adjust block size to include overhead and alignment reqs. */
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
    int idx = find_idx(asize);
    void *ptr;

    for (int i=idx; i<=LISTLIMIT; i++) {
        for (ptr = free_list[i]; ptr != NULL; ptr = GET_SCRP(ptr)) {
            if (GET_SIZE(HDRP(ptr)) >= asize) 
                return ptr;
        }
    }
    return NULL;
}

static void place(void *ptr, size_t asize)
{

    size_t size = GET_SIZE(HDRP(ptr));

    remove_block(ptr);
    if (size-asize < 2*DSIZE) { // 남은 블록을 사용할 수 없는 경우 - 분할하지 않는다.
        PUT(HDRP(ptr), PACK(size, 1));    
        PUT(FTRP(ptr), PACK(size, 1));
    } else {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(size-asize, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size-asize, 0));

        coalesce(NEXT_BLKP(ptr)); // 남은 블록 붙이기
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     copySize = GET_SIZE(HDRP(ptr));
//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }


void *mm_realloc(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (4 * WSIZE);   // 4*WISE(Header, Pred, Suc, Footer)

    // 필요한 size가 기존 size보다 작거나 같으면 기존 bp 사용
    if (new_size <= old_size) {
        return bp;
    }
    // 필요한 size가 기존 size보다 큰 경우
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // next block가 가용 블록이고, 기존 블록과의 합이 필요한 사이즈 보다 크면 합쳐서 사용
        if (!next_alloc && current_size >= new_size) {
            remove_block(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        // 그렇지 않은 경우 그냥 공간 새로 할당 받기
        else {
            void *new_bp = mm_malloc(new_size);
            memcpy(new_bp, bp, new_size);  
            mm_free(bp);
            return new_bp;
        }
    }
}










