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
    ""};


// 매크로들은 모두 반복적으로 쓰이는 변수나 함수를 일반화 시켜놓은 것
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 조정 크기 8배수

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 가장 근접한 8의 배수로 올림

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE 4 // 헤더 == 푸터 == 워드에 크기
#define DSIZE 8 // 더블 워드 = Alignment 크기
#define CHUNKSIZE (1<<12)   // 초기 최대 힙 사이즈 (1 => 4096, 4KB)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 큰 값 가져오기

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 만듬.
#define PACK(size,alloc) ((size) | (alloc)) // alloc : 가용여부 (ex. 000, 001) / size : block size를 의미. =>합치면 온전한 주소가 나온다.

// Read and write a word at address p // p는 보통 void포인터이지만 사이즈를 나타내기 위해 형변환
#define GET(p) (*(unsigned int *)(p)) // 주소 읽기
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 주소 쓰기

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더 정보에 있는 사이즈의 크기만 쉽게 가져옴
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 여부만 가져옴


// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE) //헤더의 bp는 bp에서 WSIZE 값을 뺀 값 (bp - 4byte = 헤더 위치)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //푸터의 bp는 bp에서 내 사이즈를 더하고 DSIZE 값을 뺀 만큼 (bp(payload주소) + (블록 크기) - (헤더 + 푸터))

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 bp (bp + 현재 블록 크기(현재 블록 헤더에서 사이즈 받기))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 bp (bp + 이전 블록 크기(이전 블록 푸터에서 사이즈 받기))


static char *heap_listp; // 처음에 쓸 큰 가용블록 힙을 만들어줌.
static char *find_nextp; // Next에 쓸 큰 가용블록 힙을 만들어줌.
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize); // 65점
static void place(void *bp, size_t asize);
static void *best_fit(size_t asize); // 63점
static void *next_fit(size_t asize); // 83점
static void *good_fit(size_t asize); // 
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);
    find_nextp = heap_listp;
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));


    return coalesce(bp);
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size==0){
        return NULL;
    }

    if(size<=DSIZE){
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if((bp = best_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
    
}

/*
 * mm_free - Freeing a block does nothing.
 */

 static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    find_nextp = bp;
    return bp;
}



static void *find_fit(size_t asize){
    void *bp;
    
    for(bp=heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;

}

static void *best_fit(size_t asize){
    void *bp = NULL;
    void *find_best;
    size_t best_size = -1;
    for(find_best=heap_listp; GET_SIZE(HDRP(find_best)) > 0; find_best = NEXT_BLKP(find_best)){
        if(!GET_ALLOC(HDRP(find_best)) && (asize < GET_SIZE(HDRP(find_best))) && (GET_SIZE(HDRP(find_best))<best_size)){  
            bp = find_best;
            best_size = GET_SIZE(HDRP(bp));
        }
        else if(!GET_ALLOC(HDRP(find_best)) && (asize == GET_SIZE(HDRP(find_best)))){
            return find_best;
        }
    }

    return bp;    
}

static void *good_fit(size_t asize) {
    void *bp;
    void *find_best = NULL;
    size_t good_size = -1;
    int search_limit = 2000;   
    int count = 0;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0 && count < search_limit; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))) && (GET_SIZE(HDRP(bp))<good_size)) {
            find_best = bp;
            good_size = GET_SIZE(HDRP(find_best));
        }
        count++;
    }

    return find_best;
}

static void *next_fit(size_t asize){
    void *bp;
    bp = find_nextp;
    for(; GET_SIZE(HDRP(find_nextp)) > 0; find_nextp = NEXT_BLKP(find_nextp)){
        if(!GET_ALLOC(HDRP(find_nextp)) && (asize <= GET_SIZE(HDRP(find_nextp)))){
            return find_nextp;
        }
    }

    for(find_nextp = heap_listp; find_nextp != bp; find_nextp = NEXT_BLKP(find_nextp)){
        if(!GET_ALLOC(HDRP(find_nextp)) && (asize <= GET_SIZE(HDRP(find_nextp)))){
            return find_nextp;
        }
    }
    return NULL;

}


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
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}