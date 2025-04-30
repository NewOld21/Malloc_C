#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "team 5",
    "Juhee Lee",
    "juhee971204@gmail.com",
    "",
    ""};

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* === Explicit Free List Macros === */
#define MIN_BLOCK_SIZE (2 * WSIZE + 2 * DSIZE) // 24 bytes

#define GET_PRED(bp) (*(void **)(bp))
#define GET_SUCC(bp) (*(void **)((char *)(bp) + DSIZE))

#define SET_PRED(bp, pred_bp) (*(void **)(bp) = (pred_bp))
#define SET_SUCC(bp, succ_bp) (*(void **)((char *)(bp) + DSIZE) = (succ_bp))

/* Global variables */
static char *heap_listp = NULL;
static char *free_listp = NULL; // free list root(LIFO)
static char *next_fit_ptr = NULL; // NEXT FIT 포인터

/* Function prototypes */
static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *rand_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_free_block(void *bp);
static void splice_free_block(void *bp);
static void *probability_rand_fit(size_t asize);
static void *best_fit(size_t asize);

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);
    free_listp = NULL;
    next_fit_ptr = NULL; // 초기화

    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

    // NEXT FIT REVISED: 초기 힙 확장 후 next_fit_ptr 설정
    // coalesce 가 free_listp 를 설정하므로 그 값을 사용
    next_fit_ptr = free_listp;

    return 0;
}

static void *extend_heap(size_t size)
{
    char *bp;
    size_t aligned_size = ALIGN(size);
    if ((bp = mem_sbrk(aligned_size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(aligned_size, 0));
    PUT(FTRP(bp), PACK(aligned_size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;

    if (size <= DSIZE) asize = 2 * DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = best_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    if (bp == NULL) return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void* original_next_fit_ptr = next_fit_ptr; // NEXT FIT: 이전 포인터 값 저장 (비교용)

    // NEXT FIT REVISED: 병합될 블록 중 하나가 next_fit_ptr 인지 확인
    int next_fit_needs_update = 0;
    if (!next_alloc && (NEXT_BLKP(bp) == next_fit_ptr)) {
        next_fit_needs_update = 1;
    }
    if (!prev_alloc && (PREV_BLKP(bp) == next_fit_ptr)) {
         next_fit_needs_update = 1;
    }
    // 현재 블록(bp) 자체가 next_fit_ptr 일 수도 있음 (예: free 직후 coalesce 호출 시)
    // splice_free_block 에서 처리되므로 여기선 고려 X

    if (prev_alloc && next_alloc) { 
        /* Case 1 */
        // 변경 없음, 현재 블록만 리스트에 추가
    } 
    else if (prev_alloc && !next_alloc) { 
        /* Case 2 */
        splice_free_block(NEXT_BLKP(bp)); // 다음 블록 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else if (!prev_alloc && next_alloc) {
         /* Case 3 */
        splice_free_block(PREV_BLKP(bp)); // 이전 블록 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else { 
        /* Case 4 */
        splice_free_block(PREV_BLKP(bp)); // 이전 블록 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 블록 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    add_free_block(bp); // 최종 병합된 블록 추가

    // NEXT FIT REVISED: 병합으로 인해 포인터가 사라졌다면, 새로 병합된 블록을 가리키도록 설정
    if (next_fit_needs_update) {
        next_fit_ptr = bp;
    }

    return bp;
}

void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) { mm_free(ptr); return NULL; }

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t current_size = GET_SIZE(HDRP(oldptr));
    size_t required_size = ALIGN(size + DSIZE);

    // Optimization 1: Current block is large enough
    if (current_size >= required_size) {
        // Optionally split block here if (current_size - required_size) >= MIN_BLOCK_SIZE
        return oldptr;
    }

    // Optimization 2: Next block is free and combination is large enough
    void* next_bp = NEXT_BLKP(oldptr);
    int next_is_free = !GET_ALLOC(HDRP(next_bp));
    if (next_is_free) {
        size_t combined_size = current_size + GET_SIZE(HDRP(next_bp));
        if (combined_size >= required_size) {
            splice_free_block(next_bp); // next_bp 제거 시 next_fit_ptr 업데이트됨
            PUT(HDRP(oldptr), PACK(combined_size, 1));
            PUT(FTRP(oldptr), PACK(combined_size, 1));
            // Optionally split block here
            return oldptr;
        }
    }

    // Default: Malloc new block, copy, free old
    newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize) copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr); // free 시 coalesce 호출 및 next_fit_ptr 관리됨
    return newptr;
}

/*
 * find_fit - Find a fit for a block with asize bytes (Next Fit - Revised)
 */
static void *find_fit(size_t asize)
{
    char *rover;
    char *start_search_ptr = next_fit_ptr; // NEXT FIT REVISED: 시작점 후보

    // NEXT FIT REVISED: 시작점 유효성 검사 및 설정
    // next_fit_ptr가 NULL이거나, 할당된 블록을 가리키면 리스트 처음부터 시작
    if (start_search_ptr == NULL || GET_ALLOC(HDRP(start_search_ptr))) {
        start_search_ptr = free_listp;
    }

    // 리스트가 비어있거나 유효한 시작점이 없으면 반환
    if (start_search_ptr == NULL) {
        return NULL;
    }

    // 1단계: start_search_ptr 부터 리스트 끝까지 탐색
    for (rover = start_search_ptr; rover != NULL; rover = GET_SUCC(rover)) {
        if (GET_SIZE(HDRP(rover)) >= asize) {
            // 찾았으면 반환 (next_fit_ptr는 place에서 업데이트)
            return rover;
        }
    }

    // 2단계: 리스트 처음부터 start_search_ptr 이전까지 탐색 (순환)
    for (rover = free_listp; rover != start_search_ptr; rover = GET_SUCC(rover)) {
        // rover가 NULL이 되는 경우는 리스트가 비었거나 start_search_ptr가 잘못된 경우인데,
        // 이미 위에서 처리되었으므로 이론상 발생하지 않음. 안전을 위해 체크.
         if (rover == NULL) {
             break;
         }
         if (GET_SIZE(HDRP(rover)) >= asize) {
            // 찾았으면 반환
            return rover;
        }
    }

    return NULL; /* No fit found */
}


static void *rand_fit(size_t asize)
{
    char *rover;
    int free_block_count = 0;

    // 1단계: 가용 블록 개수 세기
    for (rover = free_listp; rover != NULL; rover = GET_SUCC(rover)) {
        if (GET_SIZE(HDRP(rover)) >= asize) {
            free_block_count++;
        }
    }

    // 할당 가능한 블록이 없으면 NULL 반환
    if (free_block_count == 0) {
        return NULL;
    }

    // 2단계: 0부터 free_block_count-1 사이 랜덤 인덱스 뽑기
    int random_index = rand() % free_block_count;

    // 3단계: 해당 인덱스 위치의 블록 찾아서 반환
    int current_index = 0;
    for (rover = free_listp; rover != NULL; rover = GET_SUCC(rover)) {
        if (GET_SIZE(HDRP(rover)) >= asize) {
            if (current_index == random_index) {
                return rover;
            }
            current_index++;
        }
    }
    return NULL;
}


static void *probability_rand_fit(size_t asize)
{
    char *rover;
    char *best_fit = NULL;

    for (rover = free_listp; rover != NULL; rover = GET_SUCC(rover)) {
        size_t bsize = GET_SIZE(HDRP(rover));

        if (bsize >= asize) {
            int diff = bsize - asize;
            int prob;

            if (diff == 0) prob = 10;
            else if (diff <= 32) prob = 7;
            else if (diff <= 64) prob = 4;
            else prob = 1;

            if ((rand() % 10) < prob) {
                return rover;
            }


            best_fit = rover;
        }
    }

    return best_fit;
}

static void *best_fit(size_t asize)
{
    char *rover;
    size_t csize = (size_t)-1;
    char *best = NULL;
    // 1단계: 가용 블록 개수 세기
    for (rover = free_listp; rover != NULL; rover = GET_SUCC(rover)) {
        size_t size = GET_SIZE(HDRP(rover));
        if (size >= asize) {
            if(csize>size){
                csize = size;
                best = rover;
            }
            
        }
        else if  (GET_SIZE(HDRP(rover)) == asize){
            return rover;
        }
    }

    return best;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    // NEXT FIT REVISED: bp를 splice 하기 전의 다음 가용 블록 포인터를 저장
    void* next_free_in_list = GET_SUCC(bp);

    splice_free_block(bp); // 블록 제거 (여기서 next_fit_ptr가 bp였다면 업데이트됨)

    if ((csize - asize) >= MIN_BLOCK_SIZE) { // Split
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *remainder_bp = NEXT_BLKP(bp);
        PUT(HDRP(remainder_bp), PACK(csize - asize, 0));
        PUT(FTRP(remainder_bp), PACK(csize - asize, 0));
        add_free_block(remainder_bp); // 남은 블록 추가

        // NEXT FIT REVISED: 다음 탐색은 분할되고 남은 새 가용 블록부터 시작
        next_fit_ptr = remainder_bp;

    } 
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        next_fit_ptr = next_free_in_list;
    }
}

/* --- Explicit Free List Helper Functions --- */

static void add_free_block(void *bp)
{
    // LIFO (Stack): 리스트 맨 앞에 추가
    SET_SUCC(bp, free_listp);
    SET_PRED(bp, NULL); // 새 블럭의 이전은 없음
    if (free_listp != NULL) {
        SET_PRED(free_listp, bp); // 기존 첫 블럭의 이전을 새 블럭으로
    }
    free_listp = bp; // 리스트 시작점을 새 블럭으로 업데이트

    // NEXT FIT 관점: add는 next_fit_ptr를 직접 바꾸지 않음.
    // coalesce에서 추가 후 필요시 next_fit_ptr를 bp로 설정함.
}

static void splice_free_block(void *bp)
{
    void *pred = GET_PRED(bp);
    void *succ = GET_SUCC(bp);

    // NEXT FIT REVISED: 제거하려는 블록이 next_fit_ptr인지 확인
    // 만약 그렇다면, next_fit_ptr를 다음 가용 블록으로 이동시켜 dangling 포인터 방지
    // 링크를 바꾸기 전에 수행해야 함!
    if (next_fit_ptr == bp) {
        next_fit_ptr = succ;
    }

    // 링크 재연결
    if (pred == NULL) { // bp가 리스트의 첫 블록일 때
        free_listp = succ; // 다음 블록이 첫 블록이 됨
        if (succ != NULL) {
           SET_PRED(succ, NULL); // 새 첫 블록의 이전은 없음
        }
    } else { // bp가 중간 또는 마지막 블록일 때
        SET_SUCC(pred, succ); // 이전 블록의 다음을 bp의 다음으로 연결
        if (succ != NULL) {
            SET_PRED(succ, pred); // 다음 블록의 이전을 bp의 이전으로 연결
        }
    }
    // bp의 PRED/SUCC 포인터는 이제 가비지 값이 되어도 상관 없음 (할당되거나 병합됨)
}