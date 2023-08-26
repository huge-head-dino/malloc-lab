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
    "week06-03",
    /* First member's full name */
    "JOONHO",
    /* First member's email address */
    "sjunho98@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

//***********************************************
#define ALIGNMENT 8  // 여기서는 double word로 할당 (byte)
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // /* rounds up to the nearest multiple of ALIGNMENT */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// ***********************************************

// *️⃣기본 상수 & 매크로******
#define WSIZE 8                             //싱글워드 = 헤더 = 풋터의 사이즈 (byte)
#define DSIZE 16                            //더블워드 사이즈 (byte)
#define CHUNKSIZE (1<<12)                   // 초기 가용 블록과 힙 확장을 위한 기본 크기
#define MAX(x , y) ( (x) > (y)? (x) : (y))  // MAX(x,y)는 삼항 연산자로 MAX 함수를 구현한 것

// *️⃣ 가용리스트 접근 or 순회 할 때 사용하는 매크로
#define PACK(size,alloc) ((size)|(alloc))            // size와 할당비트를 결합, header와 footer에 저장할 값 
#define GET(p) (*(unsigned int*)(p))                 // p가 참조하는 워드를 반환 
#define PUT(p,val) (*(unsigned int *)(p)=(int)(val)) // p에 val을 저장한다. 블록의 주소를 담는다. 위치를 담아서 이 주소를 읽고 헤더나 푸터에서 이동 혹은 연결하도록 한다.
#define GET_SIZE(p) (GET(p) & ~0x7)                  // 사이즈 반환. 8의 배수로 만들어주기  (&랑 ~를 이용해서 끝에 3bit 비우기)
#define GET_ALLOC(p) (GET(p) & 0x1)                  // 0,1로 현재 블록의 가용여부 판단 
#define HDRP(bp) ((char *)(bp) - WSIZE)              // bp(현재 블록의 포인터)로 현재 블록의 헤더위치와 풋터위치 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))    // 다음 블록의 포인터 (=bp) 위치 반환(bp + 현재 블록의 크기)
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))    // 이전 블록의 포인터 (=bp) 위치 반환(bp - 이전 블록의 크기)

// *️⃣ 변수 선언 
static char *heap_listp; // 프롤로그 사이를 가리키는 놈이다. (클래스의 시작)
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);



/* 
 * 1️⃣초기 힙 생성 함수 mm_init
 */
int mm_init(void)
{
    //초기 가용블록을 만든다.
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)   // 8워드 크기의 힙을 생성한다. heap_list에 힙의 시작 주소값을 할당한다(가용블록만 추적)
        return -1;                             // 불러올 수 없으면 -1을 반환한다.
    PUT(heap_listp, 0);                        // 정렬 패딩
    PUT(heap_listp + (1*WSIZE),PACK(DSIZE,1)); // 프롤로그 헤더 8바이트, 할당됐다는 1
    PUT(heap_listp + (2*WSIZE),PACK(DSIZE,1)); // 프롤로그 풋터 8바이트, 할당됐다는 1
    PUT(heap_listp + (3*WSIZE),PACK(0,1));     // 에필로그 헤더 : 프로그램이 할당한 마지막 블록의 뒤에 위치
    heap_listp += (2*WSIZE); // 처음에는 항상 프롤로그 사이를 가리킨다.
    // 나중에 find_fit을 할 때 사용됨
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    } // word가 몇개인지 확인하고 넣는다.
    return 0;      
}

// extend_heap이 사용되는 경우
// 1. 힙이 초기화 될 때
// 2. mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때

static void *extend_heap(size_t words)
{
    char * bp;
    size_t size;
    /* allocate an even number of words to maintain alignment*/
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // words가 
    if ((long)(bp = mem_sbrk(size))== -1) 
        return NULL;
    
    /* Initialize free block header footer and the epilogue header */
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    /* Coalesce if the previous block was free*/
    return coalesce(bp);
}


static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case1: 앞, 뒤 블록 모두 할당되어 있을 때
    if (prev_alloc && next_alloc) {
        return bp;
    }

    // case2: 앞 블록 할당, 뒷 블록 가용
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case3: 앞 블록 가용, 뒷 블록 할당
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // case4: 앞, 뒤 블록 모두 가용
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);    
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       //할당할 블록 사이즈
    size_t extendsize;  //확장할 사이즈 
    char *bp;

    // size가 0이거나 0보다 작으면 할당하지 않는다(잘못된 요청을 거르는 곳)
    if(size <= 0) // == 대신 <=  책은 ==
        return NULL;

    // 사이즈 조정
    if(size <= DSIZE)       // size가 8byte보다 작다면,
        asize = 2*DSIZE;    // 최소블록조건인 16byte로 맞춤
    else                    // size가 8byte보다 크다면
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1)) / DSIZE); // 8의 배수로 맞춰주는 과정 (올림하는 과정) 

    /**️⃣ 사이즈 조정은 다른 방법으로도 풀 수 있음*/
    // 요청받은 size에 8(헤더와 푸터 크기)를 더한 값을 2의 n승이 되도록 올림

    /*  while (asize < size + DSIZE) 
    {
        asize <<= 1;
    }*/


    // 적절한 가용(free)블록을 가용리스트에서 검색
    if((bp = find_fit(asize))!=NULL){
        place(bp,asize); // 할당
        return bp;       // 새로 할당된 블록의 포인터를 리턴해준다
    }

    //적당한 블록이 없을 경우에는 sbrk 명령으로 힙확장
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp,asize);
    return bp;
}

static void *find_fit(size_t a_size) {
    void *bp;

    for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (a_size <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;    // NO fit
}

// static void *find_fit(size_t a_size) {
//     char *bp = heap_listp;
//     bp = NEXT_BLKP(bp);
//     while (GET_SIZE(HDRP(bp)) < a_size || GET_ALLOC(HDRP(bp)) == 1) {   // bp가 적용될 블록의 크기보다 작고, free일 때
//         bp = NEXT_BLKP(bp);
//         if (GET_SIZE(HDRP(bp)) == 0) {      // Epilogue를 만났을 때
//             return NULL;
//         }
//     }
//     return bp;
// }

static void place(void *bp, size_t a_size) {
    size_t c_size = GET_SIZE(HDRP(bp));

    if ((c_size - a_size) >= (2 * (DSIZE))) {
        // 요청 용량 만큼 블록 배치
        PUT(HDRP(bp), PACK(a_size, 1));
        PUT(FTRP(bp), PACK(a_size, 1));
        
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header, footer 배치
        PUT(HDRP(bp), PACK(c_size - a_size, 0));
        PUT(FTRP(bp), PACK(c_size - a_size, 0));
    }
    else {      // csize와 aszie 차이가 네 칸(16byte)보다 작다면 해당 블록 통째로 사용
        PUT(HDRP(bp), PACK(c_size, 1));
        PUT(FTRP(bp), PACK(c_size, 1));
    }
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
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}











