// Marcin Linkiewicz, nr indeksu: 323853; Jestem jedynym autorem poniższego kodu
// źródłowego

/*
Opis działania kodu:

Poniższy kod działa na podstawie Segregated Free Lists (Segregated Fits).
Oznacza to, że Wszystkie wolne bloki zostają umieszczone w Liście wolnych bloków
o odpowiedniej klasie. Klasa wyliczana jest na podstawie rozmiaru wolnego bloku.
W moim kodzie Lista wolnych bloków podzielona jest na 10 różnych klas. Niech
Size określa rozmiar wolnego bloku, wtedy do listy wolnych bloków o klasie 0
trafiają bloki, których Size <= 128, do listy o klasie 1 trafiają bloki, których
Size <= 256 itd...

Miejsce na Segregated Lists jest alokowane przy wywołaniu procedury init.
Znajdują się one przed wskaźnikiem na heap_start, czyli przed obszarem dostępnym
dla użytkownika.

Oczywiście miejsce jest alokowane jedynie dla wskaźników na początek danych klas
Segregated Lists. Następne wskaźniki z danej klasy przechowywane są w samych
wolnych blokach w skompresowanej postaci (do 4B). Wygląda to następująco:

|   4B   |     4B    |    4B     |    xB     | (opcjonalnie) |   4B   |
|------------------------------------------------------------|--------|
| header | prev_free | next_free | leftovers |   alignment   | footer |
|------------------------------------------------------------|--------|

Do kompresji wskaźników, umieszczania ich w wolnych blokach oraz następnie
wydobywania ich w celu przeszukiwania listy wolnych bloków używam następujących
makr zdefiniowanych poniżej: GET_PREV_FREE, GET_NEXT_FREE, PUT_PREV_FREE,
PUT_NEXT_FREE, WORD_TO_POINTER

Ogólna struktura bloków w poniższej implementacji jest następująca:

- Blok zajęty:
|   4B   |              xB              | (opcjonalnie) |
|-------------------------------------------------------|
| header |           payload            |   alignment   |
|-------------------------------------------------------|

- Blok wolny:
|   4B   |              xB              | (opcjonalnie) |   4B   |
|-------------------------------------------------------|--------|
| header |           payload            |   alignment   | footer |
|-------------------------------------------------------|--------|

Każdy blok jest wyrównany do 16B (dlatego opcjonalnie jest w nich allignment).
Bloki zajęte posiadają tylko header. Footer posiadają jedynie bloki wolne. W
headerach bloków zajętych znajdują się informacje o rozmiarze bloku (razem z
headerem + alignmentem), o stanie zajętości (USED) oraz o stanie zajętości bloku
poprzedniego (PREVFREE). Analogicznie wygląda to w headerach i footerach bloków
wolnych.

Wybrana przeze mnie poltyka szukania nowych bloków to First-Fit.

*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif
static int counter = 0; // counter do checkheap

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

/* Moje definicje */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

#define WSIZE 4
#define DSIZE 8
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PACK(size, alloc) ((size) | (alloc))

// Powyższe makra zostały zapożyczone z CSAPP

#define GET_PREV_FREE(p) *(p + 1)
#define GET_NEXT_FREE(p) *(p + 2)
#define PUT_PREV_FREE(p, prev)                                                 \
  (*(word_t *)(p + 1) = (word_t)((unsigned long)prev))
#define PUT_NEXT_FREE(p, next)                                                 \
  (*(word_t *)(p + 2) = (word_t)((unsigned long)next))
#define WORD_TO_POINTER(word) (word_t *)((unsigned long)word | 0x800000000)
#define NR_OF_SEG_LISTS 10

static word_t **segregated_list;

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
// static word_t *last;       /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + (bt_size(bt) - WSIZE);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make_free(word_t *bt, size_t size, bt_flags flags) {
  PUT(bt, PACK(size, flags));            // header
  PUT(bt_footer(bt), PACK(size, flags)); // footer
}

static inline void bt_make_alloc(word_t *bt, size_t size, bt_flags flags) {
  PUT(bt, PACK(size, flags));
}

/* Previous block free flag handling for optimized boundary tags. */
static inline int bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  word_t *next = (void *)bt + bt_size(bt);
  return next <= heap_end ? next : NULL;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  word_t *prev = (void *)bt - bt_size(bt - 1);
  return prev >= heap_start ? prev : NULL;
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Oblicza klasę bloku o danym rozmiarze size */
static inline size_t calc_class(size_t size) {
  size_t class = 0;

  for (size_t class_size = 128; class < NR_OF_SEG_LISTS;
       class ++, class_size <<= 1)
    if (class_size >= size)
      break;
  return class < NR_OF_SEG_LISTS ? class : NR_OF_SEG_LISTS - 1;
}

/* Dodawanie bloku do listy wolnych bloków o odpowiedniej klasie. */
static void add_to_seg_list(word_t *ptr, size_t class) {
  if (segregated_list[class]) {
    PUT_NEXT_FREE(ptr, segregated_list[class]);
    PUT_PREV_FREE(ptr, NULL);
    PUT_PREV_FREE(segregated_list[class], ptr);
    segregated_list[class] = ptr;
  } else {
    PUT_NEXT_FREE(ptr, NULL);
    PUT_PREV_FREE(ptr, NULL);
    segregated_list[class] = ptr;
  }
}

/* Usuwanie bloku o danej klasie z listy wolnych bloków */
static void del_from_seg_list(word_t *ptr, size_t class) {
  word_t *class_head = segregated_list[class];

  if (!GET_NEXT_FREE(ptr) && !GET_PREV_FREE(ptr))
    segregated_list[class] = NULL;
  else {
    if (ptr == class_head) {
      PUT_PREV_FREE(WORD_TO_POINTER(GET_NEXT_FREE(class_head)), NULL);
      segregated_list[class] = WORD_TO_POINTER(GET_NEXT_FREE(ptr));
    } else if (!GET_NEXT_FREE(ptr))
      PUT_NEXT_FREE(WORD_TO_POINTER(GET_PREV_FREE(ptr)), NULL);
    else {
      PUT_NEXT_FREE(WORD_TO_POINTER(GET_PREV_FREE(ptr)), GET_NEXT_FREE(ptr));
      PUT_PREV_FREE(WORD_TO_POINTER(GET_NEXT_FREE(ptr)), GET_PREV_FREE(ptr));
    }
  }
}

static void *coalesce(void *ptr) {
  size_t next_free = 0, prev_free = 0;

  word_t *next = bt_next(ptr);
  if (next)
    next_free = bt_free(next);

  word_t *prev;
  if (((word_t *)ptr > heap_start) && bt_get_prevfree(ptr))
    prev = bt_prev(ptr);
  else
    prev = NULL;

  if (prev)
    prev_free = 1;

  size_t size = bt_size(ptr);
  if (prev_free && next_free) {
    size += bt_size(prev) + bt_size(next);
    del_from_seg_list(prev, calc_class(bt_size(prev)));
    del_from_seg_list(next, calc_class(bt_size(next)));
    bt_make_free(prev, size, FREE);
    ptr = prev;
    next = bt_next(prev);
    add_to_seg_list(ptr, calc_class(size));
  } else if (!prev_free && next_free) {
    size += bt_size(next);
    del_from_seg_list(next, calc_class(bt_size(next)));
    bt_make_free(ptr, size, FREE);
    next = bt_next(ptr);
    add_to_seg_list(ptr, calc_class(size));
  } else if (prev_free && !next_free) {
    size += bt_size(prev);
    del_from_seg_list(prev, calc_class(bt_size(prev)));
    bt_make_free(prev, size, FREE);
    ptr = prev;
    add_to_seg_list(ptr, calc_class(size));
  } else {
    add_to_seg_list(ptr, calc_class(size));
  }

  bt_set_prevfree(next);

  return ptr;
}

/* Funkcja rozszerzająca heap. Po każdym wywołaniu na koniec jest dodawany
 * epilog, który oznacza koniec heap'a. */
static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);

  if (ptr == (void *)-1)
    return NULL;

  ptr = heap_end;

  bt_make_free(ptr, size, FREE);
  PUT(bt_footer(ptr) + 1, PACK(0, PREVFREE | USED)); // new epilogue

  // last = heap_end;
  heap_end = bt_footer(ptr) + 1;

  return ptr;
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  segregated_list = mem_sbrk(NR_OF_SEG_LISTS * DSIZE);

  for (int i = 0; i < NR_OF_SEG_LISTS; i++)
    segregated_list[i] = NULL;

  if ((heap_start = mem_sbrk(4 * DSIZE)) == (void *)-1)
    return -1;

  bt_make_alloc(heap_start + 3, ALIGNMENT, USED); // prologue
  PUT(heap_start + 7, PACK(0, USED));             // epilogue
  heap_start += 7;
  heap_end = heap_start;

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  size_t class = calc_class(reqsz);
  word_t *ptr;

  while (class < NR_OF_SEG_LISTS) {
    ptr = segregated_list[class ++];
    if (!ptr)
      continue;

    while (ptr != (word_t *)0x800000000) {
      if (reqsz <= bt_size(ptr))
        return ptr;

      ptr = WORD_TO_POINTER(GET_NEXT_FREE(ptr));
    }
  }
  return NULL; // No fit
}
#else
/* Best fit startegy. */
#endif

/* Funkcja tworząca nowy zajęty blok o rozmiarze asize w miejscu ptr */
static void place(word_t *ptr, size_t asize) {
  size_t csize = bt_size(ptr);

  del_from_seg_list(ptr, calc_class(bt_size(ptr)));
  if ((csize - asize) >= 2 * ALIGNMENT) {
    bt_make_alloc(ptr, asize, USED);
    bt_make_free(bt_next(ptr), csize - asize, FREE);
    add_to_seg_list(bt_next(ptr), calc_class(csize - asize));
  } else
    bt_make_alloc(ptr, csize, USED);

  bt_clr_prevfree(bt_next(ptr));
}

/* Szukamy miejsca na size w liście wolnych bloków. Jeżeli go nie znajdziemy,
 * musimy zwiększyć stertę. Jako optymalizację, jeżeli sterta jest już spora,
 * oraz alokowany rozmiar jest "mały" (<= 256B), alokujemy od razu kilkanaście
 * bloków tego rozmiaru, aby nie robić w przyszłości nadmiarowych wywołań
 * malloc'a. */
void *malloc(size_t size) {
  if (size == 0)
    return NULL;

  size_t asize; // Adjusted block size
  asize = round_up(size + WSIZE);

  word_t *ptr = find_fit(asize);

  if (!ptr) {
    if ((ptr = morecore(asize)) == NULL)
      return NULL;
    ptr = coalesce(ptr);
    if (asize <= 256) {
      if ((unsigned long)ptr > 0x800001000) {
        word_t *tmp;
        size_t class = calc_class(asize);
        for (int i = 0; i < 15; i++) {
          tmp = morecore(asize);
          bt_set_prevfree(tmp);
          add_to_seg_list(tmp, class);
        }
      }
    }
  }
  place(ptr, asize);

  return bt_payload(ptr);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  word_t *block_ptr = bt_fromptr(ptr);

  if (block_ptr < heap_start || block_ptr > heap_end)
    return;

  bt_make_free(block_ptr, bt_size(block_ptr),
               FREE | bt_get_prevfree(block_ptr));
  coalesce(block_ptr);
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  /* Przypadki podstawowe */
  if (!old_ptr)
    return malloc(size);

  if (!size) {
    free(old_ptr);
    return NULL;
  }

  size_t asize = round_up(size + WSIZE); // Adjusted size
  word_t *block_ptr = bt_fromptr(old_ptr);

  /* Przypadek, w którym rozmiar podany w realloc jest mniejszy lub równy od
   * aktualnego rozmiaru bloku */
  int csize = bt_size(block_ptr) - asize;
  if (csize >= 2 * ALIGNMENT) {
    bt_make_alloc(block_ptr, asize, USED);
    word_t *next = bt_next(block_ptr);
    bt_make_free(next, csize, FREE);
    coalesce(next);
    return old_ptr;
  } else if (csize >= 0)
    return old_ptr;

  /* Przypadek, w którym reallocowany blok jest ostatnim.
   * Możemy wtedy po prostu rozszerzyć stertę o nadmiar. */
  word_t *next;
  if (bt_next(block_ptr) < heap_end)
    next = bt_next(block_ptr);
  else {
    bt_flags prev_free = bt_get_prevfree(block_ptr);
    morecore(asize - bt_size(block_ptr));
    bt_make_alloc(block_ptr, asize, USED | prev_free);
    bt_clr_prevfree(bt_next(block_ptr));
    return old_ptr;
  }

  word_t *prev = (block_ptr > heap_start && bt_get_prevfree(block_ptr))
                   ? bt_prev(block_ptr)
                   : NULL;

  size_t prev_size = prev ? bt_size(prev) : 0;
  size_t curr_size = bt_size(block_ptr);
  size_t next_size = bt_size(next);

  size_t new_size = curr_size;

  /* Sprawdzenie czy bloki poprzedni i/lub następny od reallocowanego bloku są
   * wolne oraz jeżeli są, to sprawdzenie, czy dodatkowe wolne miejsce z tych
   * bloków jest wystarczające. Następnie dodawanie i usuwanie bloków z list
   * wolnych bloków. */
  if (prev && bt_free(prev))
    new_size += prev_size;
  if (bt_free(next))
    new_size += next_size;
  if (new_size >= asize) {
    if (bt_free(next))
      del_from_seg_list(next, calc_class(next_size));
    if (prev) {
      if (bt_free(prev)) {
        del_from_seg_list(prev, calc_class(prev_size));
        block_ptr = prev;
      }
      memcpy(bt_payload(block_ptr), old_ptr, curr_size - WSIZE);
    }

    if (new_size - asize < 2 * ALIGNMENT) {
      bt_make_alloc(block_ptr, new_size, USED);
      bt_clr_prevfree(bt_next(block_ptr));
    } else {
      bt_make_alloc(block_ptr, asize, USED);
      bt_make_free(bt_next(block_ptr), new_size - asize, FREE);
      coalesce(bt_next(block_ptr));
    }
    return bt_payload(block_ptr);
  }

  /* Przypadek ostatni, czyli żaden z poprzednich nie zachodzi, więc musimy
   * zrobić malloca. */
  word_t *new_ptr;
  if ((new_ptr = malloc(size)) == NULL)
    return NULL;
  memcpy(new_ptr, old_ptr, bt_size(block_ptr) - WSIZE);
  free(old_ptr);
  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
  void *bt;
  printf("Check Heap \n");
  /* Printowanie bloków w heapie */
  for (bt = heap_start; bt && bt_size(bt) > 0; bt = bt_next(bt)) {
    if (counter > -1) { // dodatkowy if, który pomagał mi w debugowaniu
      printf(
        "\n\nBlock Address: %p Block Header Size: %d Block Header type: %X "
        "Block ends at: %p Block Footer Size: %d Block Footer Type: %X\n",
        bt, bt_size(bt), bt_used(bt) | bt_get_prevfree(bt), bt_next(bt),
        bt_size(bt_footer(bt)), bt_used(bt_footer(bt)));
    }
  }
  // counter++;
  printf("Heap start: %p Heap end: %p \n", heap_start, heap_end);
  printf("Check Heap End\n\n");

  printf("Seglists check: \n");

  /* Printowanie segregated lists */
  for (int i = 0; i < NR_OF_SEG_LISTS; i++) {
    if (!segregated_list[i])
      printf("%d: NULL\n", i);
    else {
      word_t *ptr = segregated_list[i];
      printf("%d: ", i);
      while (1) {
        printf("%p -> ", ptr);
        ptr = WORD_TO_POINTER(GET_NEXT_FREE(ptr));
        if (ptr == (word_t *)0x800000000) {
          printf("NULL\n");
          break;
        }
      }
    }
  }
}
